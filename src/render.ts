// render.ts — pure rendering layer from Lean IR to Twelf LF text.
//
// This module is the "moral Twelf" rendering boundary: every function here
// produces Twelf source text from Lean IR, with no proof construction.
// Auditing the encoding means reading this file alone.
//
// State: a single module-level Map of level-param bindings is exported and
// mutated by generate-twelf.ts when it enters/leaves a polymorphic
// declaration's scope. It's consulted by lfLevel (for `param` levels) and by
// freshVar (to avoid colliding with binder names). Keeping it module-local
// here avoids threading it through every call site.

import type { Expr, Level, Name } from "./shared.ts";
import { nameToString } from "./shared.ts";

// =====================================================================
// Level-param scope (mutated by generate-twelf.ts around polymorphic decls)
// =====================================================================

export const levelParamBindings: Map<string, string> = new Map();

// Parallel to `levelParamBindings`: maps a universe parameter's name to its
// de Bruijn index for the current declaration.  The (untrusted) prover needs
// the raw index — not just the rendered `(lvar i)` string — to build the
// `lvl-subst` / `mleq/var-elim` proofs for universe-variable elimination.
export const levelParamIndices: Map<string, number> = new Map();

// =====================================================================
// Nat literal accumulator
// =====================================================================
//
// Every (natLit n) we render becomes `(enatlit n nonneg_n)`, where
// `nonneg_n` is a Twelf proof of `n >= 0` discharged via `%solve`.
// %solve declarations must appear at the top level (not inside an
// expression), so lfExpr accumulates the integers it has seen into
// this set; generate-twelf.ts iterates it once at the end and
// prepends a `%solve nonneg_N : N >= 0.` line per unique N.
//
// Stored as strings (not bigint) because the Lean IR carries arbitrary-
// precision nat literals as strings already (`Expr.lit (Literal.natVal n)`
// — see shared.ts), and Twelf accepts the same text as an integer literal.

// Distinct non-negative integers that need a `%solve nonneg_<n> : <n> >= 0.`
// witness in the generated prelude.  Populated both by nat literals (during
// rendering) and by `mleq` leaves (during level-equality proving, see
// `recordNonneg`); deduped here so the generator emits one witness per value.
export const natLiteralsSeen: Set<string> = new Set();

// Register a non-negative integer offset that needs an `n >= 0` witness (used
// by `mleq/lz` / `mleq/self` leaves in level-equality proofs).  Returns the
// witness name the proof term should reference.  The caller guarantees n >= 0;
// the witness is emitted from the same `natLiteralsSeen` set as nat literals.
export function recordNonneg(n: number): string {
  natLiteralsSeen.add(String(n));
  return `nonneg_${n}`;
}

// ---------------------------------------------------------------------------
// Posited string-disequality facts
// ---------------------------------------------------------------------------
//
// `no-self-ref` proofs (strict positivity, see synth.ts) discharge each
// `econst N` leaf with a `string-neq N N0` witness asserting the constant's
// name differs from the inductive's.  LF cannot derive string disequality, so
// the environment *posits* these facts as constants on the open `string-neq`
// family.  Each distinct (a, b) pair requested here becomes one declaration
//
//   sneq/<i> : string-neq "a" "b".
//
// emitted into the generated prelude; the no-self-ref proof refers to it by
// the returned `sneq/<i>` name.  Soundness does not depend on these claims
// being true: final-checks.elf's `%query 0 * string-neq X X` aborts the whole
// load if any posited pair is reflexive (a = b).  So an untrusted prover may
// request whatever it likes — a lie only ever sinks the development.
const stringNeqIndex: Map<string, number> = new Map();
export const stringNeqFacts: { a: string; b: string }[] = [];

export function recordStringNeq(a: string, b: string): string {
  const key = JSON.stringify([a, b]);
  let i = stringNeqIndex.get(key);
  if (i === undefined) {
    i = stringNeqFacts.length;
    stringNeqIndex.set(key, i);
    stringNeqFacts.push({ a, b });
  }
  return `sneq/${i}`;
}

export function clearStringNeqFacts(): void {
  stringNeqIndex.clear();
  stringNeqFacts.length = 0;
}

// =====================================================================
// Name mangling
// =====================================================================

export function mangle(n: Name): string {
  // Replace dots and disallowed chars for use as Twelf identifiers.
  return nameToString(n).replace(/[^A-Za-z0-9_]/g, "_");
}

// =====================================================================
// LF emission for levels and expressions
// =====================================================================

export function lfLevel(l: Level): string {
  switch (l.kind) {
    case "zero":
      return "lzero";
    case "succ":
      return `(lsucc ${lfLevel(l.arg)})`;
    case "max":
      return `(lmax ${lfLevel(l.l)} ${lfLevel(l.r)})`;
    case "imax":
      return `(limax ${lfLevel(l.l)} ${lfLevel(l.r)})`;
    case "param": {
      const v = levelParamBindings.get(nameToString(l.name));
      if (v === undefined) throw new Error(`unbound level param: ${nameToString(l.name)}`);
      return v;
    }
  }
}

export function lfLvls(ls: Level[]): string {
  return ls.reduceRight((acc, l) => `(lcons ${lfLevel(l)} ${acc})`, "lnil");
}

// A self-reference substitution for building a HOAS abstraction: when
// rendering hits a `const` whose rendered form equals `selfStr`, emit the
// bound variable `varName` instead.  Used by the trusted generator to compute
// the `T_HOAS` argument of `ctor-positive/intro` itself (rather than trusting
// an untrusted prover to supply it).  Rendering of a `const` is injective on
// (name, levels), so string comparison reliably identifies the self-reference.
export type SelfSubst = { selfStr: string; varName: string };

// HOAS translation: bvar 0 inside a binder becomes the LF-level variable
// introduced at that binder.  `boundVars` is the LF-side variable name
// stack, innermost-first.  When `self` is supplied, occurrences of the
// self-reference constant are abstracted to `self.varName` (see SelfSubst).
export function lfExpr(e: Expr, boundVars: string[], self?: SelfSubst): string {
  switch (e.kind) {
    case "bvar": {
      const name = boundVars[e.deBruijn];
      if (name === undefined)
        throw new Error(`bvar ${e.deBruijn} out of scope (depth ${boundVars.length})`);
      return name;
    }
    case "sort":
      return `(esort ${lfLevel(e.level)})`;
    case "const": {
      const s = `(econst "${nameToString(e.name)}" ${lfLvls(e.us)})`;
      return self && s === self.selfStr ? self.varName : s;
    }
    case "app":
      return `(eapp ${lfExpr(e.fn, boundVars, self)} ${lfExpr(e.arg, boundVars, self)})`;
    case "lam": {
      const v = freshVar(boundVars);
      return `(elam ${lfExpr(e.type, boundVars, self)} ([${v}] ${lfExpr(e.body, [v, ...boundVars], self)}))`;
    }
    case "forallE": {
      const v = freshVar(boundVars);
      return `(eforall ${lfExpr(e.type, boundVars, self)} ([${v}] ${lfExpr(e.body, [v, ...boundVars], self)}))`;
    }
    case "letE":
      // Unreachable: parse.ts desugars letE to (λx:T. body) value before
      // any IR reaches the translator. See desugarLetE in src/parse.ts.
      throw new Error("letE should have been desugared by parse.ts");
    case "proj":
      return `(eproj "${nameToString(e.typeName)}" ${e.idx} ${lfExpr(e.struct, boundVars, self)})`;
    case "natLit": {
      natLiteralsSeen.add(e.value);
      return `(enatlit ${e.value} nonneg_${e.value})`;
    }
    case "strLit":
      return `(estrlit ${JSON.stringify(e.value)})`;
  }
}

// =====================================================================
// Fresh variable names
// =====================================================================

export function freshVar(scope: string[]): string {
  // Predictable names: x, y, z, w, x1, y1, ...  Scope must include
  // *every* bound name (vars and hyps both) — they live in the same
  // LF namespace and would shadow.  Level params are no longer LF
  // variables (they render as `(lvar i)` data), so they can't collide.
  const letters = ["x", "y", "z", "w"];
  for (let suf = 0; suf < 1000; suf++) {
    for (const l of letters) {
      const v = suf === 0 ? l : `${l}${suf}`;
      if (!scope.includes(v)) return v;
    }
  }
  throw new Error("ran out of fresh variable names");
}
