// render.ts — pure rendering layer from Lean IR to Twelf LF text.
//
// This module is the "moral Twelf" rendering boundary: every function here
// produces Twelf source text from Lean IR, with no proof construction.
// Auditing the encoding means reading this file alone.
//
// State: a single module-level Map of level-param bindings is exported and
// mutated by lean2lf.ts when it enters/leaves a polymorphic declaration's
// scope. It's consulted by lfLevel (for `param` levels) and by freshVar
// (to avoid colliding with binder names). Keeping it module-local here
// avoids threading it through every call site.

import type { Expr, Level, Name } from "./shared.ts";
import { nameToString } from "./shared.ts";

// =====================================================================
// Level-param scope (mutated by lean2lf.ts around polymorphic decls)
// =====================================================================

export const levelParamBindings: Map<string, string> = new Map();

// =====================================================================
// Nat literal accumulator
// =====================================================================
//
// Every (natLit n) we render becomes `(enatlit n nonneg_n)`, where
// `nonneg_n` is a Twelf proof of `n >= 0` discharged via `%solve`.
// %solve declarations must appear at the top level (not inside an
// expression), so lfExpr accumulates the integers it has seen into
// this set; main() in lean2lf.ts iterates it once at the end and
// prepends a `%solve nonneg_N : N >= 0.` line per unique N.
//
// Stored as strings (not bigint) because the Lean IR carries arbitrary-
// precision nat literals as strings already (`Expr.lit (Literal.natVal n)`
// — see shared.ts), and Twelf accepts the same text as an integer literal.

export const natLiteralsSeen: Set<string> = new Set();

// =====================================================================
// Name mangling
// =====================================================================

export function mangle(n: Name): string {
  // Replace dots and disallowed chars for use as Twelf identifiers.
  return nameToString(n).replace(/[^A-Za-z0-9_]/g, "_");
}

// Sanitize a Lean level-param name into an LF identifier that won't
// collide with freshVar's letters (x/y/z/w).
//
// NOTE: dead w.r.t. the de Bruijn level scheme used by generate-twelf.ts
// (level params now render as `(lvar i)` data, not LF variables).  Retained
// only because the superseded lean2lf.ts / render-cli.ts still import it; it
// will go when those are deleted in the end-state cleanup.
export function nameToLfLevelVar(n: Name): string {
  const raw = nameToString(n).replace(/[^A-Za-z0-9_]/g, "_");
  if (raw === "") return "lv_anon";
  if (/^[xyzw]/.test(raw)) return `lv_${raw}`;
  return raw;
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

// HOAS translation: bvar 0 inside a binder becomes the LF-level variable
// introduced at that binder.  `boundVars` is the LF-side variable name
// stack, innermost-first.
export function lfExpr(e: Expr, boundVars: string[]): string {
  switch (e.kind) {
    case "bvar": {
      const name = boundVars[e.deBruijn];
      if (name === undefined)
        throw new Error(`bvar ${e.deBruijn} out of scope (depth ${boundVars.length})`);
      return name;
    }
    case "sort":
      return `(esort ${lfLevel(e.level)})`;
    case "const":
      return `(econst "${nameToString(e.name)}" ${lfLvls(e.us)})`;
    case "app":
      return `(eapp ${lfExpr(e.fn, boundVars)} ${lfExpr(e.arg, boundVars)})`;
    case "lam": {
      const v = freshVar(boundVars);
      return `(elam ${lfExpr(e.type, boundVars)} ([${v}] ${lfExpr(e.body, [v, ...boundVars])}))`;
    }
    case "forallE": {
      const v = freshVar(boundVars);
      return `(eforall ${lfExpr(e.type, boundVars)} ([${v}] ${lfExpr(e.body, [v, ...boundVars])}))`;
    }
    case "letE":
      // Unreachable: parse.ts desugars letE to (λx:T. body) value before
      // any IR reaches the translator. See desugarLetE in src/parse.ts.
      throw new Error("letE should have been desugared by parse.ts");
    case "proj":
      return `(eproj "${nameToString(e.typeName)}" ${e.idx} ${lfExpr(e.struct, boundVars)})`;
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
