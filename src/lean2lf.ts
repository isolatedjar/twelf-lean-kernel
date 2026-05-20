#!/usr/bin/env -S node --experimental-strip-types
// lean2lf.ts — read a ParsedEnv JSON on stdin (from parse.ts), emit Twelf LF on stdout.
//
// Precondition: stdin is the JSON produced by parse.ts.  We don't
// re-validate the shape — the type ascription via `as ParsedEnv`
// trusts that contract.  If you want runtime validation, replace the
// JSON.parse call below with a Zod parse over the shared types.
//
// Discipline: if the translator can't construct a proof, it emits a
// Twelf comment recording the skip rather than an axiom.  This is
// what the harness reports as 🤷.  Translator-side rejections that
// previously used `tcb-violation` are gone — see translator notes on
// each %% SKIP path for the principled (Twelf-side) replacement.

import {
  freshVar,
  levelParamBindings,
  lfExpr,
  lfLevel,
  lfLvls,
  mangle,
  nameToLfLevelVar,
  natLiteralsSeen,
} from "./render.ts";
import type { Decl, Expr, Inductive, Level, Name, ParsedEnv } from "./shared.ts";
import { nameToString, transformNamesFromJSON } from "./shared.ts";

// Build a Twelf proof of `ends-in-sort <lfExpr t>` if `t` is structurally
// a (possibly empty) chain of forall-binders ending in a sort literal.
// Used by the inductive type-former path to satisfy the tightened
// `dkind-ok/indt` rule.  Returns null if t doesn't structurally qualify
// (e.g. a const reference, an app, a bvar) — the caller treats this as
// a translator-side rejection.
//
// We don't recurse through `t.body` with substitution; the proof
// just structurally walks `forall A B → forall A' B' → ... → sort`.
// Twelf checks each inner proof under the binder introduced by the
// corresponding ends-in-sort/forall, so the bound variable doesn't
// need to flow into our textual proof at all.
function endsInSortProof(t: Expr, lfScope: string[]): string | null {
  if (t.kind === "sort") return "ends-in-sort/sort";
  if (t.kind === "forallE") {
    const v = freshVar(lfScope);
    const inner = endsInSortProof(t.body, [...lfScope, v]);
    if (inner === null) return null;
    return `(ends-in-sort/forall ([${v}] ${inner}))`;
  }
  return null;
}

// Constructors for ctor-positive witnesses.  Soundness gate on
// inductive definitions: every ctor of inductive Foo must have a
// type that is strictly positive in Foo (Lean's standard restriction
// that prevents the (Foo → Empty) → Foo paradox).
//
// `selfName` and `selfLevels` identify the inductive Foo whose
// ctors we're checking.  Each builder returns the Twelf-term string
// of the witness, or null if the ctor's type doesn't satisfy the
// non-nested strict-positivity condition (in which case the
// translator emits a rejection).
//
// `scope` tracks LF-bound expression variables introduced by walking
// under forall/lambda binders.  Each entry carries the LF name `y`
// of the expression variable AND the LF name `hy` of its `absent S y`
// hypothesis.  De-Bruijn lookup uses this scope; the innermost binder
// is at the END.

// Positivity scope: LF binder names (innermost-first) introduced by
// strict-pos/forall and ctor-spine/arg as we descend into Π-bodies.
// Same convention as lfExpr's boundVars — they're combined below.
type PosScope = string[];

function isSelfRef(t: Expr, selfName: string, selfLevels: Level[]): boolean {
  if (t.kind !== "const") return false;
  if (nameToString(t.name) !== selfName) return false;
  if (t.us.length !== selfLevels.length) return false;
  return t.us.every((u, i) => {
    const sl = selfLevels[i];
    return sl !== undefined && levelEq(u, sl);
  });
}

// Does t syntactically mention the inductive's self-reference?
// Used to decide between strict-pos/no-occur (E : expr — must be
// closed wrt S in LF) and the recursive cases.
function exprMentions(t: Expr, selfName: string, selfLevels: Level[]): boolean {
  if (isSelfRef(t, selfName, selfLevels)) return true;
  switch (t.kind) {
    case "sort":
    case "const":
    case "bvar":
    case "natLit":
    case "strLit":
      return false;
    case "app":
      return exprMentions(t.fn, selfName, selfLevels) || exprMentions(t.arg, selfName, selfLevels);
    case "forallE":
    case "lam":
      return (
        exprMentions(t.type, selfName, selfLevels) || exprMentions(t.body, selfName, selfLevels)
      );
    case "letE":
      return (
        exprMentions(t.type, selfName, selfLevels) ||
        exprMentions(t.value, selfName, selfLevels) ||
        exprMentions(t.body, selfName, selfLevels)
      );
    case "proj":
      return exprMentions(t.struct, selfName, selfLevels);
  }
}

// Build a witness of `applies-self ([S] T_with_S)` — i.e., t's head,
// after substituting S for the self-reference, is the bound S.
// applies-self/refl when t IS the self-reference; otherwise walks
// applications.  Argument terms aren't checked — the rule allows
// them to be arbitrary (typed expr -> expr).
function buildAppliesSelf(t: Expr, selfName: string, selfLevels: Level[]): string | null {
  if (isSelfRef(t, selfName, selfLevels)) return "applies-self/refl";
  if (t.kind === "app") {
    const inner = buildAppliesSelf(t.fn, selfName, selfLevels);
    if (inner === null) return null;
    return `(applies-self/app ${inner})`;
  }
  return null;
}

// Build a witness of `strict-pos ([S] T_with_S)`.  Tries head, then
// no-occur (LF parameter discipline), then the Π case.
function buildStrictPos(
  t: Expr,
  selfName: string,
  selfLevels: Level[],
  scope: PosScope,
): string | null {
  // Head case: S applied to args.
  const head = buildAppliesSelf(t, selfName, selfLevels);
  if (head !== null) return `(strict-pos/head ${head})`;
  // No-occur: t doesn't mention S anywhere.  The /no-occur rule has
  // signature `{E : expr} strict-pos ([S] E)` — E being typed `expr`
  // (not `expr -> expr`) is precisely what enforces absence of S in
  // E.  We render t as a closed LF expression (lfExpr ignores S).
  if (!exprMentions(t, selfName, selfLevels)) {
    return `(strict-pos/no-occur ${lfExpr(t, scope)})`;
  }
  // Π case: domain must NOT mention S (so the rule's `{A : expr}`
  // can take it as a closed expression), codomain recursively strict-
  // positive under a fresh LF param for the bound variable.
  if (t.kind === "forallE") {
    if (exprMentions(t.type, selfName, selfLevels)) return null;
    const A_lf = lfExpr(t.type, scope);
    const y = `_y${scope.length}`;
    const innerSP = buildStrictPos(t.body, selfName, selfLevels, [y, ...scope]);
    if (innerSP === null) return null;
    return `(strict-pos/forall ${A_lf} ([${y}] ${innerSP}))`;
  }
  return null;
}

// Build a witness of `ctor-spine ([S] T_with_S)`.  Π-bodies descend
// via ctor-spine/arg; the leaf (result type) must be S-applied.
function buildCtorSpine(
  t: Expr,
  selfName: string,
  selfLevels: Level[],
  scope: PosScope,
): string | null {
  if (t.kind === "forallE") {
    // Note: unlike strict-pos/forall, ctor-spine/arg takes A : expr -> expr
    // (the argument type may mention S, gated by the strict-pos premise).
    const argSP = buildStrictPos(t.type, selfName, selfLevels, scope);
    if (argSP === null) return null;
    const y = `_y${scope.length}`;
    const bodyCS = buildCtorSpine(t.body, selfName, selfLevels, [y, ...scope]);
    if (bodyCS === null) return null;
    return `(ctor-spine/arg ${argSP} ([${y}] ${bodyCS}))`;
  }
  // Result: must be S-applied.
  const result = buildAppliesSelf(t, selfName, selfLevels);
  if (result === null) return null;
  return `(ctor-spine/result ${result})`;
}

// Render an Expr to LF using `S` as the literal for occurrences of
// the inductive's self-reference (econst selfName selfLevels).  This
// is the body of the explicit T_HOAS argument to ctor-positive/intro.
function lfExprHoasSelf(
  t: Expr,
  selfName: string,
  selfLevels: Level[],
  boundVars: string[],
  selfLfName: string,
): string {
  if (isSelfRef(t, selfName, selfLevels)) return selfLfName;
  switch (t.kind) {
    case "bvar": {
      const name = boundVars[t.deBruijn];
      if (name === undefined) throw new Error(`bvar ${t.deBruijn} out of scope`);
      return name;
    }
    case "sort":
      return `(esort ${lfLevel(t.level)})`;
    case "const":
      return `(econst "${nameToString(t.name)}" ${lfLvls(t.us)})`;
    case "app":
      return `(eapp ${lfExprHoasSelf(t.fn, selfName, selfLevels, boundVars, selfLfName)} ${lfExprHoasSelf(t.arg, selfName, selfLevels, boundVars, selfLfName)})`;
    case "forallE":
    case "lam": {
      const v = freshVar(boundVars);
      const inner = lfExprHoasSelf(t.body, selfName, selfLevels, [v, ...boundVars], selfLfName);
      const head = t.kind === "forallE" ? "eforall" : "elam";
      return `(${head} ${lfExprHoasSelf(t.type, selfName, selfLevels, boundVars, selfLfName)} ([${v}] ${inner}))`;
    }
    case "letE":
    case "proj":
    case "natLit":
    case "strLit":
      throw new Error(`lfExprHoasSelf: ${t.kind} not supported`);
  }
}

// Do ALL of `names` appear as words in at least one of `bodies`?  Used
// to detect whether every polymorphic level binder has a strict
// occurrence in a proof body.  Twelf rejects `c : {u} T = body` when
// `u` has no strict occurrence, so we fall back to %abbrev in that case.
function allMentioned(names: string[], ...bodies: string[]): boolean {
  for (const n of names) {
    const escaped = n.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    const re = new RegExp(`(?:^|[^A-Za-z0-9_])${escaped}(?:$|[^A-Za-z0-9_])`);
    if (!bodies.some((b) => re.test(b))) return false;
  }
  return true;
}

// Translator-side rejection: emit `%% SKIP:` and decline to emit the
// problematic declaration.  Twelf doesn't see the broken content, and
// the harness marks the file as INCOMPLETE (🤷) on the SKIP marker.
//
// Note: this is NOT a Twelf-side rejection.  When the translator emits
// SKIP it's giving up — Twelf isn't checking the soundness condition
// for the declined declaration.  Per-test outcomes that hinge on a
// SKIP marker are intentionally tracked as INCOMPLETE, not as PASS,
// even when the underlying NDJSON was supposed to be rejected: a SKIP
// shows we couldn't pose the question to Twelf, not that Twelf
// verified it as bad.  The principled fix for each SKIP path is to
// encode the missing check inside the LF signature so Twelf rejects
// the witness directly.
// For duplicate-name handling: instead of declining to emit the second
// declaration, we give it a unique LF mangle and let Twelf's `%unique
// declared +N +LS -1T -1DK *W` directive detect the overlap (two
// `declared "foo" lnil ...` clauses with different outputs) when the
// signature is loaded.  This is a genuine Twelf-verified rejection
// rather than a translator-side decline.  Counter is per-base-mangle.
const dupCounter: Map<string, number> = new Map();

// Given a base LF mangle and the Lean name it derives from, return either
// the base mangle (if first occurrence) or `<base>__dup<n>` (subsequent).
// Side-effects: increments dupCounter on duplicates.  Does NOT mutate
// declTable — downstream refs resolve to the first occurrence.
function freshMangleForDuplicates(baseMangle: string, leanName: string): string {
  if (!declTable.has(leanName)) return baseMangle;
  const n = (dupCounter.get(baseMangle) || 0) + 1;
  dupCounter.set(baseMangle, n);
  return `${baseMangle}__dup${n}`;
}

// Substitute level params throughout a Level expression.  Used to
// produce a closed level term from a polymorphic one for %solve.
function substLevel(l: Level, sub: Map<string, Level>): Level {
  switch (l.kind) {
    case "zero":
      return l;
    case "succ":
      return { kind: "succ", arg: substLevel(l.arg, sub) };
    case "max":
      return { kind: "max", l: substLevel(l.l, sub), r: substLevel(l.r, sub) };
    case "imax":
      return { kind: "imax", l: substLevel(l.l, sub), r: substLevel(l.r, sub) };
    case "param": {
      const replacement = sub.get(nameToString(l.name));
      return replacement === undefined ? l : replacement;
    }
  }
}

// Substitute level params throughout an Expr.  Bvars / fvars / lam /
// forall / app / letE are recursed structurally; only `sort` and
// `const` carry levels.
function substExprLevels(e: Expr, sub: Map<string, Level>): Expr {
  switch (e.kind) {
    case "bvar":
      return e;
    case "sort":
      return { kind: "sort", level: substLevel(e.level, sub) };
    case "const":
      return { kind: "const", name: e.name, us: e.us.map((u) => substLevel(u, sub)) };
    case "app":
      return { kind: "app", fn: substExprLevels(e.fn, sub), arg: substExprLevels(e.arg, sub) };
    case "lam":
      return {
        kind: "lam",
        name: e.name,
        type: substExprLevels(e.type, sub),
        body: substExprLevels(e.body, sub),
      };
    case "forallE":
      return {
        kind: "forallE",
        name: e.name,
        type: substExprLevels(e.type, sub),
        body: substExprLevels(e.body, sub),
      };
    case "letE":
      return {
        kind: "letE",
        name: e.name,
        type: substExprLevels(e.type, sub),
        value: substExprLevels(e.value, sub),
        body: substExprLevels(e.body, sub),
      };
    case "proj":
      return {
        kind: "proj",
        typeName: e.typeName,
        idx: e.idx,
        struct: substExprLevels(e.struct, sub),
      };
    case "natLit":
    case "strLit":
      return e;
  }
}

// Build a substitution that sends each level param to a distinct
// concrete level (lzero, lsucc lzero, lsucc lsucc lzero, ...).  Used
// for the polymorphic ctor-positive %solve path, where the goal must
// be closed and we want syntactic-distinctness so head-mismatches
// (e.g., swapped-level-arg ctors) aren't masked by the substitution.
function distinctLevelSub(params: Name[]): Map<string, Level> {
  const sub = new Map<string, Level>();
  for (const [i, p] of params.entries()) {
    let l: Level = { kind: "zero" };
    for (let j = 0; j < i; j++) l = { kind: "succ", arg: l };
    sub.set(nameToString(p), l);
  }
  return sub;
}

// =====================================================================
// 7. Type synthesis + proof construction
// =====================================================================

// --- Expr utilities --------------------------------------------------

// Shift bvars in `e` at or above `cutoff` by `by`.
function shift(e: Expr, by: number, cutoff: number = 0): Expr {
  switch (e.kind) {
    case "bvar":
      return e.deBruijn >= cutoff ? { kind: "bvar", deBruijn: e.deBruijn + by } : e;
    case "sort":
    case "const":
    case "natLit":
    case "strLit":
      return e;
    case "lam":
      return { ...e, type: shift(e.type, by, cutoff), body: shift(e.body, by, cutoff + 1) };
    case "forallE":
      return { ...e, type: shift(e.type, by, cutoff), body: shift(e.body, by, cutoff + 1) };
    case "app":
      return { kind: "app", fn: shift(e.fn, by, cutoff), arg: shift(e.arg, by, cutoff) };
    case "letE":
      return {
        ...e,
        type: shift(e.type, by, cutoff),
        value: shift(e.value, by, cutoff),
        body: shift(e.body, by, cutoff + 1),
      };
    case "proj":
      return { ...e, struct: shift(e.struct, by, cutoff) };
  }
}

// Substitute `r` for bvar at `depth` in `e`.  Bvars > depth get decremented;
// `r`'s free bvars are shifted into the surrounding scope appropriately.
function subst(e: Expr, r: Expr, depth: number = 0): Expr {
  switch (e.kind) {
    case "bvar":
      if (e.deBruijn === depth) return shift(r, depth);
      if (e.deBruijn > depth) return { kind: "bvar", deBruijn: e.deBruijn - 1 };
      return e;
    case "sort":
    case "const":
    case "natLit":
    case "strLit":
      return e;
    case "lam":
      return { ...e, type: subst(e.type, r, depth), body: subst(e.body, r, depth + 1) };
    case "forallE":
      return { ...e, type: subst(e.type, r, depth), body: subst(e.body, r, depth + 1) };
    case "app":
      return { kind: "app", fn: subst(e.fn, r, depth), arg: subst(e.arg, r, depth) };
    case "letE":
      return {
        ...e,
        type: subst(e.type, r, depth),
        value: subst(e.value, r, depth),
        body: subst(e.body, r, depth + 1),
      };
    case "proj":
      return { ...e, struct: subst(e.struct, r, depth) };
  }
}

// Structural equality of Exprs.  De Bruijn means this is α-equivalence.
// Binder display-names are not part of the structural identity.
function exprEq(a: Expr, b: Expr): boolean {
  switch (a.kind) {
    case "bvar":
      return b.kind === "bvar" && a.deBruijn === b.deBruijn;
    case "sort":
      return b.kind === "sort" && levelEq(a.level, b.level);
    case "const":
      return (
        b.kind === "const" &&
        nameEq(a.name, b.name) &&
        a.us.length === b.us.length &&
        a.us.every((u, i) => {
          const bU = b.us[i];
          return bU !== undefined && levelEq(u, bU);
        })
      );
    case "app":
      return b.kind === "app" && exprEq(a.fn, b.fn) && exprEq(a.arg, b.arg);
    case "lam":
      return b.kind === "lam" && exprEq(a.type, b.type) && exprEq(a.body, b.body);
    case "forallE":
      return b.kind === "forallE" && exprEq(a.type, b.type) && exprEq(a.body, b.body);
    case "letE":
      return (
        b.kind === "letE" &&
        exprEq(a.type, b.type) &&
        exprEq(a.value, b.value) &&
        exprEq(a.body, b.body)
      );
    case "proj":
      return (
        b.kind === "proj" &&
        nameEq(a.typeName, b.typeName) &&
        a.idx === b.idx &&
        exprEq(a.struct, b.struct)
      );
    case "natLit":
      return b.kind === "natLit" && a.value === b.value;
    case "strLit":
      return b.kind === "strLit" && a.value === b.value;
  }
}

// --- Level substitution (for universe-polymorphic instantiation) ----

function substLevelsInLevel(l: Level, m: Map<string, Level>): Level {
  switch (l.kind) {
    case "zero":
      return l;
    case "succ":
      return { kind: "succ", arg: substLevelsInLevel(l.arg, m) };
    case "max":
      return { kind: "max", l: substLevelsInLevel(l.l, m), r: substLevelsInLevel(l.r, m) };
    case "imax":
      return { kind: "imax", l: substLevelsInLevel(l.l, m), r: substLevelsInLevel(l.r, m) };
    case "param": {
      const sub = m.get(nameToString(l.name));
      return sub !== undefined ? sub : l;
    }
  }
}

function substLevels(e: Expr, m: Map<string, Level>): Expr {
  if (m.size === 0) return e;
  switch (e.kind) {
    case "bvar":
    case "natLit":
    case "strLit":
      return e;
    case "sort":
      return { kind: "sort", level: substLevelsInLevel(e.level, m) };
    case "const":
      return { kind: "const", name: e.name, us: e.us.map((u) => substLevelsInLevel(u, m)) };
    case "app":
      return { kind: "app", fn: substLevels(e.fn, m), arg: substLevels(e.arg, m) };
    case "lam":
    case "forallE":
      return { ...e, type: substLevels(e.type, m), body: substLevels(e.body, m) };
    case "letE":
      return {
        ...e,
        type: substLevels(e.type, m),
        value: substLevels(e.value, m),
        body: substLevels(e.body, m),
      };
    case "proj":
      return { ...e, struct: substLevels(e.struct, m) };
  }
}

// --- Decl table (populated as we walk NDJSON) ------------------------

interface DeclEntry {
  mangle: string;
  levelParams: Name[]; // empty for monomorphic decls
  type: Expr;
  // defn/thm/opq/ax are value-level decls; indt/ctor/irec/quot are
  // kernel-derived structural decls (no value, but distinguishable
  // from `ax` for dependency-graph honesty and ι-rule attachment).
  kind: "defn" | "thm" | "opq" | "ax" | "indt" | "ctor" | "irec" | "quot";
  value?: Expr;
}
const declTable: Map<string, DeclEntry> = new Map();

// Stage-1 enum iota lookup: maps a ctor's name (e.g. "Bool.false") to the
// metadata `reduceOnce` needs to invoke the corresponding `<ctor>/iota`
// helper.  Populated by emitStage1EnumIotaHelpers.
interface IotaInfo {
  recName: string; // e.g. "Bool.rec"
  indName: Name; // the inductive's Name (for constructing expected motive types)
  indNameStr: string; // e.g. "Bool"
  ctorMangle: string; // e.g. "Bool_false"
  position: number; // 0-indexed cidx
  allCtors: { name: string; nameStruct: Name }[]; // in cidx order
}
const iotaTable: Map<string, IotaInfo> = new Map();

// --- Level-equality solver (unchanged) -------------------------------

function levelEq(a: Level, b: Level): boolean {
  switch (a.kind) {
    case "zero":
      return b.kind === "zero";
    case "succ":
      return b.kind === "succ" && levelEq(a.arg, b.arg);
    case "max":
      return b.kind === "max" && levelEq(a.l, b.l) && levelEq(a.r, b.r);
    case "imax":
      return b.kind === "imax" && levelEq(a.l, b.l) && levelEq(a.r, b.r);
    case "param":
      return b.kind === "param" && nameEq(a.name, b.name);
  }
}
function nameEq(a: Name, b: Name): boolean {
  switch (a.kind) {
    case "anon":
      return b.kind === "anon";
    case "str":
      return b.kind === "str" && a.str === b.str && nameEq(a.pre, b.pre);
    case "num":
      return b.kind === "num" && a.i === b.i && nameEq(a.pre, b.pre);
  }
}

// One-step top-level reduction.  Each rule corresponds to an lvl-eq
// constructor in tcb.elf.  Returns null when no reduction applies.
function reduceLevel(l: Level): { result: Level; proof: string } | null {
  if (l.kind === "imax" && l.r.kind === "zero") {
    return { result: { kind: "zero" }, proof: "lvl-eq/imax-zero" };
  }
  if (l.kind === "imax" && l.r.kind === "succ") {
    return { result: { kind: "max", l: l.l, r: l.r }, proof: "lvl-eq/imax-succ" };
  }
  if (l.kind === "imax" && levelEq(l.l, l.r)) {
    return { result: l.l, proof: "lvl-eq/imax-idem" };
  }
  if (l.kind === "max" && levelEq(l.l, l.r)) {
    return { result: l.l, proof: "lvl-eq/max-idem" };
  }
  if (l.kind === "max" && l.l.kind === "zero") {
    return { result: l.r, proof: "lvl-eq/max-zero-l" };
  }
  if (l.kind === "max" && l.r.kind === "zero") {
    return { result: l.l, proof: "lvl-eq/max-zero-r" };
  }
  if (l.kind === "max" && l.l.kind === "succ" && l.r.kind === "succ") {
    return {
      result: { kind: "succ", arg: { kind: "max", l: l.l.arg, r: l.r.arg } },
      proof: "lvl-eq/max-succ",
    };
  }
  return null;
}

// One-step reduction at any position (top-level or under a constructor).
// Wraps a sub-position reduction in the appropriate congruence rule.
// Returns null only if `l` is in normal form (no reductions anywhere).
function stepLevel(l: Level): { result: Level; proof: string } | null {
  const top = reduceLevel(l);
  if (top !== null) return top;
  switch (l.kind) {
    case "zero":
    case "param":
      return null;
    case "succ": {
      const inner = stepLevel(l.arg);
      if (inner === null) return null;
      return {
        result: { kind: "succ", arg: inner.result },
        proof: `(lvl-eq/lsucc-cong ${inner.proof})`,
      };
    }
    case "max": {
      const lstep = stepLevel(l.l);
      if (lstep !== null) {
        return {
          result: { kind: "max", l: lstep.result, r: l.r },
          proof: `(lvl-eq/lmax-cong ${lstep.proof} lvl-eq/refl)`,
        };
      }
      const rstep = stepLevel(l.r);
      if (rstep !== null) {
        return {
          result: { kind: "max", l: l.l, r: rstep.result },
          proof: `(lvl-eq/lmax-cong lvl-eq/refl ${rstep.proof})`,
        };
      }
      return null;
    }
    case "imax": {
      const lstep = stepLevel(l.l);
      if (lstep !== null) {
        return {
          result: { kind: "imax", l: lstep.result, r: l.r },
          proof: `(lvl-eq/limax-cong ${lstep.proof} lvl-eq/refl)`,
        };
      }
      const rstep = stepLevel(l.r);
      if (rstep !== null) {
        return {
          result: { kind: "imax", l: l.l, r: rstep.result },
          proof: `(lvl-eq/limax-cong lvl-eq/refl ${rstep.proof})`,
        };
      }
      return null;
    }
  }
}

// Try to find a proof of (lvl-eq from to).  Strategy:
//   1. If syntactically equal, lvl-eq/refl.
//   2. Try a step (top-level OR internal congruence-wrapped) in `from`.
//   3. Try a step in `to` (used with symm).
//   4. If `from` and `to` share an outer constructor, try congruence.
//
// `depth` guards against pathological recursion.
function solveLvlEq(from: Level, to: Level, depth: number = 0): string | null {
  if (depth > 12) return null;
  if (levelEq(from, to)) return "lvl-eq/refl";

  // (2) step `from`.
  const r = stepLevel(from);
  if (r !== null) {
    const rest = solveLvlEq(r.result, to, depth + 1);
    if (rest !== null) return `(lvl-eq/trans ${r.proof} ${rest})`;
  }
  // (3) step `to`.
  const r2 = stepLevel(to);
  if (r2 !== null) {
    const rest = solveLvlEq(from, r2.result, depth + 1);
    if (rest !== null) return `(lvl-eq/trans ${rest} (lvl-eq/symm ${r2.proof}))`;
  }
  // (4) congruence.
  if (from.kind === "succ" && to.kind === "succ") {
    const inner = solveLvlEq(from.arg, to.arg, depth + 1);
    if (inner !== null) return `(lvl-eq/lsucc-cong ${inner})`;
  }
  if (from.kind === "max" && to.kind === "max") {
    const lP = solveLvlEq(from.l, to.l, depth + 1);
    const rP = solveLvlEq(from.r, to.r, depth + 1);
    if (lP !== null && rP !== null) return `(lvl-eq/lmax-cong ${lP} ${rP})`;
  }
  if (from.kind === "imax" && to.kind === "imax") {
    const lP = solveLvlEq(from.l, to.l, depth + 1);
    const rP = solveLvlEq(from.r, to.r, depth + 1);
    if (lP !== null && rP !== null) return `(lvl-eq/limax-cong ${lP} ${rP})`;
  }

  return null;
}

// Parse the inferred-type string back to a Level for solver use.
// Cheap parser — matches our own output exactly.
function _parseLvlSyntax(raw: string): Level {
  const s = raw.trim();
  if (s === "lzero") return { kind: "zero" };
  // Strip outer parens.
  if (s.startsWith("(") && s.endsWith(")")) {
    const inner = s.slice(1, -1);
    const [head, arg1, arg2] = splitTopLevel(inner);
    if (head === "lsucc" && arg1 !== undefined) return { kind: "succ", arg: _parseLvlSyntax(arg1) };
    if (head === "lmax" && arg1 !== undefined && arg2 !== undefined)
      return { kind: "max", l: _parseLvlSyntax(arg1), r: _parseLvlSyntax(arg2) };
    if (head === "limax" && arg1 !== undefined && arg2 !== undefined)
      return { kind: "imax", l: _parseLvlSyntax(arg1), r: _parseLvlSyntax(arg2) };
  }
  throw new Error(`parseLvlSyntax: cannot parse ${s}`);
}
function splitTopLevel(s: string): string[] {
  const out: string[] = [];
  let depth = 0,
    start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if (c === "(") depth++;
    else if (c === ")") depth--;
    else if (c === " " && depth === 0) {
      out.push(s.slice(start, i));
      start = i + 1;
    }
  }
  out.push(s.slice(start));
  return out.filter((p) => p.length > 0);
}

// --- Type synthesis ---------------------------------------------------
//
// For each Expr e we produce (tyExpr, proof) where:
//   - tyExpr is the synthesized type, as a Lean Expr (NOT an LF string)
//   - proof is a Twelf term of type `defeq <lfExpr e> <lfExpr e> <lfExpr tyExpr>`
//
// Scope convention:
//   - vars[i], hyps[i], tys[i]: information about bvar i (innermost first).
//   - tys[i] is stored in its ORIGINAL form (as written at the time the
//     binder was introduced).  When looking up via bvar i, we shift by
//     (i+1) to bring it into the current scope.
//
// Supported: sort, forallE, lam, bvar, const (non-poly), app (no conv yet).

interface Scope {
  vars: string[];
  hyps: string[];
  tys: Expr[];
}
type Synth = { tyExpr: Expr; proof: string };

function synth(e: Expr, scope: Scope): Synth {
  switch (e.kind) {
    case "bvar": {
      const ty = scope.tys[e.deBruijn];
      const h = scope.hyps[e.deBruijn];
      if (ty === undefined || h === undefined) {
        throw new Error(`bvar ${e.deBruijn} out of scope`);
      }
      return { tyExpr: shift(ty, e.deBruijn + 1), proof: h };
    }
    case "sort":
      return {
        tyExpr: { kind: "sort", level: { kind: "succ", arg: e.level } },
        proof: `(defeq/sort-refl-at ${lfLevel(e.level)})`,
      };
    case "const": {
      const entry = declTable.get(nameToString(e.name));
      if (entry === undefined) {
        throw new Error(`const "${nameToString(e.name)}" not in decl table`);
      }
      if (e.us.length !== entry.levelParams.length) {
        throw new Error(
          `const "${nameToString(e.name)}": got ${e.us.length} level args, expected ${entry.levelParams.length}`,
        );
      }
      // Build the level-param → actual-level substitution and apply it
      // to the looked-up type.
      const m: Map<string, Level> = new Map();
      for (const [i, lp] of entry.levelParams.entries()) {
        const u = e.us[i];
        if (u !== undefined) m.set(nameToString(lp), u);
      }
      const tyExpr = substLevels(entry.type, m);
      // For poly decls, `<mangle>/decl` is itself an LF function that
      // takes the level args.  We apply it.
      const declInst =
        e.us.length === 0
          ? `${entry.mangle}/decl`
          : `(${entry.mangle}/decl ${e.us.map(lfLevel).join(" ")})`;
      return {
        tyExpr,
        proof: `(defeq/const ${declInst})`,
      };
    }
    case "forallE": {
      const aSynth = synth(e.type, scope);
      if (aSynth.tyExpr.kind !== "sort") {
        throw new Error(
          `forallE: binder type does not have a sort type (got ${aSynth.tyExpr.kind})`,
        );
      }
      const uA = aSynth.tyExpr.level;

      const allBound = [...scope.vars, ...scope.hyps];
      const v = freshVar(allBound);
      const h = freshVar([...allBound, v]);
      const innerScope: Scope = {
        vars: [v, ...scope.vars],
        hyps: [h, ...scope.hyps],
        tys: [e.type, ...scope.tys],
      };
      const bodySynth = synth(e.body, innerScope);
      if (bodySynth.tyExpr.kind !== "sort") {
        throw new Error(`forallE: body does not have a sort type (got ${bodySynth.tyExpr.kind})`);
      }
      const vB = bodySynth.tyExpr.level;

      return {
        tyExpr: { kind: "sort", level: { kind: "imax", l: uA, r: vB } },
        proof: `(defeq/forall ${aSynth.proof} ([${v}] [${h}] ${bodySynth.proof}))`,
      };
    }
    case "lam": {
      const aSynth = synth(e.type, scope);
      const allBound = [...scope.vars, ...scope.hyps];
      const v = freshVar(allBound);
      const h = freshVar([...allBound, v]);
      const innerScope: Scope = {
        vars: [v, ...scope.vars],
        hyps: [h, ...scope.hyps],
        tys: [e.type, ...scope.tys],
      };
      const bodySynth = synth(e.body, innerScope);
      // The lam's type is forallE A bodySynth.tyExpr.  bodySynth.tyExpr's
      // bvar 0 (if any) already correctly refers to this binder.
      return {
        tyExpr: { kind: "forallE", name: e.name, type: e.type, body: bodySynth.tyExpr },
        proof: `(defeq/lam ${aSynth.proof} ([${v}] [${h}] ${bodySynth.proof}))`,
      };
    }
    case "app": {
      const fSynth = synth(e.fn, scope);
      if (fSynth.tyExpr.kind !== "forallE") {
        throw new Error(`app: function does not have a forall type (got ${fSynth.tyExpr.kind})`);
      }
      const A_expected = fSynth.tyExpr.type;
      const B = fSynth.tyExpr.body;
      const aSynth = synth(e.arg, scope);

      // Argument-type check: try syntactic equality first, then full
      // bridgeTypes (which handles sort-level, forall congruence, and
      // whnf-based reduction).
      let aProof = aSynth.proof;
      if (!exprEq(aSynth.tyExpr, A_expected)) {
        const conv = bridgeTypes(aSynth.tyExpr, A_expected, scope);
        if (conv === null) {
          throw new Error(`app: cannot bridge arg type to function domain`);
        }
        aProof = `(defeq/conv ${conv} ${aSynth.proof})`;
      }

      return {
        tyExpr: subst(B, e.arg),
        proof: `(defeq/app ${fSynth.proof} ${aProof})`,
      };
    }
    default:
      throw new Error(`synth: case ${(e as { kind: string }).kind} not yet supported`);
  }
}

// --- One-step head reduction (with proof) ----------------------------
//
// tryIotaEnum: detect an iota redex for a stage-1 enum recursor.
//
// Pattern: e = (eapp ... (eapp (eapp (econst RecName [u]) Motive) Mp_1) ...) (econst CtorName lnil))
// where CtorName is registered in iotaTable as a stage-1 enum ctor.
//
// On match, produces a defeq proof using the <CtorMangle>/iota helper
// (which lifts defeq/extra (defeq/iota-enum-K-pos ...)) and returns the
// reduced expression (the appropriate minor premise).
function tryIotaEnum(e: Expr, scope: Scope): { result: Expr; proof: string } | null {
  if (e.kind !== "app") return null;
  // Walk the spine: collect args, find the head.
  const args: Expr[] = [];
  let head: Expr = e;
  while (head.kind === "app") {
    args.unshift(head.arg);
    head = head.fn;
  }
  // Head must be a const (the recursor).
  if (head.kind !== "const") return null;
  // The last arg (major premise) must be a const with no level args
  // and no further application: a 0-field ctor invocation.
  if (args.length === 0) return null;
  const major = args[args.length - 1];
  if (major === undefined || major.kind !== "const") return null;
  if (major.us.length !== 0) return null;
  // Look up iota info for this ctor.
  const ctorName = nameToString(major.name);
  const info = iotaTable.get(ctorName);
  if (!info) return null;
  // Sanity: rec name and arg count.
  if (nameToString(head.name) !== info.recName) return null;
  if (head.us.length !== 1) return null;
  const k = info.allCtors.length;
  if (args.length !== k + 2) return null; // motive + k cases + major
  const u = head.us[0];
  if (u === undefined) return null;

  const motive = args[0];
  if (motive === undefined) return null;
  const cases = args.slice(1, k + 1);

  // Build the expected motive type: eforall (econst indName lnil) ([_] esort u)
  const indConst: Expr = { kind: "const", name: info.indName, us: [] };
  const expectedMotiveTy: Expr = {
    kind: "forallE",
    name: { kind: "anon" },
    type: indConst,
    body: { kind: "sort", level: u },
  };
  // Synth motive; bridge its type to expectedMotiveTy if needed.
  let motiveS: Synth;
  try {
    motiveS = synth(motive, scope);
  } catch {
    return null;
  }
  let motiveProof = motiveS.proof;
  if (!exprEq(motiveS.tyExpr, expectedMotiveTy)) {
    const conv = bridgeTypes(motiveS.tyExpr, expectedMotiveTy, scope, 0);
    if (conv === null) return null;
    motiveProof = `(defeq/conv ${conv} ${motiveS.proof})`;
  }

  // For each case, build expected type (eapp motive (econst ctor_i lnil))
  // and bridge as needed.
  const caseProofs: string[] = [];
  for (const [i, caseExpr] of cases.entries()) {
    const ci = info.allCtors[i];
    if (ci === undefined) return null;
    const expectedCaseTy: Expr = {
      kind: "app",
      fn: motive,
      arg: { kind: "const", name: ci.nameStruct, us: [] },
    };
    let caseS: Synth;
    try {
      caseS = synth(caseExpr, scope);
    } catch {
      return null;
    }
    let cp = caseS.proof;
    if (!exprEq(caseS.tyExpr, expectedCaseTy)) {
      const conv = bridgeTypes(caseS.tyExpr, expectedCaseTy, scope, 0);
      if (conv === null) return null;
      cp = `(defeq/conv ${conv} ${caseS.proof})`;
    }
    caseProofs.push(cp);
  }

  // Assemble: (<ctorMangle>/iota u motiveProof caseProofs...)
  let helperCall = `(${info.ctorMangle}/iota ${lfLevel(u)} ${motiveProof} ${caseProofs.join(" ")})`;

  // The helper produces a proof at type `(eapp M (econst ctor lnil))`.  If M
  // is a lam, that's a β-redex; the outer context typically expects the
  // β-reduced form `(M.body[ctor])`.  Wrap with defeq/conv via β-reduction
  // of the type index so the proof's index matches what callers expect.
  if (motive.kind === "lam") {
    const posCtorInfo = info.allCtors[info.position];
    if (posCtorInfo === undefined) return null;
    const ctorExpr: Expr = { kind: "const", name: posCtorInfo.nameStruct, us: [] };
    const allBound = [...scope.vars, ...scope.hyps];
    const v = freshVar(allBound);
    const h = freshVar([...allBound, v]);
    const innerScope: Scope = {
      vars: [v, ...scope.vars],
      hyps: [h, ...scope.hyps],
      tys: [motive.type, ...scope.tys],
    };
    let bodyS: Synth, ctorS: Synth;
    try {
      bodyS = synth(motive.body, innerScope);
    } catch {
      return null;
    }
    try {
      ctorS = synth(ctorExpr, scope);
    } catch {
      return null;
    }
    const betaProof = `(defeq/beta ([${v}] [${h}] ${bodyS.proof}) ${ctorS.proof})`;
    helperCall = `(defeq/conv ${betaProof} ${helperCall})`;
  }

  const resultExpr = cases[info.position];
  if (resultExpr === undefined) return null;
  return {
    result: resultExpr,
    proof: helperCall,
  };
}

// reduceOnce(e, scope) attempts a single head-reduction step and returns
// (e', proof : defeq e e' T) where T is the expression's type.  Returns
// null if e is in whnf.  Sort-level rewrites (imax-zero, imax-succ,
// max-idem) are treated as reductions.
//
// IMPORTANT: the proof's `T` index is left implicit.  Twelf reconstructs
// it; if reconstruction fails because two chain steps disagree on T up
// to lvl-eq but not syntactically, we'd need additional congruence
// rules in tcb.elf (lvl-eq/lsucc-cong, etc.).

function reduceOnce(e: Expr, scope: Scope): { result: Expr; proof: string } | null {
  // Sort-level reductions via defeq/sort-eq.
  if (e.kind === "sort") {
    if (e.level.kind === "imax" && e.level.r.kind === "zero") {
      return {
        result: { kind: "sort", level: { kind: "zero" } },
        proof: "(defeq/sort-eq lvl-eq/imax-zero)",
      };
    }
    if (e.level.kind === "imax" && e.level.r.kind === "succ") {
      return {
        result: { kind: "sort", level: { kind: "max", l: e.level.l, r: e.level.r } },
        proof: "(defeq/sort-eq lvl-eq/imax-succ)",
      };
    }
    if (e.level.kind === "max" && levelEq(e.level.l, e.level.r)) {
      return {
        result: { kind: "sort", level: e.level.l },
        proof: "(defeq/sort-eq lvl-eq/max-idem)",
      };
    }
    return null;
  }

  // δ-unfold for defns.
  if (e.kind === "const") {
    const entry = declTable.get(nameToString(e.name));
    if (
      entry !== undefined &&
      entry.kind === "defn" &&
      entry.value !== undefined &&
      e.us.length === entry.levelParams.length
    ) {
      const m: Map<string, Level> = new Map();
      for (const [i, lp] of entry.levelParams.entries()) {
        const u = e.us[i];
        if (u !== undefined) m.set(nameToString(lp), u);
      }
      const declInst =
        e.us.length === 0
          ? `${entry.mangle}/decl`
          : `(${entry.mangle}/decl ${e.us.map(lfLevel).join(" ")})`;
      return {
        result: substLevels(entry.value, m),
        proof: `(defeq/delta ${declInst})`,
      };
    }
    return null;
  }

  // app: try iota first (stage-1 enum recursors), then β, then lift from f.
  if (e.kind === "app") {
    const iotaStep = tryIotaEnum(e, scope);
    if (iotaStep !== null) return iotaStep;

    if (e.fn.kind === "lam") {
      const A = e.fn.type;
      const Body = e.fn.body;
      const allBound = [...scope.vars, ...scope.hyps];
      const v = freshVar(allBound);
      const h = freshVar([...allBound, v]);
      const innerScope: Scope = {
        vars: [v, ...scope.vars],
        hyps: [h, ...scope.hyps],
        tys: [A, ...scope.tys],
      };
      let bodyS: Synth, argS: Synth;
      try {
        bodyS = synth(Body, innerScope);
      } catch {
        return null;
      }
      try {
        argS = synth(e.arg, scope);
      } catch {
        return null;
      }
      // Ensure arg has type A.
      let argProof = argS.proof;
      if (!exprEq(argS.tyExpr, A)) {
        const conv = bridgeTypes(argS.tyExpr, A, scope, 0);
        if (conv === null) return null;
        argProof = `(defeq/conv ${conv} ${argS.proof})`;
      }
      return {
        result: subst(Body, e.arg),
        proof: `(defeq/beta ([${v}] [${h}] ${bodyS.proof}) ${argProof})`,
      };
    }

    // f is not a lam — try to reduce f one step and lift via defeq/app.
    const fReduced = reduceOnce(e.fn, scope);
    if (fReduced !== null) {
      // Need defeq arg arg A.  Get A from synth(e.fn).
      let fS: Synth, argS: Synth;
      try {
        fS = synth(e.fn, scope);
      } catch {
        return null;
      }
      try {
        argS = synth(e.arg, scope);
      } catch {
        return null;
      }
      if (fS.tyExpr.kind !== "forallE") return null;
      const A_expected = fS.tyExpr.type;
      let argProof = argS.proof;
      if (!exprEq(argS.tyExpr, A_expected)) {
        const conv = bridgeTypes(argS.tyExpr, A_expected, scope, 0);
        if (conv === null) return null;
        argProof = `(defeq/conv ${conv} ${argS.proof})`;
      }
      return {
        result: { kind: "app", fn: fReduced.result, arg: e.arg },
        proof: `(defeq/app ${fReduced.proof} ${argProof})`,
      };
    }

    // Neither β nor fn-reduce fired — try arg-side reduction.  This
    // departs from strict head-reduction but is needed when an iota
    // redex (or any other redex) lives inside a syntactically-stable
    // application like `Eq A B (rec ... ctor)`.  Lifting an arg
    // reduction `arg ≡ arg'` via defeq/app with a refl proof for the
    // fn gives `defeq (eapp fn arg) (eapp fn arg') (B arg)`.
    const argReduced = reduceOnce(e.arg, scope);
    if (argReduced !== null) {
      let fS: Synth;
      try {
        fS = synth(e.fn, scope);
      } catch {
        return null;
      }
      if (fS.tyExpr.kind !== "forallE") return null;
      return {
        result: { kind: "app", fn: e.fn, arg: argReduced.result },
        proof: `(defeq/app ${fS.proof} ${argReduced.proof})`,
      };
    }
    return null;
  }

  return null;
}

// Repeatedly head-reduce until stuck.  Also records `typeOfType`: the
// type of the expression (as an Expr — should be a sort if `e` is a type
// expression).  This is needed because defeq/trans requires both args
// at syntactically the same type, and chain steps from different
// derivations (e.g. sort-eq vs δ+β) can have type indices that are
// equivalent but not syntactically equal.
function whnf(
  e: Expr,
  scope: Scope,
  maxSteps: number = 30,
): { result: Expr; chain: string | null; typeOfType: Expr | null } {
  let typeOfType: Expr | null = null;
  try {
    typeOfType = synth(e, scope).tyExpr;
  } catch {
    // synth may fail for unsupported expression forms; typeOfType stays null
  }

  let cur = e;
  let chain: string | null = null;
  for (let i = 0; i < maxSteps; i++) {
    const step = reduceOnce(cur, scope);
    if (step === null) break;
    cur = step.result;
    chain = chain === null ? step.proof : `(defeq/trans ${chain} ${step.proof})`;
  }
  return { result: cur, chain, typeOfType };
}

// Construct a proof of `defeq a b (esort _)`, using whnf as needed.
// Returns null if no bridge can be found.
//
// Subtlety: chain steps from different sources (e.g. sort-eq on `a`'s
// side vs δ+β on `b`'s side) live at different type indices.  We wrap
// each chain with defeq/conv to bring its type to a common target.
function bridgeTypes(a: Expr, b: Expr, scope: Scope, depth: number = 0): string | null {
  if (depth > 6) return null;

  if (exprEq(a, b)) {
    if (a.kind === "sort") return "defeq/sort-refl";
    try {
      const aS = synth(a, scope);
      if (aS.tyExpr.kind === "sort") return aS.proof;
    } catch {
      // synth may fail; fall through to return null
    }
    return null;
  }
  if (a.kind === "sort" && b.kind === "sort") {
    const le = solveLvlEq(a.level, b.level);
    if (le !== null) return `(defeq/sort-eq ${le})`;
  }

  // Both forall — try congruence via defeq/forall.  This is needed when
  // both types are quantifier types whose bodies disagree but are defeq.
  if (a.kind === "forallE" && b.kind === "forallE") {
    const aaBridge = bridgeTypes(a.type, b.type, scope, depth + 1);
    if (aaBridge !== null) {
      const allBound = [...scope.vars, ...scope.hyps];
      const v = freshVar(allBound);
      const h = freshVar([...allBound, v]);
      const innerScope: Scope = {
        vars: [v, ...scope.vars],
        hyps: [h, ...scope.hyps],
        tys: [a.type, ...scope.tys],
      };
      const bbBridge = bridgeTypes(a.body, b.body, innerScope, depth + 1);
      if (bbBridge !== null) {
        return `(defeq/forall ${aaBridge} ([${v}] [${h}] ${bbBridge}))`;
      }
    }
    // Fall through if forall-congruence didn't pan out.
  }

  const aW = whnf(a, scope);
  const bW = whnf(b, scope);

  if (aW.chain === null && bW.chain === null && !exprEq(a, b)) return null;

  // Connect aW.result to bW.result, producing `middleProof` and its `middleType`.
  let middleProof: string | null;
  let middleType: Expr | null;
  if (exprEq(aW.result, bW.result)) {
    middleProof = null;
    middleType = aW.typeOfType ?? bW.typeOfType;
  } else if (aW.result.kind === "sort" && bW.result.kind === "sort") {
    const le = solveLvlEq(aW.result.level, bW.result.level);
    if (le === null) return null;
    middleProof = `(defeq/sort-eq ${le})`;
    // sort-eq's type index is `(esort (lsucc L_from))`.
    middleType = { kind: "sort", level: { kind: "succ", arg: aW.result.level } };
  } else {
    if (aW.chain === null && bW.chain === null) return null;
    middleProof = bridgeTypes(aW.result, bW.result, scope, depth + 1);
    if (middleProof === null) return null;
    // Can't easily determine middleType for recursive bridge; assume bW's typeOfType.
    middleType = bW.typeOfType ?? aW.typeOfType;
  }

  // Pick a target type-of-type for the final chain.  Prefer bW's (it's
  // typically what's expected at the call site, since b is the declared
  // type in our main use).
  const targetT: Expr | null = bW.typeOfType ?? aW.typeOfType ?? middleType;

  // Helper: convert a proof from its native typeOfType to targetT (or
  // leave alone if they match / either is null).
  function coerce(proof: string, nativeT: Expr | null): string | null {
    if (targetT === null || nativeT === null) return proof;
    if (exprEq(nativeT, targetT)) return proof;
    const conv = bridgeTypes(nativeT, targetT, scope, depth + 1);
    if (conv === null) return null;
    return `(defeq/conv ${conv} ${proof})`;
  }

  // Assemble the chain.  Each segment's native type-of-type:
  //   aW.chain    : aW.typeOfType
  //   middleProof : middleType
  //   bW.chain    : bW.typeOfType  (we'll flip via defeq/symm)
  const segments: string[] = [];
  if (aW.chain !== null) {
    const seg = coerce(aW.chain, aW.typeOfType);
    if (seg === null) return null;
    segments.push(seg);
  }
  if (middleProof !== null) {
    const seg = coerce(middleProof, middleType);
    if (seg === null) return null;
    segments.push(seg);
  }
  if (bW.chain !== null) {
    const seg = coerce(bW.chain, bW.typeOfType);
    if (seg === null) return null;
    segments.push(`(defeq/symm ${seg})`);
  }

  if (segments.length === 0) {
    return a.kind === "sort" ? "defeq/sort-refl" : null;
  }
  const seed = segments[0] ?? "";
  if (segments.length === 1) return seed;
  return segments.slice(1).reduce((acc, p) => `(defeq/trans ${acc} ${p})`, seed);
}

// =====================================================================
// 8. Top-level emission
// =====================================================================

const out: string[] = [];
const skips: string[] = [];

// Hole tracking.  Each entry is a tag matching one of the constants in
// HOLE_AXIOM_DECLS below.  When the translator can't construct a proof
// of a particular judgment, it emits `%% HOLE/<tag>:` and uses
// `hole/<tag>` in place of a real proof; the harness counts these.
//
// Hole axioms are declared INLINE in each generated file (not in
// sources.cfg) so that Twelf's higher-order unification can't sneak
// them in to discharge unrelated `%solve` obligations across the
// global signature.
const holesUsed: Set<string> = new Set();

const HOLE_AXIOM_DECLS: Record<string, string> = {
  defeq: `hole/defeq : {E1 : expr} {E2 : expr} {T : expr} defeq E1 E2 T.`,
  "ends-in-sort": `hole/ends-in-sort : {T : expr} ends-in-sort T.`,
  "ctor-positive": `hole/ctor-positive : {N : name} {LS : lvls} {T : expr} ctor-positive N LS T.`,
  "lvl-eq": `hole/lvl-eq : {L1 : lvl} {L2 : lvl} lvl-eq L1 L2.`,
};

function recordHole(tag: string): void {
  if (!(tag in HOLE_AXIOM_DECLS)) {
    throw new Error(`unknown hole tag: ${tag}`);
  }
  holesUsed.add(tag);
}

function emit(s: string): void {
  out.push(s);
}
function emitBlank(): void {
  out.push("");
}

// Three of the four kinds (def, thm, opq) share the same structure: a
// type-WF proof, a value-typing proof, and a `declared` with the
// appropriate dkind wrapping the value.  The fourth (axiom) has no
// value.  Twelf's `dkind-ok/thm` rule enforces that the type is at
// `(esort lzero)` (a Prop); we don't need to check that ourselves.
type ValDeclKind = "def" | "thm" | "opaque";
const VAL_KIND_INFO: Record<
  ValDeclKind,
  { dkindCtor: string; okCtor: string; tableKind: DeclEntry["kind"] }
> = {
  def: { dkindCtor: "defn", okCtor: "dkind-ok/defn", tableKind: "defn" },
  thm: { dkindCtor: "thm", okCtor: "dkind-ok/thm", tableKind: "thm" },
  opaque: { dkindCtor: "opq", okCtor: "dkind-ok/opq", tableKind: "opq" },
};

function emitValDecl(d: Decl & { kind: ValDeclKind }): void {
  const info = VAL_KIND_INFO[d.kind];
  const kindTag = d.kind;
  const declName = nameToString(d.name);
  const mn = freshMangleForDuplicates(mangle(d.name), declName);
  // declTable.has(declName) → mn now ends in "__dup<n>"; both
  // declarations are emitted so Twelf's %unique on `declared` can
  // detect the overlap on first-argument string.

  // Set up level-param bindings so lfLevel can render `param` levels
  // and freshVar avoids collisions.  Tear down at the end.
  const levelBinders: string[] = [];
  for (const p of d.levelParams) {
    const lfName = nameToLfLevelVar(p);
    levelParamBindings.set(nameToString(p), lfName);
    levelBinders.push(lfName);
  }

  const cleanup = () => {
    for (const p of d.levelParams) levelParamBindings.delete(nameToString(p));
  };

  try {
    const T_lf = (() => {
      try {
        return lfExpr(d.type, []);
      } catch {
        return null;
      }
    })();
    const V_lf = (() => {
      try {
        return lfExpr(d.value, []);
      } catch {
        return null;
      }
    })();
    if (T_lf === null || V_lf === null) {
      skips.push(`${kindTag} ${declName}: untranslatable expression`);
      emit(`%% SKIP: ${kindTag} ${declName} — could not translate type/value to LF`);
      emitBlank();
      return;
    }

    // Try each synth separately.  On failure, fall through to HOLE
    // emission rather than abandoning the declaration — the
    // surrounding `/decl` is still emitted using `hole/defeq` proofs.
    let typeWf: Synth | null = null;
    let valTy: Synth | null = null;
    let typeWfErr: string | null = null;
    let valTyErr: string | null = null;
    try {
      typeWf = synth(d.type, { vars: [], hyps: [], tys: [] });
    } catch (e: unknown) {
      typeWfErr = e instanceof Error ? e.message : String(e);
    }
    try {
      valTy = synth(d.value, { vars: [], hyps: [], tys: [] });
    } catch (e: unknown) {
      valTyErr = e instanceof Error ? e.message : String(e);
    }

    // Existing duplicate-detection path: if a duplicate was already
    // seen earlier in this file, %unique on `declared` will catch it,
    // so we don't bother emitting a HOLE — keep the previous "declined"
    // comment so the harness doesn't accidentally mark the file SKIP.
    if ((typeWfErr || valTyErr) && dupCounter.size > 0) {
      const reason = typeWfErr ?? valTyErr ?? "synth failed";
      emit(`%% (declined to emit ${kindTag} ${declName}: ${reason})`);
      emit(`%% Duplicate already detected; %unique on \`declared\` will ABORT.`);
      emitBlank();
      return;
    }

    // For type-wf we need a sort literal `(esort U)` even when synth
    // failed.  Use lzero as the placeholder — hole/defeq accepts any
    // combination of (E1, E2, T) so the specific sort doesn't matter.
    const typeWfTyLF = typeWf ? lfExpr(typeWf.tyExpr, []) : "(esort lzero)";

    let typeWfProof: string;
    const typeWfHoleComment: string | null = typeWfErr
      ? `%% HOLE/defeq: type-wf for ${declName} — ${typeWfErr}`
      : null;
    if (typeWf) {
      typeWfProof = typeWf.proof;
    } else {
      recordHole("defeq");
      typeWfProof = `(hole/defeq ${T_lf} ${T_lf} ${typeWfTyLF})`;
    }

    let valuePf: string;
    const valTyHoleComment: string | null = valTyErr
      ? `%% HOLE/defeq: value-typed for ${declName} — ${valTyErr}`
      : null;
    if (valTy) {
      valuePf = valTy.proof;
      if (!exprEq(valTy.tyExpr, d.type)) {
        const bridge = bridgeTypes(valTy.tyExpr, d.type, { vars: [], hyps: [], tys: [] });
        if (bridge !== null) {
          valuePf = `(defeq/conv ${bridge} ${valTy.proof})`;
        } else {
          // bridge-failure path: synth produced a type, but it doesn't
          // match the declared type and no defeq-conv bridge could be
          // constructed.  We deliberately do NOT admit this via hole/defeq:
          // the same shape arises (a) when a TCB rule is missing (good
          // test that fails until iota/eta/K is implemented) and (b) when
          // the test genuinely has a type mismatch and should be rejected
          // (bad tests like 002_badDef).  Admitting via hole/defeq would
          // collapse both into 🩹 and lose the soundness signal on the
          // bad cases.  Instead, emit the inferred proof and let Twelf
          // reject; the file ends up ❌ for good tests (named TODOs for
          // future TCB work) and ✅ for bad tests.
          emit(`%% TRANSLATOR: could not bridge inferred type to declared type`);
          emit(`%%   inferred type kind: ${valTy.tyExpr.kind}`);
          emit(`%%   declared type kind: ${d.type.kind}`);
          emit(`%%   emitting valTy.proof; Twelf will likely reject.`);
        }
      }
    } else {
      recordHole("defeq");
      valuePf = `(hole/defeq ${V_lf} ${V_lf} ${T_lf})`;
    }

    // Polymorphic prefix: "{u_1 : lvl} ... {u_n : lvl}"  (empty if mono)
    const levelPrefix =
      levelBinders.length === 0 ? "" : levelBinders.map((n) => `{${n} : lvl}`).join(" ") + " ";
    // Body-side LF lambda over the level binders.  Twelf needs explicit
    // [u_1] ... [u_n] on the proof bodies to put the level binders in
    // scope; otherwise occurrences of `u_i` in the body get parsed as
    // free names and reconstruction fails.
    const bodyLambda = levelBinders.length === 0 ? "" : levelBinders.map((n) => `[${n}] `).join("");
    // Level argument list for use when referencing this decl from another
    // sub-proof (e.g. when /decl applies /type-wf and /value-typed).
    const levelArgList = levelBinders.length === 0 ? "" : " " + levelBinders.join(" ");
    // lvls expression for the `declared` index: (lcons u_1 (lcons u_2 ... lnil))
    const lvlsExpr =
      levelBinders.length === 0
        ? "lnil"
        : levelBinders.reduceRight((acc, n) => `(lcons ${n} ${acc})`, "lnil");

    // Twelf rejects `c : {u} T = body` when `u` has no strict occurrence
    // in the body.  This happens when a Lean decl is polymorphic over
    // a level param that doesn't appear in its type or value.  Use
    // %abbrev in that case — it accepts vacuous binders.
    const tw_decl =
      levelBinders.length > 0 && !allMentioned(levelBinders, T_lf, typeWfProof, typeWfTyLF)
        ? "%abbrev "
        : "";
    const vt_decl =
      levelBinders.length > 0 && !allMentioned(levelBinders, V_lf, valuePf, T_lf) ? "%abbrev " : "";

    emit(`%% ${kindTag} ${declName}`);
    if (typeWfHoleComment) emit(typeWfHoleComment);
    emit(`${tw_decl}${mn}/type-wf :`);
    emit(`   ${levelPrefix}defeq ${T_lf} ${T_lf} ${typeWfTyLF}`);
    emit(`   = ${bodyLambda}${typeWfProof}.`);
    emitBlank();
    if (valTyHoleComment) emit(valTyHoleComment);
    emit(`${vt_decl}${mn}/value-typed :`);
    emit(`   ${levelPrefix}defeq ${V_lf} ${V_lf} ${T_lf}`);
    emit(`   = ${bodyLambda}${valuePf}.`);
    emitBlank();
    const tw_inst = levelBinders.length === 0 ? `${mn}/type-wf` : `(${mn}/type-wf${levelArgList})`;
    const vt_inst =
      levelBinders.length === 0 ? `${mn}/value-typed` : `(${mn}/value-typed${levelArgList})`;
    emit(`${mn}/decl : ${levelPrefix}declared "${declName}" ${lvlsExpr}`);
    emit(`   ${T_lf}`);
    emit(`   (${info.dkindCtor} ${V_lf})`);
    emit(`   (${info.okCtor} ${tw_inst} ${vt_inst}).`);
    emitBlank();

    if (!declTable.has(declName)) {
      declTable.set(declName, {
        mangle: mn,
        levelParams: d.levelParams,
        type: d.type,
        kind: info.tableKind,
        value: d.value,
      });
    }
  } finally {
    cleanup();
  }
}

// Emit a "structural" declaration — i.e. one with no body, just a typed
// name.  Covers `axiom`, `inductive` type formers, constructors,
// recursors, and the four `Quot` builtins.  These all share the shape
//   <mn>/type-wf : {us..} defeq T T (esort L) = [us..] <typeWf>.
//   <mn>/decl    : {us..} declared "name" (lcons us..) T <dkindCtor>
//                  (<okCtor> (<mn>/type-wf us..)).
//
// `dkindCtor` is the dkind constant ("ax" / "indt" / "ctor" / "irec" /
// "quot").  `okCtor` is the corresponding `dkind-ok/...`.  `tableKind`
// is what goes into declTable for downstream consumers.
function emitStructuralDecl(
  declName: Name,
  levelParams: Name[],
  type: Expr,
  dkindCtor: string,
  okCtor: string,
  tableKind: DeclEntry["kind"],
  banner: string,
  positivityInfo?: { selfName: string; selfLevels: Level[] },
): void {
  const nameStr = nameToString(declName);
  const mn = freshMangleForDuplicates(mangle(declName), nameStr);
  // duplicate → mn now ends in "__dup<n>"; both declarations are
  // emitted so Twelf's %unique on `declared` can detect the overlap.

  const levelBinders: string[] = [];
  for (const p of levelParams) {
    const lfName = nameToLfLevelVar(p);
    levelParamBindings.set(nameToString(p), lfName);
    levelBinders.push(lfName);
  }

  const cleanup = () => {
    for (const p of levelParams) levelParamBindings.delete(nameToString(p));
  };

  try {
    const T_lf = (() => {
      try {
        return lfExpr(type, []);
      } catch {
        return null;
      }
    })();
    if (T_lf === null) {
      skips.push(`${banner} ${nameStr}: untranslatable type`);
      emit(`%% SKIP: ${banner} ${nameStr} — could not translate type to LF`);
      emitBlank();
      return;
    }

    let typeWf: Synth | null = null;
    let typeWfErr: string | null = null;
    try {
      typeWf = synth(type, { vars: [], hyps: [], tys: [] });
    } catch (e: unknown) {
      typeWfErr = e instanceof Error ? e.message : String(e);
    }

    // When a duplicate name has already been emitted in this file, the
    // resulting LF name collision in declTable can make downstream
    // synth fail in ways that aren't real translator limitations —
    // they're side effects of the very malformed-NDJSON we're trying
    // to report.  In that case skip the offending decl silently
    // (without a `%% SKIP:` marker) so the harness doesn't mark the
    // file 🤷; Twelf's `%unique declared` will fire on the duplicate
    // pair and ABORT, which is the genuine Twelf-verified rejection.
    if (typeWfErr && dupCounter.size > 0) {
      emit(`%% (declined to emit ${banner} ${nameStr}: ${typeWfErr})`);
      emit(
        `%% This file already has a duplicate-name violation that %unique on \`declared\` will catch; downstream synth fallout doesn't need its own SKIP.`,
      );
      emitBlank();
      return;
    }

    // Placeholder sort when synth couldn't determine one.  hole/defeq
    // accepts any (E1, E2, T) so the specific sort doesn't matter for
    // typing — the decl is admitted, not verified.
    const typeWfTyLF = typeWf ? lfExpr(typeWf.tyExpr, []) : "(esort lzero)";
    let typeWfProof: string;
    const typeWfHoleComment: string | null = typeWfErr
      ? `%% HOLE/defeq: type-wf for ${nameStr} — ${typeWfErr}`
      : null;
    if (typeWf) {
      typeWfProof = typeWf.proof;
    } else {
      recordHole("defeq");
      typeWfProof = `(hole/defeq ${T_lf} ${T_lf} ${typeWfTyLF})`;
    }

    const levelPrefix =
      levelBinders.length === 0 ? "" : levelBinders.map((n) => `{${n} : lvl}`).join(" ") + " ";
    const bodyLambda = levelBinders.length === 0 ? "" : levelBinders.map((n) => `[${n}] `).join("");
    const levelArgList = levelBinders.length === 0 ? "" : " " + levelBinders.join(" ");
    const lvlsExpr =
      levelBinders.length === 0
        ? "lnil"
        : levelBinders.reduceRight((acc, n) => `(lcons ${n} ${acc})`, "lnil");

    const tw_decl =
      levelBinders.length > 0 && !allMentioned(levelBinders, T_lf, typeWfProof, typeWfTyLF)
        ? "%abbrev "
        : "";

    emit(`%% ${banner} ${nameStr}`);
    if (typeWfHoleComment) emit(typeWfHoleComment);
    emit(`${tw_decl}${mn}/type-wf :`);
    emit(`   ${levelPrefix}defeq ${T_lf} ${T_lf} ${typeWfTyLF}`);
    emit(`   = ${bodyLambda}${typeWfProof}.`);
    emitBlank();
    const tw_inst = levelBinders.length === 0 ? `${mn}/type-wf` : `(${mn}/type-wf${levelArgList})`;

    // Inductive type formers also need a structural `ends-in-sort` proof:
    // the kernel demands the signature to be `Π ... → Sort _`, not an
    // arbitrary well-typed term.  Two cases:
    //   • translator can build the proof → emit it as a definition;
    //   • translator can't build it AND the type is monomorphic → emit
    //     `%solve ${mn}/ends-in-sort : ends-in-sort ${T_lf}.` so Twelf
    //     itself runs proof search and ABORTs if no proof exists.
    //     This is a genuine Twelf-verified rejection: the brokenness is
    //     expressed in LF (the `ends-in-sort` family) and Twelf decides.
    //   • can't build it AND polymorphic → fall back to SKIP (we'd
    //     need to specialize the level params to close the %solve goal).
    let okArgs = tw_inst;
    if (tableKind === "indt") {
      const eis = endsInSortProof(type, []);
      if (eis === null && levelBinders.length > 0) {
        emit(
          `%% SKIP: inductive ${nameStr} — type signature is not a forall-chain ending in a sort literal (polymorphic; would need a Twelf %solve over closed instantiations)`,
        );
        emitBlank();
        skips.push(`inductive ${nameStr}: type signature is not Π…→Sort_ (polymorphic)`);
        return;
      }
      if (eis === null) {
        // Defer to Twelf-side proof search.
        emit(`%% Translator can't construct ends-in-sort for "${nameStr}";`);
        emit(`%% deferring to Twelf — %solve ABORTs if no proof exists.`);
        emit(`%solve ${mn}/ends-in-sort : ends-in-sort ${T_lf}.`);
        emitBlank();
      } else {
        // The ends-in-sort proof is monomorphic in the level binders too —
        // it just structurally walks foralls and ends at sorts.  Wrap with
        // [u..] body lambdas if needed for poly inductives.
        const eisWithLambda = levelBinders.length === 0 ? eis : `${bodyLambda}${eis}`;
        // Same strict-occurrence concern as /type-wf: if no level binder
        // appears in the body, Twelf rejects the universal quantifier and
        // we need %abbrev.
        const eis_decl =
          levelBinders.length > 0 && !allMentioned(levelBinders, T_lf, eis) ? "%abbrev " : "";
        // Emit it as a separate constant so the /decl line stays readable.
        emit(`${eis_decl}${mn}/ends-in-sort :`);
        emit(`   ${levelPrefix}ends-in-sort ${T_lf}`);
        emit(`   = ${eisWithLambda}.`);
        emitBlank();
      }
      const eis_inst =
        levelBinders.length === 0 ? `${mn}/ends-in-sort` : `(${mn}/ends-in-sort${levelArgList})`;
      okArgs = `${tw_inst} ${eis_inst}`;
    }

    // Constructor strict-positivity witness.  See tcb.elf for the
    // adequacy story: we HOAS-bind the inductive's self-reference,
    // structurally check absence/strict-positivity/ctor-spine, and
    // emit a ctor-positive/intro with explicit T_HOAS (Twelf's
    // higher-order pattern unification can't reconstruct T_HOAS
    // when ctors duplicate bound variables, e.g. Eq.refl).
    // SAFELIST NOTE: the LF encoding of `ctor-positive` is unsound under
    // %solve when the failure is a *field-position* issue (negative
    // occurrence inside an arrow within a ctor argument).  Twelf's HOU
    // can pick a T_HOAS that leaves the offending `(econst N0 LS0)`
    // occurrences unreplaced — making them S-free inside the closure —
    // and then `strict-pos/no-occur` fires vacuously to "prove" the
    // field strictly positive.  Concretely, for ctor `mk : (I → I) → I`,
    // Twelf picks T_HOAS = [e] eforall (eforall (econst I) ([_] econst I))
    // ([_] e), leaving the inner I→I closed and unchecked.
    //
    // The failure is sound to defer when it's a *result-head* issue
    // (the ctor returns something other than the inductive at the
    // expected level instantiation): `applies-self` only inhabits chains
    // ending in [S] S, with no rule to make a constant or wrong-named
    // head match, so Twelf's search correctly aborts.  We detect this
    // case by walking past leading Π binders and checking whether
    // `buildAppliesSelf` accepts the result.
    if (tableKind === "ctor" && positivityInfo) {
      const cs = buildCtorSpine(type, positivityInfo.selfName, positivityInfo.selfLevels, []);
      const indLvlsLF = lfLvls(positivityInfo.selfLevels);
      if (cs === null) {
        // Walk past leading binders to the result and test the head.
        let resultT = type;
        while (resultT.kind === "forallE") resultT = resultT.body;
        const headOK =
          buildAppliesSelf(resultT, positivityInfo.selfName, positivityInfo.selfLevels) !== null;
        const monomorphic = levelBinders.length === 0;
        if (!headOK && monomorphic) {
          // Head-mismatch + monomorphic: sound to defer to Twelf.
          emit(`%% Translator can't build ctor-positive for "${nameStr}";`);
          emit(`%% result-type head isn't the inductive — deferring to Twelf,`);
          emit(`%% which can soundly abort (no T_HOAS makes applies-self fire on a wrong head).`);
          emit(
            `%solve ${mn}/positivity : ctor-positive "${positivityInfo.selfName}" ${indLvlsLF} ${T_lf}.`,
          );
          emitBlank();
        } else if (!headOK && !monomorphic) {
          // Head-mismatch + polymorphic: substitute level params with
          // distinct concrete levels (lzero, lsucc lzero, ...) and
          // %solve on the closed instance.  Substitution preserves
          // syntactic structure, so any head mismatch in the original
          // is preserved in the substituted instance.  If %solve fails
          // there, the original polymorphic ctor is bad too.
          //
          // Note we don't emit the polymorphic decl below: it'd
          // reference the now-monomorphic positivity binding, which
          // would itself be a Twelf error.  Twelf aborts on %solve
          // first; downstream content doesn't matter.
          const sub = distinctLevelSub(levelParams);
          const substType = substExprLevels(type, sub);
          const substT_lf = lfExpr(substType, []);
          const substIndLevels = positivityInfo.selfLevels.map((l) => substLevel(l, sub));
          const substIndLvlsLF = lfLvls(substIndLevels);
          emit(`%% Translator can't build ctor-positive for polymorphic "${nameStr}";`);
          emit(
            `%% result-type head doesn't match the inductive at the ctor's level instantiation.`,
          );
          emit(`%% Substituting [${levelParams.map((p) => nameToString(p)).join(",")}] with`);
          emit(`%% distinct concrete levels exposes the mismatch in a closed %solve goal.`);
          emit(
            `%solve ${mn}/positivity_probe : ctor-positive "${positivityInfo.selfName}" ${substIndLvlsLF} ${substT_lf}.`,
          );
          emitBlank();
          return;
        } else {
          // Field-position issue: the ctor-positive LF encoding has a
          // soundness gap (negative occurrence in a Π-domain inside a
          // ctor argument; T_HOAS reconstruction lets it slip through).
          // Previously SKIPped; now admit via hole/ctor-positive so the
          // surrounding /decl is still emitted and downstream lookups
          // succeed.  The 🩹 verdict advertises that the positivity
          // check is unproven.
          recordHole("ctor-positive");
          emit(
            `%% HOLE/ctor-positive: ${nameStr} — strict positivity in ${positivityInfo.selfName} not witnessable by current encoding (likely field-position negative occurrence)`,
          );
          const cp_decl_h =
            levelBinders.length > 0 && !allMentioned(levelBinders, T_lf) ? "%abbrev " : "";
          emit(`${cp_decl_h}${mn}/positivity :`);
          emit(`   ${levelPrefix}ctor-positive "${positivityInfo.selfName}" ${indLvlsLF} ${T_lf}`);
          emit(
            `   = ${bodyLambda}(hole/ctor-positive "${positivityInfo.selfName}" ${indLvlsLF} ${T_lf}).`,
          );
          emitBlank();
        }
      } else {
        const hoasBody = lfExprHoasSelf(
          type,
          positivityInfo.selfName,
          positivityInfo.selfLevels,
          [],
          "S",
        );
        const positivityProof = `(ctor-positive/intro ([S] ${hoasBody}) ${cs})`;
        const cp_decl =
          levelBinders.length > 0 && !allMentioned(levelBinders, T_lf, hoasBody, cs)
            ? "%abbrev "
            : "";
        emit(`${cp_decl}${mn}/positivity :`);
        emit(`   ${levelPrefix}ctor-positive "${positivityInfo.selfName}" ${indLvlsLF} ${T_lf}`);
        emit(
          `   = ${levelBinders.length === 0 ? positivityProof : `${bodyLambda}${positivityProof}`}.`,
        );
        emitBlank();
      }
      const cp_inst =
        levelBinders.length === 0 ? `${mn}/positivity` : `(${mn}/positivity${levelArgList})`;
      okArgs = `${tw_inst} ${cp_inst}`;
    }

    emit(`${mn}/decl : ${levelPrefix}declared "${nameStr}" ${lvlsExpr}`);
    emit(`   ${T_lf}`);
    emit(`   ${dkindCtor}`);
    emit(`   (${okCtor} ${okArgs}).`);
    emitBlank();

    if (!declTable.has(nameStr)) {
      declTable.set(nameStr, {
        mangle: mn,
        levelParams,
        type,
        kind: tableKind,
      });
    }
  } finally {
    cleanup();
  }
}

function emitAxiom(d: Decl & { kind: "axiom" }): void {
  emitStructuralDecl(d.name, d.levelParams, d.type, "ax", "dkind-ok/ax", "ax", "axiom");
}

// --- Pre-flight checks for inductive wellformedness invariants ----------
//
// The LF encoding's ctor-positive judgment verifies strict positivity and
// that the result-type head is the inductive, but doesn't verify several
// further kernel-level invariants that Lean checks:
//   (a) numParams ≤ #leading Π binders in the inductive's type signature
//   (b) the ctor's result type applies the inductive to its bound param
//       binders in canonical order (i.e., its first numParams args are
//       bvars referring to the corresponding param binders).
//   (c) the ctor's result-type *index* args don't mention the inductive
//       (would put the inductive in a non-strictly-positive position).
//   (d) when the inductive's universe is a concrete `Sort n` (n > 0) and
//       a ctor field's type is a concrete `Sort k`, then k+1 ≤ n.  We
//       only check the easy concrete case; polymorphic inductives and
//       Prop-ctors (n = 0) are passed through unchecked.
//
// (a) catches 042_inductTooFewParams.
// (b) catches 043 / 044 (wrong / swapped param args).
// (c) catches 046_inductInIndex.
// (d) catches 054_typeWithTooHighTypeField.
//
// All are translator-side rejections: on violation, emit `%% SKIP:` and
// decline to emit the offending declaration.  The harness sees the SKIP
// and marks the file as INCOMPLETE.  This is intentionally a 🤷, not a
// ❌/💥: Twelf isn't checking these conditions.  The principled path
// forward is to encode each check inside the LF signature so Twelf
// rejects the witness directly; until then, these tests don't count
// as success stories even when the OUTCOME happens to align with the
// .ndjson's expected verdict.

function countLeadingForalls(e: Expr): number {
  let n = 0;
  let cur = e;
  while (cur.kind === "forallE") {
    cur = cur.body;
    n++;
  }
  return n;
}

// Strip leading Π binders and return the result-type expression.
function _stripForalls(e: Expr, n: number): Expr | null {
  let cur = e;
  for (let i = 0; i < n; i++) {
    if (cur.kind !== "forallE") return null;
    cur = cur.body;
  }
  return cur;
}

// If the level is a chain of lsucc applied to lzero, return its numeric
// value; otherwise null (we don't reason about max/imax/param levels).
function levelToNumber(l: Level): number | null {
  let n = 0;
  let cur = l;
  while (cur.kind === "succ") {
    cur = cur.arg;
    n++;
  }
  return cur.kind === "zero" ? n : null;
}

// Inductive's universe, if its type signature ends in a concrete Sort.
function inductiveResultUniverse(t: Expr): Level | null {
  let cur = t;
  while (cur.kind === "forallE") cur = cur.body;
  return cur.kind === "sort" ? cur.level : null;
}

// Returns null if the ctor's structure passes all checks (b), (c), (d);
// otherwise a human-readable mismatch.
function checkCtorStructure(
  ctorType: Expr,
  indName: string,
  indLevels: Level[],
  indUniverse: Level | null,
  numParams: number,
  numFields: number,
): string | null {
  // Walk param binders + check (d) on field binders.
  let e = ctorType;
  for (let i = 0; i < numParams; i++) {
    if (e.kind !== "forallE") {
      return `expected ≥ ${numParams + numFields} leading Π binders, found ${i}`;
    }
    e = e.body;
  }
  const indUnivN = indUniverse !== null ? levelToNumber(indUniverse) : null;
  for (let f = 0; f < numFields; f++) {
    if (e.kind !== "forallE") {
      return `expected ≥ ${numParams + numFields} leading Π binders, found ${numParams + f}`;
    }
    // (d) concrete-case field universe check.  Only fires for non-Prop
    // inductives with concrete universe, and for fields whose type is a
    // concrete `Sort k`.
    if (indUnivN !== null && indUnivN > 0 && e.type.kind === "sort") {
      const fieldLvlN = levelToNumber(e.type.level);
      if (fieldLvlN !== null && fieldLvlN + 1 > indUnivN) {
        return `field #${f + 1} has type Sort ${fieldLvlN} (which lives at Sort ${fieldLvlN + 1}); inductive is at Sort ${indUnivN}, so the field's universe must be ≤ ${indUnivN - 1}`;
      }
    }
    e = e.body;
  }
  // e is now the result type.  Decompose.
  const args: Expr[] = [];
  while (e.kind === "app") {
    args.unshift(e.arg);
    e = e.fn;
  }
  if (e.kind !== "const") {
    return `result-type head is not a constant (got ${e.kind})`;
  }
  if (nameToString(e.name) !== indName) {
    // Don't reject here.  When the result-type head isn't the inductive,
    // `buildAppliesSelf` will fail downstream and the ctor-positive
    // emit-path will defer to Twelf via %solve — a sound deferral
    // (no `applies-self` rule fires on a wrong head).  We want Twelf-
    // verified rejection rather than a translator-side SKIP here.
    return null;
  }
  if (args.length < numParams) {
    return `result-type has ${args.length} args, expected ≥ ${numParams} (one per param)`;
  }
  // (b) param args must be bvars referring to the param binders in order.
  for (const [i, a] of args.slice(0, numParams).entries()) {
    const expected = numFields + numParams - 1 - i;
    if (a.kind !== "bvar" || a.deBruijn !== expected) {
      const got = a.kind === "bvar" ? `bvar(${a.deBruijn})` : a.kind;
      return `result-type param arg #${i + 1} should be bvar(${expected}) (the param binder), got ${got}`;
    }
  }
  // (c) index args must not mention the inductive.
  for (const [i, a] of args.slice(numParams).entries()) {
    if (exprMentions(a, indName, indLevels)) {
      return `result-type index arg #${i + 1} mentions the inductive "${indName}" (not allowed in index position)`;
    }
  }
  return null;
}

// Name equality is provided by the existing structural `nameEq` above.

function emitInductive(ind: Inductive): void {
  // Pre-flight: reject inductives that violate kernel invariants the LF
  // encoding doesn't catch (see comments above checkCtorStructure).
  for (const t of ind.types) {
    const nb = countLeadingForalls(t.type);
    if (t.numParams > nb) {
      // Soundness-critical: this mismatch isn't caught by any Twelf-side
      // judgment.  Keep as SKIP rather than letting through to a
      // potentially-admitted /decl.
      const ns = nameToString(t.name);
      emit(
        `%% SKIP: inductive ${ns} declares numParams=${t.numParams} but its type has only ${nb} leading Π binder${nb === 1 ? "" : "s"}`,
      );
      emitBlank();
      skips.push(`inductive ${ns}: numParams=${t.numParams} > #binders=${nb}`);
      return;
    }
  }
  for (const c of ind.ctors) {
    const indSpec = ind.types.find((t) => nameEq(t.name, c.induct));
    if (!indSpec) continue;
    const indName = nameToString(c.induct);
    const indLevels: Level[] = indSpec.levelParams.map((name) => ({
      kind: "param" as const,
      name,
    }));
    const indUniverse = inductiveResultUniverse(indSpec.type);
    const why = checkCtorStructure(
      c.type,
      indName,
      indLevels,
      indUniverse,
      c.numParams,
      c.numFields,
    );
    if (why !== null) {
      // Soundness-critical: `buildCtorSpine` succeeds structurally even
      // when bvars or param-arity are wrong, which means letting through
      // produces an admitted-but-invalid ctor-positive witness.  Keep
      // SKIP for all checkCtorStructure failures.
      const cs = nameToString(c.name);
      emit(`%% SKIP: ctor ${cs} — ${why}`);
      emitBlank();
      skips.push(`ctor ${cs}: ${why}`);
      return;
    }
  }

  // 1. Type formers.
  for (const t of ind.types) {
    emitStructuralDecl(t.name, t.levelParams, t.type, "indt", "dkind-ok/indt", "indt", "inductive");
  }
  // 2. Constructors.  Each ctor's positivity check needs to know
  //    its parent inductive's name and level instantiation.
  for (const c of ind.ctors) {
    const indTypeSpec = ind.types.find((t) => nameEq(t.name, c.induct));
    if (!indTypeSpec) {
      // Should not happen for well-formed lean4export output.
      emit(
        `%% SKIP: ctor ${nameToString(c.name)} — induct field doesn't match any type in this inductive block`,
      );
      emitBlank();
      skips.push(`ctor ${nameToString(c.name)}: induct pointer invalid`);
      continue;
    }
    const selfName = nameToString(c.induct);
    const selfLevels: Level[] = c.levelParams.map((name) => ({ kind: "param" as const, name }));
    emitStructuralDecl(
      c.name,
      c.levelParams,
      c.type,
      "ctor",
      "dkind-ok/ctor",
      "ctor",
      "inductive ctor",
      { selfName, selfLevels },
    );
  }
  // 3. Recursors.
  for (const r of ind.recursors) {
    emitStructuralDecl(
      r.name,
      r.levelParams,
      r.type,
      "irec",
      "dkind-ok/irec",
      "irec",
      "inductive recursor",
    );
  }
  // 4. Stage-1 iota helpers (if this inductive qualifies as a stage-1 enum).
  emitStage1EnumIotaHelpers(ind);
}

// Emit `<Foo>/as-enum` and per-ctor `<Foo_ctor>/iota` definitions if this
// inductive qualifies as a stage-1 enum (no level params, 0-3 ctors all
// with zero fields, single non-mutual recursor).  These are *definitions*
// (= proof terms) inhabiting closed-family judgments (`enum-rec-type`,
// `defeq`); they don't extend any open family, so the soundness story is
// unchanged.  Downstream consumers (translator-emitted defeq proofs that
// want to compute iota, or hand-written witnesses) can invoke them.
function emitStage1EnumIotaHelpers(ind: Inductive): void {
  // Single-type, single-recursor blocks only (no mutual/nested for stage 1).
  if (ind.types.length !== 1) return;
  if (ind.recursors.length !== 1) return;
  const indSpec = ind.types[0];
  const recSpec = ind.recursors[0];
  if (indSpec === undefined || recSpec === undefined) return;
  // No level params on the inductive itself.
  if (indSpec.levelParams.length !== 0) return;
  // Ctors for this inductive (already sorted by cidx in parse.ts).
  const ctorList = ind.ctors.filter((c) => nameEq(c.induct, indSpec.name));
  // Stage 1: 0-3 ctors.
  if (ctorList.length > 3) return;
  // All ctors must have zero fields (so no recursive args, no field-passing).
  for (const c of ctorList) {
    if (c.numFields !== 0) return;
  }
  // Recursor must have exactly one level parameter (the motive's level),
  // no inductive params or indices, one motive, and one minor per ctor.
  if (recSpec.levelParams.length !== 1) return;
  if (recSpec.numParams !== 0) return;
  if (recSpec.numIndices !== 0) return;
  if (recSpec.numMotives !== 1) return;
  if (recSpec.numMinors !== ctorList.length) return;

  const indName = nameToString(indSpec.name);
  const indMangle = mangle(indSpec.name);
  const recName = nameToString(recSpec.name);
  const recMangle = mangle(recSpec.name);
  const ctorInfo = ctorList.map((c) => ({
    name: nameToString(c.name),
    nameStruct: c.name,
    mangle: mangle(c.name),
  }));
  const k = ctorInfo.length;
  const u = "u";

  // Register each ctor in iotaTable so reduceOnce can invoke the helper.
  const allCtors = ctorInfo.map((c) => ({ name: c.name, nameStruct: c.nameStruct }));
  for (const [i, ci] of ctorInfo.entries()) {
    iotaTable.set(ci.name, {
      recName,
      indName: indSpec.name,
      indNameStr: indName,
      ctorMangle: ci.mangle,
      position: i,
      allCtors,
    });
  }

  // Build the full recursor-type expression to assert via enum-rec-type.
  const indConst = `(econst "${indName}" lnil)`;
  const motiveType = `(eforall ${indConst} ([x] (esort ${u})))`;
  const resultPart = `(eforall ${indConst} ([t] (eapp M t)))`;
  let bodyM = resultPart;
  for (const ci of [...ctorInfo].reverse()) {
    bodyM = `(eforall (eapp M (econst "${ci.name}" lnil)) ([x] ${bodyM}))`;
  }
  const fullRecType = `(eforall ${motiveType} ([M] ${bodyM}))`;

  let cnamesExpr = "cnil";
  for (const ci of [...ctorInfo].reverse()) {
    cnamesExpr = `(ccons "${ci.name}" ${cnamesExpr})`;
  }

  let asEnumBody = "enum-rec-body/done";
  for (let i = k - 1; i >= 0; i--) {
    asEnumBody = `(enum-rec-body/minor ([m${i + 1}] [hm${i + 1}] ${asEnumBody}))`;
  }

  emit(`%% stage-1 enum iota helpers: ${indName}`);
  emit(`${indMangle}/as-enum : {${u} : lvl}`);
  emit(`   enum-rec-type`);
  emit(`      ${fullRecType}`);
  emit(`      "${indName}" lnil ${cnamesExpr} ${u}`);
  emit(`   = [${u}] enum-rec-type/intro ([M] [hM] ${asEnumBody}).`);
  emitBlank();

  if (k === 0) return; // no iota helpers — no ctor to reduce on.

  // Per-ctor iota helpers.
  const positions = ["first", "second", "third"];
  for (const [i, c] of ctorInfo.entries()) {
    const pos = positions[i] ?? i.toString();
    const ruleName = k === 1 ? "defeq/iota-enum-1" : `defeq/iota-enum-${k}-${pos}`;

    // LHS = recursor applied to motive, k cases, then the i-th ctor.
    let lhs = `(econst "${recName}" (lcons ${u} lnil))`;
    lhs = `(eapp ${lhs} M)`;
    for (let j = 0; j < k; j++) {
      lhs = `(eapp ${lhs} Mp${j + 1})`;
    }
    lhs = `(eapp ${lhs} (econst "${c.name}" lnil))`;

    const rhs = `Mp${i + 1}`;
    const retType = `(eapp M (econst "${c.name}" lnil))`;

    // Build premise lines and body lambda bindings.
    const premiseLines: string[] = [];
    premiseLines.push(`   defeq M M ${motiveType}`);
    for (const [j, cj] of ctorInfo.entries()) {
      premiseLines.push(`   -> defeq Mp${j + 1} Mp${j + 1} (eapp M (econst "${cj.name}" lnil))`);
    }

    // Build the body: defeq/extra applied to the iota rule applied to all premises.
    const ruleArgs: string[] = [];
    ruleArgs.push(`(${recMangle}/decl ${u})`);
    for (const ci of ctorInfo) ruleArgs.push(`${ci.mangle}/decl`);
    ruleArgs.push(`(${indMangle}/as-enum ${u})`);
    ruleArgs.push("hM");
    for (let j = 0; j < k; j++) ruleArgs.push(`hMp${j + 1}`);
    const lambdaBindings = ["hM", ...Array.from({ length: k }, (_, j) => `hMp${j + 1}`)]
      .map((name) => `[${name}]`)
      .join(" ");

    emit(`${c.mangle}/iota : {${u} : lvl}`);
    for (const p of premiseLines) emit(p);
    emit(`   -> defeq ${lhs} ${rhs} ${retType}`);
    emit(`   = [${u}] ${lambdaBindings}`);
    emit(`     defeq/extra (${ruleName} ${ruleArgs.join(" ")}).`);
    emitBlank();
  }
}

// =====================================================================
// Main: read ParsedEnv JSON on stdin, dispatch by decl kind.
// =====================================================================

async function readAllStdin(): Promise<string> {
  const chunks: Buffer[] = [];
  for await (const chunk of process.stdin) {
    chunks.push(chunk as Buffer);
  }
  return Buffer.concat(chunks).toString("utf8");
}

async function main(): Promise<void> {
  const raw = await readAllStdin();
  const parsed = transformNamesFromJSON(JSON.parse(raw)) as ParsedEnv;

  for (const decl of parsed.decls) {
    try {
      switch (decl.kind) {
        case "def":
        case "thm":
        case "opaque":
          emitValDecl(decl);
          break;
        case "axiom":
          emitAxiom(decl);
          break;
        case "quot":
          emit(`%% SKIP: quot not yet supported`);
          break;
        case "inductive":
          emitInductive(decl);
          break;
      }
    } catch (e: unknown) {
      const msg = e instanceof Error ? e.message : String(e);
      const tag = decl.kind;
      skips.push(`${tag}: untranslatable (${msg})`);
      emit(`%% SKIP: ${tag} — untranslatable: ${msg}`);
      emitBlank();
    }
  }

  // (The global %mode / %worlds / %unique checks on the `declared`
  // relation live in final-checks.elf, loaded after every environment
  // file.  Keeping the per-environment file free of those directives
  // means changes to the closure check apply uniformly.)

  if (skips.length > 0) {
    emit(``);
    emit(`%% Translator summary:`);
    for (const s of skips) emit(`%%   - ${s}`);
  }

  // Prepend file-level preludes:
  //   1. Hole axiom declarations for every hole tag the translator used.
  //      These are emitted inline (not in sources.cfg) so Twelf's
  //      higher-order unification can't sneak them in to discharge
  //      `%solve` obligations elsewhere in the global signature.
  //   2. %solve declarations for every nat literal encountered by lfExpr
  //      (discharges the `n >= 0` premise of `enatlit` from tcb.elf).
  const prelude: string[] = [];
  if (holesUsed.size > 0) {
    prelude.push(`%% This file contains ${holesUsed.size} hole tag(s):`);
    for (const tag of holesUsed) {
      prelude.push(`%%   - hole/${tag} (count: see HOLE/${tag} markers below)`);
    }
    prelude.push(`%% Files with any hole/<tag> use are NOT Twelf-verified.`);
    for (const tag of holesUsed) {
      prelude.push(HOLE_AXIOM_DECLS[tag]!);
    }
    prelude.push(``);
  }
  if (natLiteralsSeen.size > 0) {
    for (const n of natLiteralsSeen) {
      prelude.push(`%solve nonneg_${n} : ${n} >= 0.`);
    }
    prelude.push(``);
  }

  process.stdout.write([...prelude, ...out].join("\n") + "\n");
}

main().catch((err: unknown) => {
  // eslint-disable-next-line no-console
  console.error(err);
  process.exit(1);
});
