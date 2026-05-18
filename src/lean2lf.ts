#!/usr/bin/env -S node --experimental-strip-types
// lean2lf.ts — translate lean4export NDJSON on stdin to Twelf LF on stdout.
//
// MVP scope: covers patterns used by tutorial/good examples 001-005.
//   - def declarations, no universe polymorphism
//   - Sort, ForallE, Lam expressions; bvar→HOAS conversion
//   - Type synthesis with lvl-eq–driven defeq/conv for sort-level mismatches
//
// Not yet handled (translator skips with a comment, file remains valid):
//   - Const references and δ/β reduction chains (needed by 006+)
//   - Universe polymorphism (needed by 008+)
//   - Theorems, opaques, axioms, inductives
//
// Per the discipline: if the translator can't construct a proof, it
// emits a Twelf comment recording the skip rather than an axiom.
// "Trusted-but-not-verified" is exactly the off-the-rails-ness we
// rejected.
//
// TODO: when zod is available, replace the ad-hoc `parse*` functions
// with z.discriminatedUnion / z.parse calls. The shape we validate is
// faithful to lean4export's wire format.

import * as readline from "node:readline";

// =====================================================================
// 1. NDJSON wire format types
// =====================================================================

// --- Names. Index 0 = anonymous (implicit).
type NameRec =
  | { tag: "str"; idx: number; pre: number; str: string }
  | { tag: "num"; idx: number; pre: number; i: number };

// --- Levels. Index 0 = zero (implicit).
type LevelRec =
  | { tag: "succ"; idx: number; arg: number }
  | { tag: "max"; idx: number; l: number; r: number }
  | { tag: "imax"; idx: number; l: number; r: number }
  | { tag: "param"; idx: number; name: number };

// --- Expressions.
type BinderInfo = "default" | "implicit" | "strictImplicit" | "instImplicit";
type ExprRec =
  | { tag: "bvar"; idx: number; deBruijn: number }
  | { tag: "sort"; idx: number; level: number }
  | { tag: "const"; idx: number; name: number; us: number[] }
  | { tag: "app"; idx: number; fn: number; arg: number }
  | { tag: "lam"; idx: number; bi: BinderInfo; name: number; type: number; body: number }
  | { tag: "forallE"; idx: number; bi: BinderInfo; name: number; type: number; body: number }
  | { tag: "letE"; idx: number; name: number; type: number; value: number; body: number }
  | { tag: "proj"; idx: number; typeName: number; pidx: number; struct: number }
  | { tag: "natLit"; idx: number; value: string }
  | { tag: "strLit"; idx: number; value: string };

// --- Top-level items (declarations).
type DefRec = {
  tag: "def";
  name: number;
  levelParams: number[];
  type: number;
  value: number;
  hints: any;
  safety: string;
};
type ThmRec = { tag: "thm"; name: number; levelParams: number[]; type: number; value: number };
type AxRec = { tag: "axiom"; name: number; levelParams: number[]; type: number };
type OpqRec = { tag: "opaque"; name: number; levelParams: number[]; type: number; value: number };
type QuotRec = { tag: "quot" };
type IndTypeSpec = {
  name: number;
  type: number;
  levelParams: number[];
  ctors: number[];
  numParams: number;
  numIndices: number;
  isRec: boolean;
  isReflexive: boolean;
};
type IndCtorSpec = {
  name: number;
  type: number;
  levelParams: number[];
  cidx: number;
  induct: number;
  numFields: number;
  numParams: number;
};
type IndRecRule = { ctor: number; nfields: number; rhs: number };
type IndRecSpec = {
  name: number;
  type: number;
  levelParams: number[];
  numParams: number;
  numIndices: number;
  numMotives: number;
  numMinors: number;
  rules: IndRecRule[];
};
type IndRec = { tag: "inductive"; types: IndTypeSpec[]; ctors: IndCtorSpec[]; recs: IndRecSpec[] };
type MetaRec = { tag: "meta" };
type Item =
  | NameRec
  | LevelRec
  | ExprRec
  | DefRec
  | ThmRec
  | AxRec
  | OpqRec
  | QuotRec
  | IndRec
  | MetaRec;

// =====================================================================
// 2. NDJSON parsing (hand-rolled; would be one z.discriminatedUnion)
// =====================================================================

function asInt(x: unknown): number | null {
  return typeof x === "number" && Number.isInteger(x) ? x : null;
}
function asStr(x: unknown): string | null {
  return typeof x === "string" ? x : null;
}
function asArrayOfInts(x: unknown): number[] | null {
  if (!Array.isArray(x)) return null;
  const out: number[] = [];
  for (const e of x) {
    const n = asInt(e);
    if (n === null) return null;
    out.push(n);
  }
  return out;
}

function parseLine(line: string): Item | null {
  let obj: any;
  try {
    obj = JSON.parse(line);
  } catch {
    return null;
  }
  if (typeof obj !== "object" || obj === null) return null;

  // Names
  if ("in" in obj && "str" in obj) {
    const idx = asInt(obj.in)!;
    const pre = asInt(obj.str.pre)!;
    const str = asStr(obj.str.str)!;
    return { tag: "str", idx, pre, str };
  }
  if ("in" in obj && "num" in obj) {
    return { tag: "num", idx: asInt(obj.in)!, pre: asInt(obj.num.pre)!, i: asInt(obj.num.i)! };
  }

  // Levels
  if ("il" in obj && "succ" in obj)
    return { tag: "succ", idx: asInt(obj.il)!, arg: asInt(obj.succ)! };
  if ("il" in obj && "max" in obj)
    return { tag: "max", idx: asInt(obj.il)!, l: obj.max[0], r: obj.max[1] };
  if ("il" in obj && "imax" in obj)
    return { tag: "imax", idx: asInt(obj.il)!, l: obj.imax[0], r: obj.imax[1] };
  if ("il" in obj && "param" in obj)
    return { tag: "param", idx: asInt(obj.il)!, name: asInt(obj.param)! };

  // Expressions
  if ("ie" in obj) {
    const idx = asInt(obj.ie)!;
    if ("bvar" in obj) return { tag: "bvar", idx, deBruijn: asInt(obj.bvar)! };
    if ("sort" in obj) return { tag: "sort", idx, level: asInt(obj.sort)! };
    if ("const" in obj)
      return { tag: "const", idx, name: asInt(obj.const.name)!, us: asArrayOfInts(obj.const.us)! };
    if ("app" in obj) return { tag: "app", idx, fn: asInt(obj.app.fn)!, arg: asInt(obj.app.arg)! };
    if ("lam" in obj)
      return {
        tag: "lam",
        idx,
        bi: obj.lam.binderInfo,
        name: asInt(obj.lam.name)!,
        type: asInt(obj.lam.type)!,
        body: asInt(obj.lam.body)!,
      };
    if ("forallE" in obj)
      return {
        tag: "forallE",
        idx,
        bi: obj.forallE.binderInfo,
        name: asInt(obj.forallE.name)!,
        type: asInt(obj.forallE.type)!,
        body: asInt(obj.forallE.body)!,
      };
    if ("letE" in obj)
      return {
        tag: "letE",
        idx,
        name: asInt(obj.letE.name)!,
        type: asInt(obj.letE.type)!,
        value: asInt(obj.letE.value)!,
        body: asInt(obj.letE.body)!,
      };
    if ("proj" in obj)
      return {
        tag: "proj",
        idx,
        typeName: asInt(obj.proj.typeName)!,
        pidx: asInt(obj.proj.idx)!,
        struct: asInt(obj.proj.struct)!,
      };
    return null;
  }

  // Top-level items
  if ("def" in obj) return { tag: "def", ...obj.def };
  if ("thm" in obj) return { tag: "thm", ...obj.thm };
  if ("axiom" in obj) return { tag: "axiom", ...obj.axiom };
  if ("opaque" in obj) return { tag: "opaque", ...obj.opaque };
  if ("quot" in obj) return { tag: "quot" };
  if ("inductive" in obj) {
    const i = obj.inductive;
    return {
      tag: "inductive",
      types: i.types ?? [],
      ctors: i.ctors ?? [],
      recs: i.recs ?? [],
    };
  }
  if ("meta" in obj) return { tag: "meta" };
  return null;
}

// =====================================================================
// 3. In-memory IR
// =====================================================================

type Name =
  | { kind: "anon" }
  | { kind: "str"; pre: Name; str: string }
  | { kind: "num"; pre: Name; i: number };
type Level =
  | { kind: "zero" }
  | { kind: "succ"; arg: Level }
  | { kind: "max"; l: Level; r: Level }
  | { kind: "imax"; l: Level; r: Level }
  | { kind: "param"; name: Name };
type Expr =
  | { kind: "bvar"; deBruijn: number }
  | { kind: "sort"; level: Level }
  | { kind: "const"; name: Name; us: Level[] }
  | { kind: "app"; fn: Expr; arg: Expr }
  | { kind: "lam"; name: Name; type: Expr; body: Expr }
  | { kind: "forallE"; name: Name; type: Expr; body: Expr }
  | { kind: "letE"; name: Name; type: Expr; value: Expr; body: Expr }
  | { kind: "proj"; typeName: Name; idx: number; struct: Expr }
  | { kind: "natLit"; value: string }
  | { kind: "strLit"; value: string };

type Decl =
  | { kind: "def"; name: Name; levelParams: Name[]; type: Expr; value: Expr }
  | { kind: "thm"; name: Name; levelParams: Name[]; type: Expr; value: Expr }
  | { kind: "axiom"; name: Name; levelParams: Name[]; type: Expr }
  | { kind: "opaque"; name: Name; levelParams: Name[]; type: Expr; value: Expr };

// =====================================================================
// 4. Index resolution: NDJSON refs -> IR objects
// =====================================================================

class Env {
  names: Map<number, Name> = new Map();
  levels: Map<number, Level> = new Map();
  exprs: Map<number, Expr> = new Map();

  constructor() {
    this.names.set(0, { kind: "anon" });
    this.levels.set(0, { kind: "zero" });
  }

  ingest(rec: Item): void {
    switch (rec.tag) {
      case "str":
        this.names.set(rec.idx, { kind: "str", pre: this.names.get(rec.pre)!, str: rec.str });
        break;
      case "num":
        this.names.set(rec.idx, { kind: "num", pre: this.names.get(rec.pre)!, i: rec.i });
        break;
      case "succ":
        this.levels.set(rec.idx, { kind: "succ", arg: this.levels.get(rec.arg)! });
        break;
      case "max":
        this.levels.set(rec.idx, {
          kind: "max",
          l: this.levels.get(rec.l)!,
          r: this.levels.get(rec.r)!,
        });
        break;
      case "imax":
        this.levels.set(rec.idx, {
          kind: "imax",
          l: this.levels.get(rec.l)!,
          r: this.levels.get(rec.r)!,
        });
        break;
      case "param":
        this.levels.set(rec.idx, { kind: "param", name: this.names.get(rec.name)! });
        break;
      case "bvar":
        this.exprs.set(rec.idx, { kind: "bvar", deBruijn: rec.deBruijn });
        break;
      case "sort":
        this.exprs.set(rec.idx, { kind: "sort", level: this.levels.get(rec.level)! });
        break;
      case "const":
        this.exprs.set(rec.idx, {
          kind: "const",
          name: this.names.get(rec.name)!,
          us: rec.us.map((i) => this.levels.get(i)!),
        });
        break;
      case "app":
        this.exprs.set(rec.idx, {
          kind: "app",
          fn: this.exprs.get(rec.fn)!,
          arg: this.exprs.get(rec.arg)!,
        });
        break;
      case "lam":
        this.exprs.set(rec.idx, {
          kind: "lam",
          name: this.names.get(rec.name)!,
          type: this.exprs.get(rec.type)!,
          body: this.exprs.get(rec.body)!,
        });
        break;
      case "forallE":
        this.exprs.set(rec.idx, {
          kind: "forallE",
          name: this.names.get(rec.name)!,
          type: this.exprs.get(rec.type)!,
          body: this.exprs.get(rec.body)!,
        });
        break;
      case "letE":
        this.exprs.set(rec.idx, {
          kind: "letE",
          name: this.names.get(rec.name)!,
          type: this.exprs.get(rec.type)!,
          value: this.exprs.get(rec.value)!,
          body: this.exprs.get(rec.body)!,
        });
        break;
      case "proj":
        this.exprs.set(rec.idx, {
          kind: "proj",
          typeName: this.names.get(rec.typeName)!,
          idx: rec.pidx,
          struct: this.exprs.get(rec.struct)!,
        });
        break;
    }
  }

  resolveDecl(rec: DefRec | ThmRec | AxRec | OpqRec): Decl {
    const name = this.names.get(rec.name)!;
    const levelParams = rec.levelParams.map((i) => this.names.get(i)!);
    const type = desugarLetE(this.exprs.get(rec.type)!);
    switch (rec.tag) {
      case "def":
        return {
          kind: "def",
          name,
          levelParams,
          type,
          value: desugarLetE(this.exprs.get(rec.value)!),
        };
      case "thm":
        return {
          kind: "thm",
          name,
          levelParams,
          type,
          value: desugarLetE(this.exprs.get(rec.value)!),
        };
      case "axiom":
        return { kind: "axiom", name, levelParams, type };
      case "opaque":
        return {
          kind: "opaque",
          name,
          levelParams,
          type,
          value: desugarLetE(this.exprs.get(rec.value)!),
        };
    }
  }
}

// Desugar letE to (λx:T, body) value.  Lean's `let` is definitionally
// equal to this β-redex (with extra inlining hints), and our β-machinery
// handles the conversion.  Applied to all expressions at decl-resolution
// time so downstream code (synth, whnf, lfExpr) never sees letE.
function desugarLetE(e: Expr): Expr {
  switch (e.kind) {
    case "letE":
      return {
        kind: "app",
        fn: {
          kind: "lam",
          name: e.name,
          type: desugarLetE(e.type),
          body: desugarLetE(e.body),
        },
        arg: desugarLetE(e.value),
      };
    case "lam":
    case "forallE":
      return { ...e, type: desugarLetE(e.type), body: desugarLetE(e.body) };
    case "app":
      return { kind: "app", fn: desugarLetE(e.fn), arg: desugarLetE(e.arg) };
    case "proj":
      return { ...e, struct: desugarLetE(e.struct) };
    case "bvar":
    case "sort":
    case "const":
    case "natLit":
    case "strLit":
      return e;
  }
}

// =====================================================================
// 5. Name mangling
// =====================================================================

function nameToString(n: Name): string {
  if (n.kind === "anon") return "";
  const prefix = nameToString(n.pre);
  const piece = n.kind === "str" ? n.str : String(n.i);
  return prefix === "" ? piece : `${prefix}.${piece}`;
}

function mangle(n: Name): string {
  // Replace dots and disallowed chars for use as Twelf identifiers.
  return nameToString(n).replace(/[^A-Za-z0-9_]/g, "_");
}

// =====================================================================
// 6. LF emission for levels and expressions
// =====================================================================

// Map from Lean level-param name to its LF binder name.  Populated by
// emitValDecl/emitAxiom while emitting a polymorphic declaration; empty
// otherwise.  Consulted by lfLevel for the `param` case and by freshVar
// to avoid collisions.
const levelParamBindings: Map<string, string> = new Map();

function lfLevel(l: Level): string {
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

// Sanitize a Lean level-param name into an LF identifier that won't
// collide with freshVar's letters (x/y/z/w).
function nameToLfLevelVar(n: Name): string {
  const raw = nameToString(n).replace(/[^A-Za-z0-9_]/g, "_");
  if (raw === "") return "lv_anon";
  if (/^[xyzw]/.test(raw)) return `lv_${raw}`;
  return raw;
}

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
  for (let i = 0; i < t.us.length; i++) {
    if (!levelEq(t.us[i], selfLevels[i])) return false;
  }
  return true;
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

// Emit a deliberate Twelf-side rejection when the translator detects an
// invalid input (duplicate name, etc.).  Uses %solve on the uninhabited
// `tcb-violation` type, which Twelf reports as ABORT.  Twelf otherwise
// silently allows shadowing constant declarations, so this is how we
// surface duplicates to the test harness.
let violationCounter = 0;
function emitDuplicateRejection(declName: string, newKind: string, oldKind: string): void {
  emit(`%% TRANSLATOR REJECT: duplicate declaration of "${declName}"`);
  emit(`%%   previously declared as kind=${oldKind}, now seen as kind=${newKind}`);
  emit(`%solve _violation_${violationCounter++} : tcb-violation.`);
  emitBlank();
  skips.push(`duplicate declaration: ${declName} (was ${oldKind}, now ${newKind})`);
}

function lfLvls(ls: Level[]): string {
  let acc = "lnil";
  for (let i = ls.length - 1; i >= 0; i--) acc = `(lcons ${lfLevel(ls[i])} ${acc})`;
  return acc;
}

// HOAS translation: bvar 0 inside a binder becomes the LF-level variable
// introduced at that binder.  `boundVars` is the LF-side variable name
// stack, innermost-first.
function lfExpr(e: Expr, boundVars: string[]): string {
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
      throw new Error("letE not yet supported");
    case "proj":
      throw new Error("proj not yet supported");
    case "natLit":
      throw new Error("natLit not yet supported");
    case "strLit":
      throw new Error("strLit not yet supported");
  }
}

function freshVar(scope: string[]): string {
  // Predictable names: x, y, z, w, x1, y1, ...  Scope must include
  // *every* bound name (vars and hyps both) — they live in the same
  // LF namespace and would shadow.  We also avoid level-param binder
  // names, which live in the same LF namespace.
  const levelNames = Array.from(levelParamBindings.values());
  const allScope = [...scope, ...levelNames];
  const letters = ["x", "y", "z", "w"];
  for (let suf = 0; suf < 1000; suf++) {
    for (const l of letters) {
      const v = suf === 0 ? l : `${l}${suf}`;
      if (!allScope.includes(v)) return v;
    }
  }
  throw new Error("ran out of fresh variable names");
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
  if (a.kind !== b.kind) return false;
  switch (a.kind) {
    case "bvar":
      return a.deBruijn === (b as any).deBruijn;
    case "sort":
      return levelEq(a.level, (b as any).level);
    case "const":
      return (
        nameEq(a.name, (b as any).name) &&
        a.us.length === (b as any).us.length &&
        a.us.every((u, i) => levelEq(u, (b as any).us[i]))
      );
    case "app":
      return exprEq(a.fn, (b as any).fn) && exprEq(a.arg, (b as any).arg);
    case "lam":
    case "forallE":
      return exprEq(a.type, (b as any).type) && exprEq(a.body, (b as any).body);
    case "letE":
      return (
        exprEq(a.type, (b as any).type) &&
        exprEq(a.value, (b as any).value) &&
        exprEq(a.body, (b as any).body)
      );
    case "proj":
      return (
        nameEq(a.typeName, (b as any).typeName) &&
        a.idx === (b as any).idx &&
        exprEq(a.struct, (b as any).struct)
      );
    case "natLit":
      return a.value === (b as any).value;
    case "strLit":
      return a.value === (b as any).value;
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
  if (a.kind !== b.kind) return false;
  switch (a.kind) {
    case "zero":
      return true;
    case "succ":
      return levelEq(a.arg, (b as any).arg);
    case "max":
    case "imax":
      return levelEq((a as any).l, (b as any).l) && levelEq((a as any).r, (b as any).r);
    case "param":
      return nameEq(a.name, (b as any).name);
  }
}
function nameEq(a: Name, b: Name): boolean {
  if (a.kind !== b.kind) return false;
  if (a.kind === "anon") return true;
  if (a.kind === "str") return a.str === (b as any).str && nameEq(a.pre, (b as any).pre);
  if (a.kind === "num") return a.i === (b as any).i && nameEq(a.pre, (b as any).pre);
  return false;
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
function parseLvlSyntax(s: string): Level {
  s = s.trim();
  if (s === "lzero") return { kind: "zero" };
  // Strip outer parens.
  if (s.startsWith("(") && s.endsWith(")")) {
    const inner = s.slice(1, -1);
    const parts = splitTopLevel(inner);
    if (parts[0] === "lsucc") return { kind: "succ", arg: parseLvlSyntax(parts[1]) };
    if (parts[0] === "lmax")
      return { kind: "max", l: parseLvlSyntax(parts[1]), r: parseLvlSyntax(parts[2]) };
    if (parts[0] === "limax")
      return { kind: "imax", l: parseLvlSyntax(parts[1]), r: parseLvlSyntax(parts[2]) };
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
      for (let i = 0; i < entry.levelParams.length; i++) {
        m.set(nameToString(entry.levelParams[i]), e.us[i]);
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
      throw new Error(`synth: case ${(e as any).kind} not yet supported`);
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
  if (major.kind !== "const") return null;
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
  const u: Level = head.us[0];

  const motive = args[0];
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
  for (let i = 0; i < k; i++) {
    const ci = info.allCtors[i];
    const expectedCaseTy: Expr = {
      kind: "app",
      fn: motive,
      arg: { kind: "const", name: ci.nameStruct, us: [] },
    };
    let caseS: Synth;
    try {
      caseS = synth(cases[i], scope);
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
    const ctorExpr: Expr = { kind: "const", name: info.allCtors[info.position].nameStruct, us: [] };
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

  return {
    result: cases[info.position],
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
      for (let i = 0; i < entry.levelParams.length; i++) {
        m.set(nameToString(entry.levelParams[i]), e.us[i]);
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
  } catch {}

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
    } catch {}
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
    if (proof === null) return null;
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
  if (segments.length === 1) return segments[0];
  return segments.slice(1).reduce((acc, p) => `(defeq/trans ${acc} ${p})`, segments[0]);
}

// =====================================================================
// 8. Top-level emission
// =====================================================================

const out: string[] = [];
const skips: string[] = [];

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
  const mn = mangle(d.name);
  const declName = nameToString(d.name);

  if (declTable.has(declName)) {
    emitDuplicateRejection(declName, kindTag, declTable.get(declName)!.kind);
    return;
  }

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

    let typeWf: Synth, valTy: Synth;
    try {
      typeWf = synth(d.type, { vars: [], hyps: [], tys: [] });
      valTy = synth(d.value, { vars: [], hyps: [], tys: [] });
    } catch (e: any) {
      skips.push(`${kindTag} ${declName}: synth failed (${e.message})`);
      emit(`%% SKIP: ${kindTag} ${declName} — synth failed: ${e.message}`);
      emitBlank();
      return;
    }

    const typeWfTyLF = lfExpr(typeWf.tyExpr, []);
    let valuePf: string = valTy.proof;
    if (!exprEq(valTy.tyExpr, d.type)) {
      const bridge = bridgeTypes(valTy.tyExpr, d.type, { vars: [], hyps: [], tys: [] });
      if (bridge !== null) {
        valuePf = `(defeq/conv ${bridge} ${valTy.proof})`;
      } else {
        emit(`%% TRANSLATOR: could not bridge inferred type to declared type`);
        emit(`%%   inferred type kind: ${valTy.tyExpr.kind}`);
        emit(`%%   declared type kind: ${d.type.kind}`);
        emit(`%%   emitting valTy.proof; Twelf will likely reject.`);
      }
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
      levelBinders.length > 0 && !allMentioned(levelBinders, T_lf, typeWf.proof, typeWfTyLF)
        ? "%abbrev "
        : "";
    const vt_decl =
      levelBinders.length > 0 && !allMentioned(levelBinders, V_lf, valuePf, T_lf) ? "%abbrev " : "";

    emit(`%% ${kindTag} ${declName}`);
    emit(`${tw_decl}${mn}/type-wf :`);
    emit(`   ${levelPrefix}defeq ${T_lf} ${T_lf} ${typeWfTyLF}`);
    emit(`   = ${bodyLambda}${typeWf.proof}.`);
    emitBlank();
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

    declTable.set(declName, {
      mangle: mn,
      levelParams: d.levelParams,
      type: d.type,
      kind: info.tableKind,
      value: d.value,
    });
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
  const mn = mangle(declName);
  const nameStr = nameToString(declName);

  if (declTable.has(nameStr)) {
    emitDuplicateRejection(nameStr, banner, declTable.get(nameStr)!.kind);
    return;
  }

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

    let typeWf: Synth;
    try {
      typeWf = synth(type, { vars: [], hyps: [], tys: [] });
    } catch (e: any) {
      skips.push(`${banner} ${nameStr}: type synth failed (${e.message})`);
      emit(`%% SKIP: ${banner} ${nameStr} — type synth failed: ${e.message}`);
      emitBlank();
      return;
    }

    const typeWfTyLF = lfExpr(typeWf.tyExpr, []);
    const levelPrefix =
      levelBinders.length === 0 ? "" : levelBinders.map((n) => `{${n} : lvl}`).join(" ") + " ";
    const bodyLambda = levelBinders.length === 0 ? "" : levelBinders.map((n) => `[${n}] `).join("");
    const levelArgList = levelBinders.length === 0 ? "" : " " + levelBinders.join(" ");
    const lvlsExpr =
      levelBinders.length === 0
        ? "lnil"
        : levelBinders.reduceRight((acc, n) => `(lcons ${n} ${acc})`, "lnil");

    const tw_decl =
      levelBinders.length > 0 && !allMentioned(levelBinders, T_lf, typeWf.proof, typeWfTyLF)
        ? "%abbrev "
        : "";

    emit(`%% ${banner} ${nameStr}`);
    emit(`${tw_decl}${mn}/type-wf :`);
    emit(`   ${levelPrefix}defeq ${T_lf} ${T_lf} ${typeWfTyLF}`);
    emit(`   = ${bodyLambda}${typeWf.proof}.`);
    emitBlank();
    const tw_inst = levelBinders.length === 0 ? `${mn}/type-wf` : `(${mn}/type-wf${levelArgList})`;

    // Inductive type formers also need a structural `ends-in-sort` proof:
    // the kernel demands the signature to be `Π ... → Sort _`, not an
    // arbitrary well-typed term.  If we can't build the proof, the type
    // isn't a forall-chain-to-sort and the translator rejects.
    let okArgs = tw_inst;
    if (tableKind === "indt") {
      const eis = endsInSortProof(type, []);
      if (eis === null) {
        emit(
          `%% TRANSLATOR REJECT: inductive ${nameStr} — type signature is not a forall-chain ending in a sort literal`,
        );
        emit(`%solve _violation_${violationCounter++} : tcb-violation.`);
        emitBlank();
        skips.push(`inductive ${nameStr}: type signature is not Π…→Sort_`);
        return;
      }
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
    if (tableKind === "ctor" && positivityInfo) {
      const cs = buildCtorSpine(type, positivityInfo.selfName, positivityInfo.selfLevels, []);
      if (cs === null) {
        emit(
          `%% TRANSLATOR REJECT: ctor ${nameStr} — type is not strictly positive in ${positivityInfo.selfName} (or uses unsupported expr form)`,
        );
        emit(`%solve _violation_${violationCounter++} : tcb-violation.`);
        emitBlank();
        skips.push(`ctor ${nameStr}: strict positivity not witnessable`);
        return;
      }
      const hoasBody = lfExprHoasSelf(
        type,
        positivityInfo.selfName,
        positivityInfo.selfLevels,
        [],
        "S",
      );
      const indLvlsLF = lfLvls(positivityInfo.selfLevels);
      const positivityProof = `(ctor-positive/intro ([S] ${hoasBody}) ${cs})`;
      // Same strict-occurrence concern as /type-wf and /ends-in-sort:
      // if no level binder appears in T_lf or the proof, %abbrev.
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
      const cp_inst =
        levelBinders.length === 0 ? `${mn}/positivity` : `(${mn}/positivity${levelArgList})`;
      okArgs = `${tw_inst} ${cp_inst}`;
    }

    emit(`${mn}/decl : ${levelPrefix}declared "${nameStr}" ${lvlsExpr}`);
    emit(`   ${T_lf}`);
    emit(`   ${dkindCtor}`);
    emit(`   (${okCtor} ${okArgs}).`);
    emitBlank();

    declTable.set(nameStr, {
      mangle: mn,
      levelParams,
      type,
      kind: tableKind,
    });
  } finally {
    cleanup();
  }
}

function emitAxiom(d: Decl & { kind: "axiom" }): void {
  emitStructuralDecl(d.name, d.levelParams, d.type, "ax", "dkind-ok/ax", "ax", "axiom");
}

function emitInductive(ir: IndRec, env: Env): void {
  // Helper: look up a name/expr from Env by index.
  const N = (i: number): Name => env.names.get(i)!;
  const E = (i: number): Expr => desugarLetE(env.exprs.get(i)!);
  // 1. Type formers.
  for (const t of ir.types) {
    emitStructuralDecl(
      N(t.name),
      t.levelParams.map(N),
      E(t.type),
      "indt",
      "dkind-ok/indt",
      "indt",
      "inductive",
    );
  }
  // 2. Constructors.  Each ctor's positivity check needs to know
  //    its parent inductive's name and level instantiation.
  //    `c.induct` is the name-index of the inductive; we cross-
  //    reference ir.types to find the corresponding level params,
  //    then build a Level[] (each as a param-Level) for the LF
  //    `lcons u1 (... lnil)` rendering.
  for (const c of ir.ctors) {
    const indTypeSpec = ir.types.find((t) => t.name === c.induct);
    if (!indTypeSpec) {
      // Should not happen for well-formed lean4export output.
      emit(
        `%% TRANSLATOR REJECT: ctor ${nameToString(N(c.name))} — induct field doesn't match any type in this inductive block`,
      );
      emit(`%solve _violation_${violationCounter++} : tcb-violation.`);
      emitBlank();
      skips.push(`ctor ${nameToString(N(c.name))}: induct pointer invalid`);
      continue;
    }
    const selfName = nameToString(N(c.induct));
    const selfLevels: Level[] = c.levelParams.map((idx) => ({
      kind: "param" as const,
      name: N(idx),
    }));
    emitStructuralDecl(
      N(c.name),
      c.levelParams.map(N),
      E(c.type),
      "ctor",
      "dkind-ok/ctor",
      "ctor",
      "inductive ctor",
      { selfName, selfLevels },
    );
  }
  // 3. Recursors.
  for (const r of ir.recs) {
    emitStructuralDecl(
      N(r.name),
      r.levelParams.map(N),
      E(r.type),
      "irec",
      "dkind-ok/irec",
      "irec",
      "inductive recursor",
    );
  }
  // 4. Stage-1 iota helpers (if this inductive qualifies as a stage-1 enum).
  emitStage1EnumIotaHelpers(ir, env);
}

// Emit `<Foo>/as-enum` and per-ctor `<Foo_ctor>/iota` definitions if this
// inductive qualifies as a stage-1 enum (no level params, 0-3 ctors all
// with zero fields, single non-mutual recursor).  These are *definitions*
// (= proof terms) inhabiting closed-family judgments (`enum-rec-type`,
// `defeq`); they don't extend any open family, so the soundness story is
// unchanged.  Downstream consumers (translator-emitted defeq proofs that
// want to compute iota, or hand-written witnesses) can invoke them.
function emitStage1EnumIotaHelpers(ir: IndRec, env: Env): void {
  // Single-type, single-recursor blocks only (no mutual/nested for stage 1).
  if (ir.types.length !== 1) return;
  if (ir.recs.length !== 1) return;
  const indSpec = ir.types[0];
  const recSpec = ir.recs[0];
  // No level params on the inductive itself.
  if (indSpec.levelParams.length !== 0) return;
  // Ctors for this inductive, sorted by cidx.
  const ctorList = ir.ctors
    .filter((c) => c.induct === indSpec.name)
    .sort((a, b) => a.cidx - b.cidx);
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

  const N = (i: number): Name => env.names.get(i)!;
  const indName = nameToString(N(indSpec.name));
  const indMangle = mangle(N(indSpec.name));
  const recName = nameToString(N(recSpec.name));
  const recMangle = mangle(N(recSpec.name));
  const ctorInfo = ctorList.map((c) => ({
    name: nameToString(N(c.name)),
    nameStruct: N(c.name),
    mangle: mangle(N(c.name)),
  }));
  const k = ctorInfo.length;
  const u = "u";

  // Register each ctor in iotaTable so reduceOnce can invoke the helper.
  const allCtors = ctorInfo.map((c) => ({ name: c.name, nameStruct: c.nameStruct }));
  for (let i = 0; i < k; i++) {
    iotaTable.set(ctorInfo[i].name, {
      recName,
      indName: N(indSpec.name),
      indNameStr: indName,
      ctorMangle: ctorInfo[i].mangle,
      position: i,
      allCtors,
    });
  }

  // Build the full recursor-type expression to assert via enum-rec-type.
  const indConst = `(econst "${indName}" lnil)`;
  const motiveType = `(eforall ${indConst} ([x] (esort ${u})))`;
  const resultPart = `(eforall ${indConst} ([t] (eapp M t)))`;
  let bodyM = resultPart;
  for (let i = k - 1; i >= 0; i--) {
    bodyM = `(eforall (eapp M (econst "${ctorInfo[i].name}" lnil)) ([x] ${bodyM}))`;
  }
  const fullRecType = `(eforall ${motiveType} ([M] ${bodyM}))`;

  let cnamesExpr = "cnil";
  for (let i = k - 1; i >= 0; i--) {
    cnamesExpr = `(ccons "${ctorInfo[i].name}" ${cnamesExpr})`;
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
  for (let i = 0; i < k; i++) {
    const c = ctorInfo[i];
    const ruleName = k === 1 ? "defeq/iota-enum-1" : `defeq/iota-enum-${k}-${positions[i]}`;

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
    for (let j = 0; j < k; j++) {
      premiseLines.push(
        `   -> defeq Mp${j + 1} Mp${j + 1} (eapp M (econst "${ctorInfo[j].name}" lnil))`,
      );
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
// 9. Main
// =====================================================================

async function main(): Promise<void> {
  const env = new Env();
  const rl = readline.createInterface({ input: process.stdin });

  for await (const raw of rl) {
    const line = raw.trim();
    if (line === "") continue;
    const rec = parseLine(line);
    if (rec === null) {
      emit(`%% UNPARSED: ${line.slice(0, 80)}`);
      continue;
    }
    env.ingest(rec);
    try {
      if (rec.tag === "def") emitValDecl(env.resolveDecl(rec) as Decl & { kind: "def" });
      else if (rec.tag === "thm") emitValDecl(env.resolveDecl(rec) as Decl & { kind: "thm" });
      else if (rec.tag === "opaque") emitValDecl(env.resolveDecl(rec) as Decl & { kind: "opaque" });
      else if (rec.tag === "axiom") emitAxiom(env.resolveDecl(rec) as Decl & { kind: "axiom" });
      else if (rec.tag === "quot") emit(`%% SKIP: quot not yet supported`);
      else if (rec.tag === "inductive") emitInductive(rec, env);
    } catch (e: any) {
      const tag = (rec as any).tag ?? "decl";
      skips.push(`${tag}: untranslatable (${e.message})`);
      emit(`%% SKIP: ${tag} — untranslatable: ${e.message}`);
      emitBlank();
    }
  }

  // Functional-dependency seal.
  //
  // For monomorphic decls, this catches duplicate names (LS=lnil twice
  // with different T or DK).  For polymorphic decls, LS varies per
  // instantiation, so we make it an input position too: given (N, LS),
  // T/DK are uniquely determined.  Duplicate poly declarations would
  // collide on the LF identifier `<mangle>/decl` independently.
  emit(`%mode declared +N +LS -T -DK -W.`);
  emit(`%worlds () (declared _ _ _ _ _).`);
  emit(`%unique declared +N +LS -1T -1DK *W.`);

  if (skips.length > 0) {
    emit(``);
    emit(`%% Translator summary:`);
    for (const s of skips) emit(`%%   - ${s}`);
  }

  process.stdout.write(out.join("\n") + "\n");
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
