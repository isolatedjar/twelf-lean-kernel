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
type IndRec = { tag: "inductive"; raw: any }; // not yet handled
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
  if ("inductive" in obj) return { tag: "inductive", raw: obj.inductive };
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
    const type = this.exprs.get(rec.type)!;
    switch (rec.tag) {
      case "def":
        return { kind: "def", name, levelParams, type, value: this.exprs.get(rec.value)! };
      case "thm":
        return { kind: "thm", name, levelParams, type, value: this.exprs.get(rec.value)! };
      case "axiom":
        return { kind: "axiom", name, levelParams, type };
      case "opaque":
        return { kind: "opaque", name, levelParams, type, value: this.exprs.get(rec.value)! };
    }
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
    case "param":
      throw new Error(`level param not yet supported: ${nameToString(l.name)}`);
  }
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
  // LF namespace and would shadow.
  const letters = ["x", "y", "z", "w"];
  for (let suf = 0; suf < 1000; suf++) {
    for (const l of letters) {
      const v = suf === 0 ? l : `${l}${suf}`;
      if (!scope.includes(v)) return v;
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

// --- Decl table (populated as we walk NDJSON) ------------------------

interface DeclEntry {
  mangle: string;
  type: Expr;
  kind: "defn" | "thm" | "opq" | "ax";
  value?: Expr;
}
const declTable: Map<string, DeclEntry> = new Map();

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
  if (l.kind === "max" && levelEq(l.l, l.r)) {
    return { result: l.l, proof: "lvl-eq/max-idem" };
  }
  return null;
}

// Try to find a proof of (lvl-eq from to).  Strategy:
//   1. If syntactically equal, lvl-eq/refl.
//   2. Try a top-level reduction of `from` and recurse.
//   3. Try a top-level reduction of `to` and recurse (with symm).
//   4. If `from` and `to` share an outer constructor, try the congruence
//      rules on the sub-levels.
//
// `depth` guards against pathological recursion.
function solveLvlEq(from: Level, to: Level, depth: number = 0): string | null {
  if (depth > 8) return null;
  if (levelEq(from, to)) return "lvl-eq/refl";

  // (2) reduce `from`.
  const r = reduceLevel(from);
  if (r !== null) {
    const rest = solveLvlEq(r.result, to, depth + 1);
    if (rest !== null) return `(lvl-eq/trans ${r.proof} ${rest})`;
  }
  // (3) reduce `to`.
  const r2 = reduceLevel(to);
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
        proof: "defeq/sort-refl",
      };
    case "const": {
      const entry = declTable.get(nameToString(e.name));
      if (entry === undefined) {
        throw new Error(`const "${nameToString(e.name)}" not in decl table`);
      }
      if (e.us.length !== 0) {
        throw new Error(
          `universe polymorphism not yet supported (const "${nameToString(e.name)}" has ${e.us.length} level args)`,
        );
      }
      return {
        tyExpr: entry.type,
        proof: `(defeq/const ${entry.mangle}/decl)`,
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

      // Argument-type check: try syntactic equality first, then sort-level
      // conversion if both are sorts.  TODO: full whnf-based conversion.
      let aProof = aSynth.proof;
      if (!exprEq(aSynth.tyExpr, A_expected)) {
        if (aSynth.tyExpr.kind === "sort" && A_expected.kind === "sort") {
          const lvlEqProof = solveLvlEq(aSynth.tyExpr.level, A_expected.level);
          if (lvlEqProof === null) {
            throw new Error(
              `app: cannot bridge arg sort ${JSON.stringify(aSynth.tyExpr.level)} to ${JSON.stringify(A_expected.level)}`,
            );
          }
          aProof = `(defeq/conv (defeq/sort-eq ${lvlEqProof}) ${aSynth.proof})`;
        } else {
          throw new Error(`app: argument type mismatch (non-sort conversion not yet implemented)`);
        }
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
      e.us.length === 0
    ) {
      return {
        result: entry.value,
        proof: `(defeq/delta ${entry.mangle}/decl)`,
      };
    }
    return null;
  }

  // app: β if f is a lam; otherwise lift a reduction step from f.
  if (e.kind === "app") {
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
    if (fReduced === null) return null;

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

function emitDef(d: Decl & { kind: "def" }): void {
  if (d.levelParams.length !== 0) {
    skips.push(`def ${nameToString(d.name)}: universe polymorphism not yet supported`);
    emit(
      `%% SKIP: def ${nameToString(d.name)} — universe-polymorphic (${d.levelParams.length} params)`,
    );
    emitBlank();
    return;
  }

  const mn = mangle(d.name);
  const declName = nameToString(d.name);
  const T_lf = (() => {
    try {
      return lfExpr(d.type, []);
    } catch (e: any) {
      return null;
    }
  })();
  const V_lf = (() => {
    try {
      return lfExpr(d.value, []);
    } catch (e: any) {
      return null;
    }
  })();
  if (T_lf === null || V_lf === null) {
    skips.push(`def ${declName}: untranslatable expression`);
    emit(`%% SKIP: def ${declName} — could not translate type/value to LF`);
    emitBlank();
    return;
  }

  let typeWf: Synth;
  let valTy: Synth;
  try {
    typeWf = synth(d.type, { vars: [], hyps: [], tys: [] });
    valTy = synth(d.value, { vars: [], hyps: [], tys: [] });
  } catch (e: any) {
    skips.push(`def ${declName}: synth failed (${e.message})`);
    emit(`%% SKIP: def ${declName} — synth failed: ${e.message}`);
    emitBlank();
    return;
  }

  // Render the synthesized type-of-type at the top-level scope (no
  // outer LF bindings) for use in the type-wf annotation.
  const typeWfTyLF = lfExpr(typeWf.tyExpr, []);

  // Value-typing conversion.  When the synthesized type doesn't match
  // the declared type, ask bridgeTypes for a `defeq valTy.tyExpr d.type
  // (esort _)` proof and wrap with defeq/conv.
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

  // Emit.
  emit(`%% def ${declName}`);
  emit(`${mn}/type-wf :`);
  emit(`   defeq ${T_lf} ${T_lf} ${typeWfTyLF}`);
  emit(`   = ${typeWf.proof}.`);
  emitBlank();
  emit(`${mn}/value-typed :`);
  emit(`   defeq ${V_lf} ${V_lf} ${T_lf}`);
  emit(`   = ${valuePf}.`);
  emitBlank();
  emit(`${mn}/decl : declared "${declName}" lnil`);
  emit(`   ${T_lf}`);
  emit(`   (defn ${V_lf})`);
  emit(`   (dkind-ok/defn ${mn}/type-wf ${mn}/value-typed).`);
  emitBlank();

  // Record in decl table so later const references can look it up.
  declTable.set(declName, {
    mangle: mn,
    type: d.type,
    kind: "defn",
    value: d.value,
  });
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
    if (rec.tag === "def") emitDef(env.resolveDecl(rec) as any);
    else if (rec.tag === "thm") emit(`%% SKIP: thm not yet supported`);
    else if (rec.tag === "axiom") emit(`%% SKIP: axiom not yet supported`);
    else if (rec.tag === "opaque") emit(`%% SKIP: opaque not yet supported`);
    else if (rec.tag === "quot") emit(`%% SKIP: quot not yet supported`);
    else if (rec.tag === "inductive") emit(`%% SKIP: inductive not yet supported`);
  }

  // Functional-dependency seal.
  emit(`%mode declared +N -LS -T -DK -W.`);
  emit(`%worlds () (declared _ _ _ _ _).`);
  emit(`%unique declared +N -1LS -1T -1DK *W.`);

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
