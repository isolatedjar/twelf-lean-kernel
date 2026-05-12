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
      return `(econst ${mangle(e.name)} ${lfLvls(e.us)})`;
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

// --- Level equality / reduction utilities -----------------------------

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

// Try to find a proof of (lvl-eq from to) by reducing `from` step-by-step.
// Returns null if we can't get there (e.g. `from` reduces to canonical form
// that's not syntactically equal to `to`).  TODO: also try reducing `to`
// and combining with lvl-eq/symm; for now, this top-level forward search
// covers the cases up through example 7 or so.
function solveLvlEq(from: Level, to: Level): string | null {
  let cur = from;
  const steps: string[] = [];
  // bounded loop to prevent runaways
  for (let i = 0; i < 16; i++) {
    if (levelEq(cur, to)) {
      if (steps.length === 0) return "lvl-eq/refl";
      let out = steps[0];
      for (let j = 1; j < steps.length; j++) out = `(lvl-eq/trans ${out} ${steps[j]})`;
      return out;
    }
    const r = reduceLevel(cur);
    if (r === null) return null;
    steps.push(r.proof);
    cur = r.result;
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
// For each Expr we produce (T_lf, proof_lf) where:
//   - T_lf is the LF expression for the synthesized type
//   - proof_lf is a term of type `defeq <lfExpr e> <lfExpr e> T_lf`
//
// boundVars: LF-side names of binders, innermost-first.
// boundHyps: corresponding names of the LF hypothesis `defeq x x A`
//            for each binder.
//
// The MVP doesn't synthesize through `const` references or `app` — it
// only handles `sort`, `lam`, `forallE` (the closed core of 001-005).
// Anything else throws and the declaration gets skipped.

type Synth = { ty: string; proof: string };

function synth(e: Expr, scope: { vars: string[]; hyps: string[]; tys: string[] }): Synth {
  switch (e.kind) {
    case "bvar": {
      const v = scope.vars[e.deBruijn];
      const h = scope.hyps[e.deBruijn];
      const t = scope.tys[e.deBruijn];
      if (v === undefined || h === undefined || t === undefined) {
        throw new Error(`bvar ${e.deBruijn} out of scope in synth`);
      }
      return { ty: t, proof: h };
    }
    case "sort": {
      const l = lfLevel(e.level);
      return { ty: `(esort (lsucc ${l}))`, proof: `defeq/sort-refl` };
    }
    case "forallE": {
      const aSynth = synth(e.type, scope);
      // aSynth.ty should be `(esort _)`; we extract U.
      // Build the inner premise as an LF lambda: ({x} defeq x x A -> defeq (body x) (body x) (esort V)).
      const allBound = [...scope.vars, ...scope.hyps];
      const v = freshVar(allBound);
      const h = freshVar([...allBound, v]);
      const innerScope = {
        vars: [v, ...scope.vars],
        hyps: [h, ...scope.hyps],
        tys: [lfExpr(e.type, scope.vars), ...scope.tys],
      };
      const bodySynth = synth(e.body, innerScope);
      // The body's type must be (esort _).
      // The whole forall has type (esort (limax U V)).
      // We trust the inferred bodyTy / aSynth.ty are (esort ...).
      return {
        ty: `(esort (limax ${stripSuccSort(aSynth.ty)} ${stripSuccSort(bodySynth.ty)}))`,
        proof: `(defeq/forall ${aSynth.proof} ([${v}] [${h}] ${bodySynth.proof}))`,
      };
    }
    case "lam": {
      const aSynth = synth(e.type, scope);
      const allBound = [...scope.vars, ...scope.hyps];
      const v = freshVar(allBound);
      const h = freshVar([...allBound, v]);
      const innerScope = {
        vars: [v, ...scope.vars],
        hyps: [h, ...scope.hyps],
        tys: [lfExpr(e.type, scope.vars), ...scope.tys],
      };
      const bodySynth = synth(e.body, innerScope);
      // bodySynth.ty is parameterized on v but we emit it as a closure;
      // for the result `(eforall A ([v] T_body))` we need T_body to be
      // syntactically free in v but allowed to reference v.
      // In LF, the LF lambda below scopes v correctly.
      return {
        ty: `(eforall ${lfExpr(e.type, scope.vars)} ([${v}] ${bodySynth.ty}))`,
        proof: `(defeq/lam ${aSynth.proof} ([${v}] [${h}] ${bodySynth.proof}))`,
      };
    }
    default:
      throw new Error(`synth: case ${(e as any).kind} not yet supported`);
  }
}

// Given "(esort (lsucc L))" or similar, extract the inner level.
// We use this to compute imax(U, V) for the forall result type.
function stripSuccSort(esortTy: string): string {
  // We don't actually evaluate; we keep things symbolic.
  // esortTy is "(esort SOMETHING)". Return SOMETHING.
  const m = esortTy.match(/^\(esort (.+)\)$/);
  if (!m) throw new Error(`expected (esort ...), got ${esortTy}`);
  return m[1];
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

  // Value-typing.  Twelf identifies α-equivalent LF terms automatically,
  // so we only need to *manually* construct a defeq/conv when the
  // top-level shape differs in a way Twelf can't reconcile — currently
  // just the sort-level case `(esort L)` vs `(esort L')` with L ≠ L'.
  // Otherwise we hand valTy.proof off at the declared type and trust
  // Twelf to accept-or-reject.

  let valuePf: string = valTy.proof;
  const inferredSort = valTy.ty.match(/^\(esort (.+)\)$/);
  const declaredSort = T_lf.match(/^\(esort (.+)\)$/);
  if (inferredSort && declaredSort && inferredSort[1] !== declaredSort[1]) {
    let parsed: { from: Level; to: Level } | null = null;
    try {
      parsed = { from: parseLvlSyntax(inferredSort[1]), to: parseLvlSyntax(declaredSort[1]) };
    } catch {
      emit(`%% TRANSLATOR: could not parse level syntax; emitting raw proof, Twelf will judge`);
    }
    if (parsed !== null) {
      const lvlEqProof = solveLvlEq(parsed.from, parsed.to);
      if (lvlEqProof !== null) {
        valuePf = `(defeq/conv (defeq/sort-eq ${lvlEqProof}) ${valTy.proof})`;
      } else {
        emit(`%% TRANSLATOR: could not construct lvl-eq ${inferredSort[1]} ≈ ${declaredSort[1]}`);
        emit(`%%   emitting value-typed at declared type; Twelf will reject if mismatch is real.`);
      }
    }
  }

  // Emit.
  emit(`%% def ${declName}`);
  emit(`${mn} : name.`);
  emitBlank();
  emit(`${mn}/type-wf :`);
  emit(`   defeq ${T_lf} ${T_lf} ${typeWf.ty}`);
  emit(`   = ${typeWf.proof}.`);
  emitBlank();
  emit(`${mn}/value-typed :`);
  emit(`   defeq ${V_lf} ${V_lf} ${T_lf}`);
  emit(`   = ${valuePf}.`);
  emitBlank();
  emit(`${mn}/decl : declared ${mn} lnil`);
  emit(`   ${T_lf}`);
  emit(`   (defn ${V_lf})`);
  emit(`   (dkind-ok/defn ${mn}/type-wf ${mn}/value-typed).`);
  emitBlank();
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
