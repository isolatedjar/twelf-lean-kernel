#!/usr/bin/env -S node --experimental-strip-types
// parse.ts — read lean4export's NDJSON on stdin, write a resolved
// declaration array as JSON on stdout.
//
// The output is essentially the same information as the NDJSON, but
// with every cross-reference resolved by value rather than by index.
// This makes the parsed declarations directly readable by humans;
// lean2lf.ts consumes it as a precondition without re-validating.
//
// If runtime defensiveness is wanted later, the parseLine + Env step
// can be replaced with a z.discriminatedUnion + z.parse pair.

import * as readline from "node:readline";

import { format, resolveConfig } from "prettier";

import type {
  BinderInfo,
  Decl,
  Expr,
  IndCtor,
  IndRecursor,
  IndType,
  Inductive,
  Level,
  Name,
  ParsedEnv,
} from "./shared.ts";
import { transformNamesToJSON } from "./shared.ts";

// =====================================================================
// NDJSON wire format (internal to parse.ts)
// =====================================================================

type NameRec =
  | { tag: "str"; idx: number; pre: number; str: string }
  | { tag: "num"; idx: number; pre: number; i: number };

type LevelRec =
  | { tag: "succ"; idx: number; arg: number }
  | { tag: "max"; idx: number; l: number; r: number }
  | { tag: "imax"; idx: number; l: number; r: number }
  | { tag: "param"; idx: number; name: number };

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

// Decl-bearing records reference numeric indices into the name/expr tables.
type DefRec = { tag: "def"; name: number; levelParams: number[]; type: number; value: number };
type ThmRec = { tag: "thm"; name: number; levelParams: number[]; type: number; value: number };
type AxRec = { tag: "axiom"; name: number; levelParams: number[]; type: number };
type OpqRec = { tag: "opaque"; name: number; levelParams: number[]; type: number; value: number };
type QuotRec = {
  tag: "quot";
  quotKind: "type" | "ctor" | "lift" | "ind";
  name: number;
  levelParams: number[];
  type: number;
};

// `recs` is the NDJSON field name; we resolve it into `recursors`
// (matching shared.ts) at decl-resolution time.
type IndTypeSpec = {
  name: number;
  levelParams: number[];
  numParams: number;
  numIndices: number;
  type: number;
};
type IndCtorSpec = {
  name: number;
  levelParams: number[];
  type: number;
  numParams: number;
  numFields: number;
  induct: number;
  cidx?: number;
};
type IndRecRuleSpec = { ctor: number; nfields: number; rhs: number };
type IndRecSpec = {
  name: number;
  levelParams: number[];
  type: number;
  numParams: number;
  numIndices: number;
  numMotives: number;
  numMinors: number;
  rules: IndRecRuleSpec[];
  k: boolean;
};

type IndRec = {
  tag: "inductive";
  types: IndTypeSpec[];
  ctors: IndCtorSpec[];
  recs: IndRecSpec[];
};

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
// NDJSON line parsing.  Hand-rolled discrimination over field names.
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

function sub(obj: Record<string, unknown>, key: string): Record<string, unknown> | null {
  const v = obj[key];
  return typeof v === "object" && v !== null && !Array.isArray(v)
    ? (v as Record<string, unknown>)
    : null;
}

function parseLine(line: string): Item | null {
  let raw: unknown;
  try {
    raw = JSON.parse(line);
  } catch {
    return null;
  }
  if (typeof raw !== "object" || raw === null) return null;
  const obj = raw as Record<string, unknown>;

  // Names: { in: idx, str: { pre, str } } or { in: idx, num: { pre, i } }
  if ("in" in obj && "str" in obj) {
    const str = sub(obj, "str");
    if (!str) return null;
    return { tag: "str", idx: asInt(obj["in"])!, pre: asInt(str["pre"])!, str: asStr(str["str"])! };
  }
  if ("in" in obj && "num" in obj) {
    const num = sub(obj, "num");
    if (!num) return null;
    return { tag: "num", idx: asInt(obj["in"])!, pre: asInt(num["pre"])!, i: asInt(num["i"])! };
  }

  // Levels: { il: idx, <variant>: ... }
  if ("il" in obj && "succ" in obj)
    return { tag: "succ", idx: asInt(obj["il"])!, arg: asInt(obj["succ"])! };
  if ("il" in obj && "max" in obj) {
    const max = asArrayOfInts(obj["max"]);
    if (!max || max[0] === undefined || max[1] === undefined) return null;
    return { tag: "max", idx: asInt(obj["il"])!, l: max[0], r: max[1] };
  }
  if ("il" in obj && "imax" in obj) {
    const imax = asArrayOfInts(obj["imax"]);
    if (!imax || imax[0] === undefined || imax[1] === undefined) return null;
    return { tag: "imax", idx: asInt(obj["il"])!, l: imax[0], r: imax[1] };
  }
  if ("il" in obj && "param" in obj)
    return { tag: "param", idx: asInt(obj["il"])!, name: asInt(obj["param"])! };

  // Expressions: { ie: idx, <variant>: ... }
  if ("ie" in obj) {
    const idx = asInt(obj["ie"])!;
    if ("bvar" in obj) return { tag: "bvar", idx, deBruijn: asInt(obj["bvar"])! };
    if ("sort" in obj) return { tag: "sort", idx, level: asInt(obj["sort"])! };
    if ("const" in obj) {
      const c = sub(obj, "const");
      if (!c) return null;
      return { tag: "const", idx, name: asInt(c["name"])!, us: asArrayOfInts(c["us"])! };
    }
    if ("app" in obj) {
      const app = sub(obj, "app");
      if (!app) return null;
      return { tag: "app", idx, fn: asInt(app["fn"])!, arg: asInt(app["arg"])! };
    }
    if ("lam" in obj) {
      const lam = sub(obj, "lam");
      if (!lam) return null;
      return {
        tag: "lam",
        idx,
        bi: lam["binderInfo"] as BinderInfo,
        name: asInt(lam["name"])!,
        type: asInt(lam["type"])!,
        body: asInt(lam["body"])!,
      };
    }
    if ("forallE" in obj) {
      const forallE = sub(obj, "forallE");
      if (!forallE) return null;
      return {
        tag: "forallE",
        idx,
        bi: forallE["binderInfo"] as BinderInfo,
        name: asInt(forallE["name"])!,
        type: asInt(forallE["type"])!,
        body: asInt(forallE["body"])!,
      };
    }
    if ("letE" in obj) {
      const letE = sub(obj, "letE");
      if (!letE) return null;
      return {
        tag: "letE",
        idx,
        name: asInt(letE["name"])!,
        type: asInt(letE["type"])!,
        value: asInt(letE["value"])!,
        body: asInt(letE["body"])!,
      };
    }
    if ("proj" in obj) {
      const proj = sub(obj, "proj");
      if (!proj) return null;
      return {
        tag: "proj",
        idx,
        typeName: asInt(proj["typeName"])!,
        pidx: asInt(proj["idx"])!,
        struct: asInt(proj["struct"])!,
      };
    }
    if ("natVal" in obj) return { tag: "natLit", idx, value: asStr(obj["natVal"])! };
    if ("strVal" in obj) return { tag: "strLit", idx, value: asStr(obj["strVal"])! };
    return null;
  }

  // Top-level items
  if ("def" in obj) return { tag: "def", ...(sub(obj, "def") ?? {}) } as unknown as DefRec;
  if ("thm" in obj) return { tag: "thm", ...(sub(obj, "thm") ?? {}) } as unknown as ThmRec;
  if ("axiom" in obj) return { tag: "axiom", ...(sub(obj, "axiom") ?? {}) } as unknown as AxRec;
  if ("opaque" in obj) return { tag: "opaque", ...(sub(obj, "opaque") ?? {}) } as unknown as OpqRec;
  if ("quot" in obj) {
    const q = sub(obj, "quot");
    if (!q) return null;
    return {
      tag: "quot",
      quotKind: q["kind"] as "type" | "ctor" | "lift" | "ind",
      name: asInt(q["name"])!,
      levelParams: asArrayOfInts(q["levelParams"]) ?? [],
      type: asInt(q["type"])!,
    };
  }
  if ("inductive" in obj) {
    const ind = sub(obj, "inductive") ?? {};
    return {
      tag: "inductive",
      types: (ind["types"] ?? []) as IndTypeSpec[],
      ctors: (ind["ctors"] ?? []) as IndCtorSpec[],
      recs: (ind["recs"] ?? []) as IndRecSpec[],
    };
  }
  if ("meta" in obj) return { tag: "meta" };
  return null;
}

// =====================================================================
// Index → IR resolution.
//
// As NDJSON Items stream in, the Env builds maps from index to
// resolved Name/Level/Expr.  Decl-bearing items don't carry indices;
// they reference the name/expr tables, so we resolve them on-demand.
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
      case "natLit":
        this.exprs.set(rec.idx, { kind: "natLit", value: rec.value });
        break;
      case "strLit":
        this.exprs.set(rec.idx, { kind: "strLit", value: rec.value });
        break;
    }
  }

  // Decl-bearing record → resolved Decl.  letE is desugared at this
  // point so downstream stages never see it.
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

  resolveQuot(rec: QuotRec): Decl {
    return {
      kind: "quot",
      quotKind: rec.quotKind,
      name: this.names.get(rec.name)!,
      levelParams: rec.levelParams.map((i) => this.names.get(i)!),
      type: desugarLetE(this.exprs.get(rec.type)!),
    };
  }

  resolveInductive(rec: IndRec): Inductive {
    const types: IndType[] = rec.types.map((t) => ({
      name: this.names.get(t.name)!,
      levelParams: t.levelParams.map((i) => this.names.get(i)!),
      type: desugarLetE(this.exprs.get(t.type)!),
      numParams: t.numParams,
      numIndices: t.numIndices,
    }));
    // Ctors in the same inductive block come with a `cidx` declaration
    // index; we sort by it so lean2lf.ts can iterate in canonical order
    // (and stage-1 enum iota helpers match the recursor's minor order).
    const sortedCtors = rec.ctors.slice().sort((a, b) => (a.cidx ?? 0) - (b.cidx ?? 0));
    const ctors: IndCtor[] = sortedCtors.map((c) => ({
      name: this.names.get(c.name)!,
      levelParams: c.levelParams.map((i) => this.names.get(i)!),
      type: desugarLetE(this.exprs.get(c.type)!),
      numParams: c.numParams,
      numFields: c.numFields,
      induct: this.names.get(c.induct)!,
    }));
    const recursors: IndRecursor[] = rec.recs.map((r) => ({
      name: this.names.get(r.name)!,
      levelParams: r.levelParams.map((i) => this.names.get(i)!),
      type: desugarLetE(this.exprs.get(r.type)!),
      numParams: r.numParams,
      numIndices: r.numIndices,
      numMotives: r.numMotives,
      numMinors: r.numMinors,
      rules: r.rules.map((rule) => ({
        ctor: this.names.get(rule.ctor)!,
        nfields: rule.nfields,
        rhs: desugarLetE(this.exprs.get(rule.rhs)!),
      })),
      k: r.k,
    }));
    return { kind: "inductive", types, ctors, recursors };
  }
}

// Desugar letE to (λx:T, body) value.  Lean's `let` is definitionally
// equal to this β-redex (with extra inlining hints), and our β-machinery
// handles the conversion.
function desugarLetE(e: Expr): Expr {
  switch (e.kind) {
    case "letE":
      return {
        kind: "app",
        fn: { kind: "lam", name: e.name, type: desugarLetE(e.type), body: desugarLetE(e.body) },
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
// Main: stream NDJSON in, accumulate resolved decls, write JSON out.
// =====================================================================

async function main(): Promise<void> {
  const env = new Env();
  const decls: Decl[] = [];

  const rl = readline.createInterface({ input: process.stdin });
  for await (const raw of rl) {
    const line = raw.trim();
    if (line === "") continue;
    const rec = parseLine(line);
    if (rec === null) {
      process.stderr.write(`%% UNPARSED: ${line.slice(0, 80)}\n`);
      continue;
    }
    env.ingest(rec);
    switch (rec.tag) {
      case "def":
      case "thm":
      case "axiom":
      case "opaque":
        decls.push(env.resolveDecl(rec));
        break;
      case "quot":
        decls.push(env.resolveQuot(rec));
        break;
      case "inductive":
        decls.push(env.resolveInductive(rec));
        break;
      // Names/levels/exprs/meta are absorbed into env; not emitted.
    }
  }

  const parsed: ParsedEnv = { decls };
  const json = JSON.stringify(transformNamesToJSON(parsed));
  const prettierConfig = await resolveConfig(import.meta.filename);
  const formatted = await format(json, { ...prettierConfig, parser: "json" });
  process.stdout.write(formatted);
}

main().catch((err: unknown) => {
  // eslint-disable-next-line no-console
  console.error(err);
  process.exit(1);
});
