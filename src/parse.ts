#!/usr/bin/env -S node --experimental-strip-types
// parse.ts — read lean4export's NDJSON on stdin, write a resolved
// declaration array as JSON on stdout.
//
// The output is essentially the same information as the NDJSON, but
// with every cross-reference resolved by value rather than by index.
// This makes the parsed declarations directly readable by humans;
// lean2lf.ts consumes it as a precondition without re-validating.
//
// parseLine uses zod schemas to validate and transform each NDJSON record.

import * as readline from "node:readline";

import { format, resolveConfig } from "prettier";
import { z } from "zod";

import type {
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
// NDJSON wire format schemas.
//
// Each schema validates one record variant and transforms it into a
// typed Item.  Grouping by top-level discriminant ("in", "il", "ie",
// or a decl key) lets parseLine pick the right union immediately.
// =====================================================================

const idx = z.number().int(); // every cross-reference is a non-negative integer index
const binderInfo = z.enum(["default", "implicit", "strictImplicit", "instImplicit"]);
const binderObj = z.object({ binderInfo, name: idx, type: idx, body: idx });

const nameSchema = z.union([
  z
    .object({ in: idx, str: z.object({ pre: idx, str: z.string() }) })
    .transform((r) => ({ tag: "str" as const, idx: r.in, pre: r.str.pre, str: r.str.str })),
  z
    .object({ in: idx, num: z.object({ pre: idx, i: idx }) })
    .transform((r) => ({ tag: "num" as const, idx: r.in, pre: r.num.pre, i: r.num.i })),
]);

const levelSchema = z.union([
  z
    .object({ il: idx, succ: idx })
    .transform((r) => ({ tag: "succ" as const, idx: r.il, arg: r.succ })),
  z
    .object({ il: idx, max: z.tuple([idx, idx]) })
    .transform((r) => ({ tag: "max" as const, idx: r.il, l: r.max[0], r: r.max[1] })),
  z
    .object({ il: idx, imax: z.tuple([idx, idx]) })
    .transform((r) => ({ tag: "imax" as const, idx: r.il, l: r.imax[0], r: r.imax[1] })),
  z
    .object({ il: idx, param: idx })
    .transform((r) => ({ tag: "param" as const, idx: r.il, name: r.param })),
]);

const exprSchema = z.union([
  z
    .object({ ie: idx, bvar: idx })
    .transform((r) => ({ tag: "bvar" as const, idx: r.ie, deBruijn: r.bvar })),
  z
    .object({ ie: idx, sort: idx })
    .transform((r) => ({ tag: "sort" as const, idx: r.ie, level: r.sort })),
  z
    .object({ ie: idx, const: z.object({ name: idx, us: z.array(idx) }) })
    .transform((r) => ({ tag: "const" as const, idx: r.ie, name: r.const.name, us: r.const.us })),
  z
    .object({ ie: idx, app: z.object({ fn: idx, arg: idx }) })
    .transform((r) => ({ tag: "app" as const, idx: r.ie, fn: r.app.fn, arg: r.app.arg })),
  z
    .object({ ie: idx, lam: binderObj })
    .transform((r) => ({
      tag: "lam" as const,
      idx: r.ie,
      bi: r.lam.binderInfo,
      name: r.lam.name,
      type: r.lam.type,
      body: r.lam.body,
    })),
  z
    .object({ ie: idx, forallE: binderObj })
    .transform((r) => ({
      tag: "forallE" as const,
      idx: r.ie,
      bi: r.forallE.binderInfo,
      name: r.forallE.name,
      type: r.forallE.type,
      body: r.forallE.body,
    })),
  z
    .object({ ie: idx, letE: z.object({ name: idx, type: idx, value: idx, body: idx }) })
    .transform((r) => ({
      tag: "letE" as const,
      idx: r.ie,
      name: r.letE.name,
      type: r.letE.type,
      value: r.letE.value,
      body: r.letE.body,
    })),
  z
    .object({ ie: idx, proj: z.object({ typeName: idx, idx: idx, struct: idx }) })
    .transform((r) => ({
      tag: "proj" as const,
      idx: r.ie,
      typeName: r.proj.typeName,
      pidx: r.proj.idx,
      struct: r.proj.struct,
    })),
  z
    .object({ ie: idx, natVal: z.string() })
    .transform((r) => ({ tag: "natLit" as const, idx: r.ie, value: r.natVal })),
  z
    .object({ ie: idx, strVal: z.string() })
    .transform((r) => ({ tag: "strLit" as const, idx: r.ie, value: r.strVal })),
]);

const defLike = z.object({ name: idx, levelParams: z.array(idx), type: idx, value: idx });
const axiomLike = z.object({ name: idx, levelParams: z.array(idx), type: idx });
const indTypeSpec = z.object({
  name: idx,
  levelParams: z.array(idx),
  numParams: idx,
  numIndices: idx,
  type: idx,
});
const indCtorSpec = z.object({
  name: idx,
  levelParams: z.array(idx),
  type: idx,
  numParams: idx,
  numFields: idx,
  induct: idx,
  cidx: idx.optional(),
});
const indRecRuleSpec = z.object({ ctor: idx, nfields: idx, rhs: idx });
const indRecSpec = z.object({
  name: idx,
  levelParams: z.array(idx),
  type: idx,
  numParams: idx,
  numIndices: idx,
  numMotives: idx,
  numMinors: idx,
  rules: z.array(indRecRuleSpec),
  k: z.boolean(),
});

const declSchema = z.union([
  z.object({ def: defLike }).transform((r) => ({ tag: "def" as const, ...r.def })),
  z.object({ thm: defLike }).transform((r) => ({ tag: "thm" as const, ...r.thm })),
  z.object({ axiom: axiomLike }).transform((r) => ({ tag: "axiom" as const, ...r.axiom })),
  z.object({ opaque: defLike }).transform((r) => ({ tag: "opaque" as const, ...r.opaque })),
  z
    .object({
      quot: z.object({
        kind: z.enum(["type", "ctor", "lift", "ind"]),
        name: idx,
        levelParams: z.array(idx),
        type: idx,
      }),
    })
    .transform((r) => ({
      tag: "quot" as const,
      quotKind: r.quot.kind,
      name: r.quot.name,
      levelParams: r.quot.levelParams,
      type: r.quot.type,
    })),
  z
    .object({
      inductive: z.object({
        types: z.array(indTypeSpec),
        ctors: z.array(indCtorSpec),
        recs: z.array(indRecSpec),
      }),
    })
    .transform((r) => ({
      tag: "inductive" as const,
      types: r.inductive.types,
      ctors: r.inductive.ctors,
      recs: r.inductive.recs,
    })),
  z.object({ meta: z.unknown() }).transform(() => ({ tag: "meta" as const })),
]);

type Item =
  | z.infer<typeof nameSchema>
  | z.infer<typeof levelSchema>
  | z.infer<typeof exprSchema>
  | z.infer<typeof declSchema>;

// Convenience aliases for Env method parameters.
type SimpleDecl = Extract<z.infer<typeof declSchema>, { tag: "def" | "thm" | "axiom" | "opaque" }>;
type QuotRec = Extract<z.infer<typeof declSchema>, { tag: "quot" }>;
type IndRec = Extract<z.infer<typeof declSchema>, { tag: "inductive" }>;

// =====================================================================
// NDJSON line parsing.
// =====================================================================

function parseLine(line: string): Item | null {
  try {
    const raw = JSON.parse(line);
    if (typeof raw !== "object" || raw === null || Array.isArray(raw)) return null;
    const obj = raw as Record<string, unknown>;
    let result;
    if ("in" in obj) result = nameSchema.safeParse(obj);
    else if ("il" in obj) result = levelSchema.safeParse(obj);
    else if ("ie" in obj) result = exprSchema.safeParse(obj);
    else result = declSchema.safeParse(obj);
    return result.success ? result.data : null;
  } catch {
    return null;
  }
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
  resolveDecl(rec: SimpleDecl): Decl {
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
