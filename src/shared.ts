// shared.ts — defines the output of `parse.ts` and the input of render.ts
//
//
// parse.ts reads lean4export's NDJSON and emits an array of these
// resolved declarations as JSON.  lean2lf.ts reads that JSON on stdin
// and emits Twelf LF on stdout.
//
// Notes:
//   - All cross-references are by-value:  Name, Expr, Level, etc. are
//     fully resolved trees, not indices into a shared table.  This
//     is what makes the parsed output human-readable.
//   - Schemas are exported for optional runtime validation; lean2lf.ts
//     trusts its input and skips the parse step.

import { z } from "../vendor/zod/index.js";

// --- Name ---

export type Name =
  | { kind: "anon" }
  | { kind: "str"; pre: Name; str: string }
  | { kind: "num"; pre: Name; i: number };

export const NameSchema: z.ZodType<Name> = z.lazy(() =>
  z.discriminatedUnion("kind", [
    z.object({ kind: z.literal("anon") }),
    z.object({ kind: z.literal("str"), pre: NameSchema, str: z.string() }),
    z.object({ kind: z.literal("num"), pre: NameSchema, i: z.number() }),
  ]),
);

// --- Level ---

export type Level =
  | { kind: "zero" }
  | { kind: "succ"; arg: Level }
  | { kind: "max"; l: Level; r: Level }
  | { kind: "imax"; l: Level; r: Level }
  | { kind: "param"; name: Name };

export const LevelSchema: z.ZodType<Level> = z.lazy(() =>
  z.discriminatedUnion("kind", [
    z.object({ kind: z.literal("zero") }),
    z.object({ kind: z.literal("succ"), arg: LevelSchema }),
    z.object({ kind: z.literal("max"), l: LevelSchema, r: LevelSchema }),
    z.object({ kind: z.literal("imax"), l: LevelSchema, r: LevelSchema }),
    z.object({ kind: z.literal("param"), name: NameSchema }),
  ]),
);

// --- BinderInfo ---

export const BinderInfoSchema = z.union([
  z.literal("default"),
  z.literal("implicit"),
  z.literal("strictImplicit"),
  z.literal("instImplicit"),
]);
export type BinderInfo = z.infer<typeof BinderInfoSchema>;

// --- Expr ---

export type Expr =
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

export const ExprSchema: z.ZodType<Expr> = z.lazy(() =>
  z.discriminatedUnion("kind", [
    z.object({ kind: z.literal("bvar"), deBruijn: z.number() }),
    z.object({ kind: z.literal("sort"), level: LevelSchema }),
    z.object({ kind: z.literal("const"), name: NameSchema, us: z.array(LevelSchema) }),
    z.object({ kind: z.literal("app"), fn: ExprSchema, arg: ExprSchema }),
    z.object({ kind: z.literal("lam"), name: NameSchema, type: ExprSchema, body: ExprSchema }),
    z.object({ kind: z.literal("forallE"), name: NameSchema, type: ExprSchema, body: ExprSchema }),
    z.object({
      kind: z.literal("letE"),
      name: NameSchema,
      type: ExprSchema,
      value: ExprSchema,
      body: ExprSchema,
    }),
    z.object({
      kind: z.literal("proj"),
      typeName: NameSchema,
      idx: z.number(),
      struct: ExprSchema,
    }),
    z.object({ kind: z.literal("natLit"), value: z.string() }),
    z.object({ kind: z.literal("strLit"), value: z.string() }),
  ]),
);

// --- Inductive blocks ---------------------------------------------------
// An #IND record in NDJSON declares a mutual-inductive *block*: one or
// more inductive type formers, all their constructors, and all their
// recursors.  We package them together so lean2lf.ts has the full block
// available when emitting any individual piece.

export const IndTypeSchema = z.object({
  name: NameSchema,
  levelParams: z.array(NameSchema),
  type: ExprSchema,
  numParams: z.number(),
  numIndices: z.number(),
});
export type IndType = z.infer<typeof IndTypeSchema>;

export const IndCtorSchema = z.object({
  name: NameSchema,
  levelParams: z.array(NameSchema),
  type: ExprSchema,
  numParams: z.number(),
  numFields: z.number(),
  induct: NameSchema,
});
export type IndCtor = z.infer<typeof IndCtorSchema>;

export const IndRecRuleSchema = z.object({
  ctor: NameSchema,
  nfields: z.number(),
  rhs: ExprSchema,
});
export type IndRecRule = z.infer<typeof IndRecRuleSchema>;

export const IndRecursorSchema = z.object({
  name: NameSchema,
  levelParams: z.array(NameSchema),
  type: ExprSchema,
  numParams: z.number(),
  numIndices: z.number(),
  numMotives: z.number(),
  numMinors: z.number(),
  rules: z.array(IndRecRuleSchema),
  k: z.boolean(),
});
export type IndRecursor = z.infer<typeof IndRecursorSchema>;

export const InductiveSchema = z.object({
  kind: z.literal("inductive"),
  types: z.array(IndTypeSchema),
  ctors: z.array(IndCtorSchema),
  recursors: z.array(IndRecursorSchema),
});
export type Inductive = z.infer<typeof InductiveSchema>;

// --- Top-level declarations ---------------------------------------------

export const DeclSchema = z.discriminatedUnion("kind", [
  z.object({
    kind: z.literal("def"),
    name: NameSchema,
    levelParams: z.array(NameSchema),
    type: ExprSchema,
    value: ExprSchema,
  }),
  z.object({
    kind: z.literal("thm"),
    name: NameSchema,
    levelParams: z.array(NameSchema),
    type: ExprSchema,
    value: ExprSchema,
  }),
  z.object({
    kind: z.literal("axiom"),
    name: NameSchema,
    levelParams: z.array(NameSchema),
    type: ExprSchema,
  }),
  z.object({
    kind: z.literal("opaque"),
    name: NameSchema,
    levelParams: z.array(NameSchema),
    type: ExprSchema,
    value: ExprSchema,
  }),
  z.object({
    kind: z.literal("quot"),
    quotKind: z.union([z.literal("type"), z.literal("ctor"), z.literal("lift"), z.literal("ind")]),
    name: NameSchema,
    levelParams: z.array(NameSchema),
    type: ExprSchema,
  }),
  InductiveSchema,
]);
export type Decl = z.infer<typeof DeclSchema>;

// The parsed environment, as emitted by parse.ts:
//   { decls: Decl[] }
// declared in the order the NDJSON declared them.
export const ParsedEnvSchema = z.object({
  decls: z.array(DeclSchema),
});
export type ParsedEnv = z.infer<typeof ParsedEnvSchema>;

// --- Prover plugin interface --------------------------------------------
//
// The generator (`generate-twelf.ts`, trusted) walks a ParsedEnv and, for
// each proof obligation it encounters, asks the Prover to discharge it.
// The Prover is UNTRUSTED: it can only influence the output through the
// `Fmt` values it returns, which the generator pretty-prints into proof
// terms.  An audit of shared.ts + parse.ts + generate-twelf.ts therefore
// suffices; prover.ts need not be audited.
//
// A `Fmt` is a structured Twelf proof term — atoms, applications, and
// `[x] body` abstractions (used for the level-lambdas a polymorphic proof
// carries).  Because it has no way to express a `.` (declaration terminator)
// or a raw newline, a prover cannot "smuggle" the end of one declaration and
// the start of another into a single Fmt (the generator additionally
// validates atoms and binder names; see ppFmt in generate-twelf.ts).

export type Fmt =
  | { kind: "atom"; text: string }
  | { kind: "app"; fn: Fmt; args: Fmt[] }
  | { kind: "lam"; binder: string; body: Fmt };

export function atom(text: string): Fmt {
  return { kind: "atom", text };
}

export function app(fn: Fmt, ...args: Fmt[]): Fmt {
  return args.length === 0 ? fn : { kind: "app", fn, args };
}

// `[binder] body` — a Twelf abstraction.
export function lam(binder: string, body: Fmt): Fmt {
  return { kind: "lam", binder, body };
}

// To *reject* an environment, a prover returns this as its "proof": the atom
// `fail-on-purpose`, a term of the dead-end `deliberate-failure` type (see
// tcb.elf).  The generator emits it like any other proof — `<const> :
// <obligation> = fail-on-purpose.` — and Twelf rejects it as ill-typed.  No
// special-casing in the generator: failure is just a (deliberately invalid)
// `Fmt`, distinct from `null` (a HOLE = "couldn't discharge it").
export const failOnPurpose: Fmt = atom("fail-on-purpose");

// A prover method returns either:
//   - an `Fmt`  → the generator emits `<const> : <type> = <Fmt>.`  (a real
//                 proof, or `failOnPurpose` to reject the environment)
//   - `null`    → can't discharge it → generator emits a HOLE
//                 (`<const> : <type>.`, a bare decl rejected by %freeze)
export type ProofResult = Fmt | null;

// type-wf is special: the obligation is `defeq T T (esort U)`, and the
// universe `U` is itself synthesized (it's the Sort that T inhabits — not
// given in the NDJSON).  The prover returns BOTH the synthesized sort (a
// `lvl` term) and the proof, so the generator can emit the universe as its
// own obligation on the freezable, declared-independent `lvl` family rather
// than relying on a placeholder or on Twelf reconstructing an implicit var.
// (To reject, set either field to `failOnPurpose`.)
export type TypeWfResult = { sort: Fmt; proof: Fmt } | null;

// One method per proof-obligation shape the generator can raise.  Each gets
// the relevant IR context; the generator owns rendering the obligation's
// *type*, the prover only supplies the *proof*.
export interface Prover {
  // defeq T T (esort U) — T is a well-formed type; U is its (synthesized) sort.
  typeWellFormed(ctx: { type: Expr; levelParams: Name[] }): TypeWfResult;
  // defeq V V T — value V has type T.
  valueHasType(ctx: { value: Expr; type: Expr; levelParams: Name[] }): ProofResult;
  // ends-in-sort T — T is a Π-chain ending in a sort (inductive type formers).
  endsInSort(ctx: { type: Expr; levelParams: Name[] }): ProofResult;
  // ctor-positive IndName IndLevels T — ctor type is strictly positive.
  ctorPositive(ctx: {
    ctorType: Expr;
    indName: Name;
    indLevels: Level[];
    levelParams: Name[];
  }): ProofResult;
}

// --- Helpers ------------------------------------------------------------

export function nameToString(n: Name): string {
  switch (n.kind) {
    case "anon":
      return "";
    case "str": {
      const p = nameToString(n.pre);
      return p === "" ? n.str : `${p}.${n.str}`;
    }
    case "num": {
      const p = nameToString(n.pre);
      return p === "" ? `${n.i}` : `${p}.${n.i}`;
    }
  }
}

// --- JSON wire compaction for human-readable parse.ts output -------------
// In TypeScript the Name type is a left-recursive struct, which prints to
// JSON as a deeply nested object that's hard to skim.  For wire transport
// we compact a Name to a `(string | number)[]` (innermost-to-outermost
// path components, or the empty array for `anon`) and tag it so lean2lf.ts
// can find and re-inflate it.
//
// Tag shape: `{ "_n": ["Foo", "bar", 0] }`.  The `_n` key is unambiguous
// against the IR (no field is named `_n`).

export type NameJSON = { _n: (string | number)[] };

export function nameToJSON(n: Name): NameJSON {
  const parts: (string | number)[] = [];
  let cur: Name = n;
  while (cur.kind !== "anon") {
    parts.unshift(cur.kind === "str" ? cur.str : cur.i);
    cur = cur.pre;
  }
  return { _n: parts };
}

export function nameFromJSON(j: NameJSON): Name {
  let n: Name = { kind: "anon" };
  for (const p of j._n) {
    n = typeof p === "string" ? { kind: "str", pre: n, str: p } : { kind: "num", pre: n, i: p };
  }
  return n;
}

// Walk an arbitrary value, applying `tx` to anything that "looks like"
// a Name (recursive struct with kind="anon"/"str"/"num").  Used by
// parse.ts to compact Names before serialization, and by lean2lf.ts
// to re-inflate compacted Names after JSON.parse.
export function transformNamesToJSON(v: unknown): unknown {
  if (v === null || typeof v !== "object") return v;
  if (Array.isArray(v)) return v.map(transformNamesToJSON);
  const obj = v as Record<string, unknown>;
  if (obj["kind"] === "anon" || obj["kind"] === "str" || obj["kind"] === "num") {
    return nameToJSON(obj as unknown as Name);
  }
  const out: Record<string, unknown> = {};
  for (const k in obj) out[k] = transformNamesToJSON(obj[k]);
  return out;
}

export function transformNamesFromJSON(v: unknown): unknown {
  if (v === null || typeof v !== "object") return v;
  if (Array.isArray(v)) return v.map(transformNamesFromJSON);
  const obj = v as Record<string, unknown>;
  if ("_n" in obj && Array.isArray(obj["_n"])) return nameFromJSON(obj as unknown as NameJSON);
  const out: Record<string, unknown> = {};
  for (const k in obj) out[k] = transformNamesFromJSON(obj[k]);
  return out;
}
