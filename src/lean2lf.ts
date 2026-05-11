#!/usr/bin/env -S node --experimental-strip-types
// lean2lf.ts — translate lean4export NDJSON on stdin to Twelf LF on stdout.
//
// Usage:
//     lake env <lean4export-bin> Mathlib > out.ndjson
//     node --experimental-strip-types lean2lf.ts < out.ndjson > extra.elf
//
// The output is intended to be appended to `lean-core-v2.elf`, which
// provides the LF type theory (level algebra, of, defeq) and the
// kernel-primitive LF constructors (eq, refl, quot, sig, ...) that
// this translator targets.
//
// Conventions
// -----------
// * Universe levels are emitted explicitly: a Lean declaration with
//   level params [u_1,...,u_n] becomes an LF constant taking n `level`
//   arguments named U0,...,U(n-1).
// * Lean bound variables (de Bruijn indices) are converted to HOAS:
//   `bvar 0` under one binder becomes the LF lambda-bound variable
//   introduced by that binder, written `b<depth>`.
// * Lean kernel primitives (Eq, Quot, False, ...) are mapped to LF
//   constructors via the `kernelPrims` table; their inductive
//   declarations are skipped on emission.
// * Implicit Lean arguments at a primitive head (the alpha in
//   `@Eq.refl alpha a`) are dropped because they don't appear in the
//   corresponding LF constructor.  See the per-primitive `argMask`.
// * For each declaration we emit:
//       <name>   : level^n -> exp.                    -- the constant
//       of/<name>: {U0..} of (<name> U0 ..) <type>.   -- its typing
//       deq/<name>: {U0..} defeq (<name> U0 ..) <val>. -- delta-rule (def/thm only)
//
// Format
// ------
// Targets the JSON shapes that lean4export's Export.lean currently
// emits (matching what nanoda_lib's parser.rs accepts).  Each line in
// the NDJSON stream is one record from `zItem`, defined below; the
// Zod schemas double as living documentation of the wire format.

import * as readline from "node:readline";
import { z } from "zod";

// =====================================================================
// 1. NDJSON wire format (Zod schemas)
// =====================================================================

// --- Names -----------------------------------------------------------
//
// Each name record introduces a Name at index `in`.  Index 0 is
// implicitly Name.anonymous (no record emitted for it).

const zNameStr = z.object({
  in: z.number(),
  str: z.object({ pre: z.number(), str: z.string() }),
});
type NameStr = z.infer<typeof zNameStr>;

const zNameNum = z.object({
  in: z.number(),
  num: z.object({ pre: z.number(), i: z.number() }),
});
type NameNum = z.infer<typeof zNameNum>;

const zName = z.union([zNameStr, zNameNum]);
type Name = z.infer<typeof zName>;

// --- Levels ----------------------------------------------------------
//
// Each level record introduces a Level at index `il`.  Index 0 is
// implicitly Level.zero (no record emitted for it).

const zLevelSucc = z.object({ il: z.number(), succ: z.number() });
const zLevelMax = z.object({ il: z.number(), max: z.tuple([z.number(), z.number()]) });
const zLevelImax = z.object({ il: z.number(), imax: z.tuple([z.number(), z.number()]) });
const zLevelParam = z.object({ il: z.number(), param: z.number() });

const zLevel = z.union([zLevelSucc, zLevelMax, zLevelImax, zLevelParam]);
type Level = z.infer<typeof zLevel>;

// --- Expressions -----------------------------------------------------
//
// Each expression record introduces an Expr at index `ie`.
//
// `binderInfo` in lam/forallE doesn't affect kernel checking and is
// recorded only for downstream tooling.  `nondep` in letE is an
// optimization hint normalized to `false` by the exporter (see the
// note in Export.lean), so we don't need to look at it.

const zBinderInfo = z.enum(["default", "implicit", "strictImplicit", "instImplicit"]);

const zExprBVar = z.object({ ie: z.number(), bvar: z.number() });
const zExprSort = z.object({ ie: z.number(), sort: z.number() });
const zExprConst = z.object({
  ie: z.number(),
  const: z.object({
    name: z.number(),
    us: z.array(z.number()),
  }),
});
const zExprApp = z.object({
  ie: z.number(),
  app: z.object({
    fn: z.number(),
    arg: z.number(),
  }),
});
const zExprLam = z.object({
  ie: z.number(),
  lam: z.object({
    name: z.number(),
    type: z.number(),
    body: z.number(),
    binderInfo: zBinderInfo,
  }),
});
const zExprForallE = z.object({
  ie: z.number(),
  forallE: z.object({
    name: z.number(),
    type: z.number(),
    body: z.number(),
    binderInfo: zBinderInfo,
  }),
});
const zExprLetE = z.object({
  ie: z.number(),
  letE: z.object({
    name: z.number(),
    type: z.number(),
    value: z.number(),
    body: z.number(),
    nondep: z.boolean(),
  }),
});
const zExprProj = z.object({
  ie: z.number(),
  proj: z.object({
    typeName: z.number(),
    idx: z.number(),
    struct: z.number(),
  }),
});
const zExprNatVal = z.object({ ie: z.number(), natVal: z.string() });
const zExprStrVal = z.object({ ie: z.number(), strVal: z.string() });
const zExprMdata = z.object({
  ie: z.number(),
  mdata: z.object({
    expr: z.number(),
    data: z.unknown(),
  }),
});

const zExpr = z.union([
  zExprBVar,
  zExprSort,
  zExprConst,
  zExprApp,
  zExprLam,
  zExprForallE,
  zExprLetE,
  zExprProj,
  zExprNatVal,
  zExprStrVal,
  zExprMdata,
]);
type Expr = z.infer<typeof zExpr>;

// --- Declarations ----------------------------------------------------
//
// One declaration record per line.  `axiom`/`def`/`thm`/`opaque`/`quot`
// each carry a single object payload; `inductive` carries a triple of
// arrays describing the mutual block.

const zAxiom = z.object({
  axiom: z.object({
    name: z.number(),
    levelParams: z.array(z.number()),
    type: z.number(),
    isUnsafe: z.boolean(),
  }),
});
type Axiom = z.infer<typeof zAxiom>;

const zReducibilityHint = z.union([
  z.literal("opaque"),
  z.literal("abbrev"),
  z.object({ regular: z.number() }),
]);
const zDefSafety = z.enum(["unsafe", "safe", "partial"]);

const zDef = z.object({
  def: z.object({
    name: z.number(),
    levelParams: z.array(z.number()),
    type: z.number(),
    value: z.number(),
    hints: zReducibilityHint,
    safety: zDefSafety,
    all: z.array(z.number()),
  }),
});
type Def = z.infer<typeof zDef>;

const zThm = z.object({
  thm: z.object({
    name: z.number(),
    levelParams: z.array(z.number()),
    type: z.number(),
    value: z.number(),
    all: z.array(z.number()),
  }),
});
type Thm = z.infer<typeof zThm>;

const zOpaque = z.object({
  opaque: z.object({
    name: z.number(),
    levelParams: z.array(z.number()),
    type: z.number(),
    value: z.number(),
    isUnsafe: z.boolean(),
    all: z.array(z.number()),
  }),
});
type Opaque = z.infer<typeof zOpaque>;

const zQuotKind = z.enum(["type", "ctor", "lift", "ind"]);
const zQuotDecl = z.object({
  quot: z.object({
    name: z.number(),
    levelParams: z.array(z.number()),
    type: z.number(),
    kind: zQuotKind,
  }),
});
type QuotDecl = z.infer<typeof zQuotDecl>;

const zInductiveVal = z.object({
  name: z.number(),
  levelParams: z.array(z.number()),
  type: z.number(),
  numParams: z.number(),
  numIndices: z.number(),
  all: z.array(z.number()),
  ctors: z.array(z.number()),
  numNested: z.number(),
  isRec: z.boolean(),
  isReflexive: z.boolean(),
  isUnsafe: z.boolean(),
});
type InductiveVal = z.infer<typeof zInductiveVal>;

const zConstructorVal = z.object({
  name: z.number(),
  levelParams: z.array(z.number()),
  type: z.number(),
  induct: z.number(),
  cidx: z.number(),
  numParams: z.number(),
  numFields: z.number(),
  isUnsafe: z.boolean(),
});
type ConstructorVal = z.infer<typeof zConstructorVal>;

const zRecursorRule = z.object({
  ctor: z.number(),
  nfields: z.number(),
  rhs: z.number(),
});
type RecursorRule = z.infer<typeof zRecursorRule>;

const zRecursorVal = z.object({
  name: z.number(),
  levelParams: z.array(z.number()),
  type: z.number(),
  all: z.array(z.number()),
  numParams: z.number(),
  numIndices: z.number(),
  numMotives: z.number(),
  numMinors: z.number(),
  rules: z.array(zRecursorRule),
  k: z.boolean(),
  isUnsafe: z.boolean(),
});
type RecursorVal = z.infer<typeof zRecursorVal>;

const zInductiveDecl = z.object({
  inductive: z.object({
    types: z.array(zInductiveVal),
    ctors: z.array(zConstructorVal),
    recs: z.array(zRecursorVal),
  }),
});
type InductiveDecl = z.infer<typeof zInductiveDecl>;

// --- Metadata --------------------------------------------------------
//
// Always the first line of the stream.

const zMeta = z.object({
  meta: z.object({
    exporter: z.object({ name: z.string(), version: z.string() }),
    lean: z.object({ githash: z.string(), version: z.string() }),
    format: z.object({ version: z.string() }),
  }),
});
type Meta = z.infer<typeof zMeta>;

// --- One NDJSON record ----------------------------------------------

const zItem = z.union([
  zMeta,
  zName,
  zLevel,
  zExpr,
  zAxiom,
  zDef,
  zThm,
  zOpaque,
  zQuotDecl,
  zInductiveDecl,
]);
type Item = z.infer<typeof zItem>;

// =====================================================================
// 2. Item tables (built up as NDJSON arrives)
// =====================================================================
//
// Names and Levels reserve index 0 for the anonymous/zero element;
// the exporter never emits a record at those indices.

const names: (Name | "anon")[] = ["anon"];
const levels: (Level | "zero")[] = ["zero"];
const exprs: Expr[] = [];

// =====================================================================
// 3. Name resolution and LF identifier mangling
// =====================================================================

function nameToString(idx: number): string {
  if (idx === 0) return "_anon";
  const parts: string[] = [];
  let cur = idx;
  while (cur !== 0) {
    const n = names[cur];
    if (n === undefined) throw new Error(`name idx ${cur} undefined`);
    if (n === "anon") break;
    if ("str" in n) {
      parts.push(n.str.str);
      cur = n.str.pre;
    } else {
      parts.push(String(n.num.i));
      cur = n.num.pre;
    }
  }
  return parts.reverse().join(".");
}

// LF-safe identifier including the declaration's id so the result is
// collision-free across Lean names that mangle to the same string
// (e.g. names with non-ASCII chars).
function mangle(idx: number): string {
  const s = nameToString(idx);
  let out = "";
  for (const c of s) {
    if (/[A-Za-z0-9_]/.test(c)) out += c;
    else if (c === ".") out += "_";
    else out += "_u" + c.codePointAt(0)!.toString(16);
  }
  return `n_${idx}_${out}`;
}

// LF representation of a list of level arguments:
//   []           → `lnil`
//   [U]          → `(lcons U lnil)`
//   [U1, U2]     → `(lcons U1 (lcons U2 lnil))`
function lvlsLF(vars: string[]): string {
  let s = "lnil";
  for (let i = vars.length - 1; i >= 0; i--) s = `(lcons ${vars[i]} ${s})`;
  return s;
}

// Return the subset of `vars` that occurs as a whole-token in `lf`.
function levelVarsUsed(lf: string, vars: string[]): string[] {
  return vars.filter((v) => new RegExp(`(^|[^A-Za-z0-9_])${v}([^A-Za-z0-9_]|$)`).test(lf));
}

// Format a string literal for the Twelf strings constraint domain.
// We can't escape (the constraint domain accepts only "...") so we
// reject non-printable / non-ASCII / quote / backslash characters.
function twelfString(s: string): string {
  for (let i = 0; i < s.length; i++) {
    const cc = s.charCodeAt(i);
    if (cc < 0x20 || cc > 0x7e || s[i] === '"' || s[i] === "\\")
      throw new Error(
        `non-printable/non-ASCII or special char in string literal ` +
          `(char ${i}: U+${cc.toString(16).padStart(4, "0")})`,
      );
  }
  return `"${s}"`;
}

// =====================================================================
// 4. Kernel-primitive table
// =====================================================================
//
// For each Lean kernel primitive we list:
//   * ctor:      LF constructor name (from lean-core-v2.elf)
//   * lvlArity:  number of universe arguments
//   * argMask:   per-Lean-arg disposition.  Length = number of args
//                the LF constructor consumes (after its lvlArity
//                level args).  Args beyond `argMask.length` are
//                applied via `app`.
//       'keep'   - pass through as an exp
//       'drop'   - implicit in LF, discard
//       'hoas'   - the Lean arg is a function expression (typically a
//                  `lam`); extract its body for LF higher-order
//                  syntax `[x] body`.  eta-expand if not a `lam`.
//   * slotTypes: optional, one entry per argMask slot.  Each entry
//                produces an LF type term given (1) the translated
//                level args, (2) the LF translations of preceding
//                slots (in their argMask-position order, including
//                drops).  Used ONLY to eta-expand partial uses of the
//                primitive: a missing slot synthesizes a fresh LF
//                variable and the type from `slotTypes` becomes the
//                lambda binder's type.  Omit on a primitive whose
//                partial application is never observed; if Lean
//                hands us one anyway, the translator falls back to
//                the same fail-soft error path as before.

type Slot = "keep" | "drop" | "hoas";
type SlotType = (Us: string[], As: string[]) => string;
// A derive callback builds the LF derivation for a kernel-primitive
// application.  Called with the argMask-many slot args (in argMask
// order — including the indices of `drop` slots, even though the
// dropped Lean expressions aren't reflected at the LF term level),
// the translated level args, and the term/derivation contexts.  Each
// primitive's callback knows which `of/...` rule to invoke and which
// of the slot args need their own derivations passed in.
type DeriveFn = (
  args: number[], // slot args (length = prim.argMask.length)
  levels: string[], // translated levels (length = prim.lvlArity)
  ctx: ExprCtx,
  derCtx: string[],
  lc: LvlCtx,
) => string;
interface PrimSpec {
  ctor: string;
  lvlArity: number;
  argMask: Slot[];
  slotTypes?: SlotType[];
  derive?: DeriveFn;
}

const kernelPrims: Record<string, PrimSpec> = {
  // ----- False / Bottom -----
  False: { ctor: "botT", lvlArity: 0, argMask: [], derive: () => "of/bot" },
  "False.rec": {
    ctor: "botrec",
    lvlArity: 1,
    argMask: ["keep"],
    slotTypes: [() => `botT`],
    derive: (args, _l, ctx, dc, lc) => `(of/botrec ${deriveOf(args[0], ctx, dc, lc)})`,
  },

  // ----- Equality -----
  Eq: {
    ctor: "eq",
    lvlArity: 1,
    argMask: ["keep", "keep", "keep"],
    slotTypes: [(Us) => `(univ ${Us[0]})`, (_, As) => As[0], (_, As) => As[0]],
    derive: (args, _l, ctx, dc, lc) =>
      `(of/eq ${deriveOf(args[0], ctx, dc, lc)} ${deriveOf(args[1], ctx, dc, lc)} ${deriveOf(args[2], ctx, dc, lc)})`,
  },
  "Eq.refl": {
    ctor: "refl",
    lvlArity: 1,
    argMask: ["drop", "keep"],
    slotTypes: [(Us) => `(univ ${Us[0]})`, (_, As) => As[0]],
    // drop α; keep a.  of/refl reconstructs A from pf_a's type.
    derive: (args, _l, ctx, dc, lc) => `(of/refl ${deriveOf(args[1], ctx, dc, lc)})`,
  },
  // Eq.rec.{v,u} α a motive base b h
  // LF eqrec V U C E absorbs motive and base after the 2 levels;
  // b and h appear in the result type and apply via `app`.
  "Eq.rec": {
    ctor: "eqrec",
    lvlArity: 2,
    argMask: ["drop", "drop", "keep", "keep"],
    // drop α, a; keep motive C, base E.  b and h are
    // beyond argMask.length and app-chain on top.
    derive: (args, _l, ctx, dc, lc) =>
      `(of/eqrec ${deriveOf(args[2], ctx, dc, lc)} ${deriveOf(args[3], ctx, dc, lc)})`,
  },

  // ----- PSigma (dependent pair, Sort-polymorphic) -----
  PSigma: {
    ctor: "sig",
    lvlArity: 2,
    argMask: ["keep", "hoas"],
    slotTypes: [(Us) => `(univ ${Us[0]})`, (Us, As) => `(pi ${As[0]} ([_] (univ ${Us[1]})))`],
    derive: (args, _l, ctx, dc, lc) => {
      const A = trExpr(args[0], ctx, lc);
      return `(of/sig ${deriveOf(args[0], ctx, dc, lc)} ${deriveHoas(args[1], A, ctx, dc, lc)})`;
    },
  },
  "PSigma.mk": {
    ctor: "mkpair",
    lvlArity: 2,
    argMask: ["drop", "drop", "keep", "keep"],
    derive: (args, _l, ctx, dc, lc) =>
      `(of/mkpair ${deriveOf(args[2], ctx, dc, lc)} ${deriveOf(args[3], ctx, dc, lc)})`,
  },

  // ----- Iff -----
  Iff: {
    ctor: "iffP",
    lvlArity: 0,
    argMask: ["keep", "keep"],
    slotTypes: [() => `(univ lz)`, () => `(univ lz)`],
    derive: (args, _l, ctx, dc, lc) =>
      `(of/iffP ${deriveOf(args[0], ctx, dc, lc)} ${deriveOf(args[1], ctx, dc, lc)})`,
  },
  "Iff.intro": {
    ctor: "iffI",
    lvlArity: 0,
    argMask: ["drop", "drop", "keep", "keep"],
    derive: (args, _l, ctx, dc, lc) =>
      `(of/iffI ${deriveOf(args[2], ctx, dc, lc)} ${deriveOf(args[3], ctx, dc, lc)})`,
  },
  "Iff.mp": {
    ctor: "iffMp",
    lvlArity: 0,
    argMask: ["drop", "drop", "keep"],
    derive: (args, _l, ctx, dc, lc) => `(of/iffMp ${deriveOf(args[2], ctx, dc, lc)})`,
  },
  "Iff.mpr": {
    ctor: "iffMpr",
    lvlArity: 0,
    argMask: ["drop", "drop", "keep"],
    derive: (args, _l, ctx, dc, lc) => `(of/iffMpr ${deriveOf(args[2], ctx, dc, lc)})`,
  },

  // ----- Nonempty (propositional truncation) -----
  Nonempty: {
    ctor: "trunc",
    lvlArity: 1,
    argMask: ["keep"],
    slotTypes: [(Us) => `(univ ${Us[0]})`],
    derive: (args, _l, ctx, dc, lc) => `(of/trunc ${deriveOf(args[0], ctx, dc, lc)})`,
  },
  "Nonempty.intro": {
    ctor: "mkt",
    lvlArity: 1,
    argMask: ["drop", "keep"],
    derive: (args, _l, ctx, dc, lc) => `(of/mkt ${deriveOf(args[1], ctx, dc, lc)})`,
  },

  // ----- Acc (well-founded accessibility) -----
  Acc: {
    ctor: "acc",
    lvlArity: 1,
    argMask: ["keep", "keep", "keep"],
    slotTypes: [
      (Us) => `(univ ${Us[0]})`,
      (_, As) => `(pi ${As[0]} ([_] (pi ${As[0]} ([_] (univ lz)))))`,
      (_, As) => As[0],
    ],
    derive: (args, _l, ctx, dc, lc) =>
      `(of/acc ${deriveOf(args[0], ctx, dc, lc)} ${deriveOf(args[1], ctx, dc, lc)} ${deriveOf(args[2], ctx, dc, lc)})`,
  },
  "Acc.intro": {
    ctor: "accI",
    lvlArity: 1,
    argMask: ["drop", "drop", "keep", "keep"],
    derive: (args, _l, ctx, dc, lc) =>
      `(of/accI ${deriveOf(args[2], ctx, dc, lc)} ${deriveOf(args[3], ctx, dc, lc)})`,
  },

  // ----- Quot -----
  Quot: {
    ctor: "quot",
    lvlArity: 1,
    argMask: ["keep", "keep"],
    slotTypes: [
      (Us) => `(univ ${Us[0]})`,
      (_, As) => `(pi ${As[0]} ([_] (pi ${As[0]} ([_] (univ lz)))))`,
    ],
    derive: (args, _l, ctx, dc, lc) =>
      `(of/quot ${deriveOf(args[0], ctx, dc, lc)} ${deriveOf(args[1], ctx, dc, lc)})`,
  },
  "Quot.mk": {
    ctor: "qmk",
    lvlArity: 1,
    argMask: ["drop", "keep", "keep"],
    slotTypes: [
      (Us) => `(univ ${Us[0]})`,
      (_, As) => `(pi ${As[0]} ([_] (pi ${As[0]} ([_] (univ lz)))))`,
      (_, As) => As[0],
    ],
    // of/qmk takes only pf_x; R is reconstructed from the result type quot U A R.
    derive: (args, _l, ctx, dc, lc) => `(of/qmk ${deriveOf(args[2], ctx, dc, lc)})`,
  },
  "Quot.sound": {
    ctor: "qsound",
    lvlArity: 1,
    argMask: ["drop", "keep", "keep", "keep", "keep"],
    derive: (args, _l, ctx, dc, lc) =>
      `(of/qsound ${deriveOf(args[2], ctx, dc, lc)} ${deriveOf(args[3], ctx, dc, lc)} ${deriveOf(args[4], ctx, dc, lc)})`,
  },
  "Quot.lift": {
    ctor: "qlift",
    lvlArity: 2,
    argMask: ["drop", "drop", "drop", "keep", "keep"],
    derive: (args, _l, ctx, dc, lc) =>
      `(of/qlift ${deriveOf(args[3], ctx, dc, lc)} ${deriveOf(args[4], ctx, dc, lc)})`,
  },

  // ----- Axioms -----
  // LF `propext : exp`, with type `Π p q : Prop. (p ↔ q) → p = q`.
  // Like Classical.choice, the dependent Π-binders are real LF binders
  // (not metavars), so all three Lean args (p, q, h) must app-chain
  // on top of `propext`.  argMask is empty.
  propext: { ctor: "propext", lvlArity: 0, argMask: [], derive: () => "of/propext" },
  // LF `choice : level -> exp`, with type `(choice U) : Π α. Π h. α`.
  // The dependent Π-binder for α is a real LF binder (not a metavar),
  // so α must flow through `app`, not be dropped.  argMask is empty:
  // both Lean args (α and h) are app-chained on top of `(choice U)`.
  "Classical.choice": {
    ctor: "choice",
    lvlArity: 1,
    argMask: [],
    derive: (_a, lvls) => `(of/choice ${lvls[0]})`,
  },
};

// Projection table.  Lean's `Expr.proj typeName idx struct` is mapped
// directly when the struct type is known to us; universe args left as
// `_` for Twelf to fill in.
const projSpecs: Record<string, { fst: string; snd: string }> = {
  PSigma: { fst: "proj1 _ _", snd: "proj2 _ _" },
  Iff: { fst: "iffMp", snd: "iffMpr" },
};

const skipDecls = new Set<string>([
  ...Object.keys(kernelPrims),
  "Quot", // inductive Quot itself; its members are listed above
]);

// =====================================================================
// 5. Expression translation: levels and exprs
// =====================================================================

type LvlCtx = Map<number, string>; // Lean name-id of param -> LF level var
type ExprCtx = string[]; // LF var stack; innermost at end

function trLevel(idx: number, lc: LvlCtx): string {
  const l = idx === 0 ? "zero" : levels[idx];
  if (l === undefined) throw new Error(`level idx ${idx} undefined`);
  if (l === "zero") return "lz";
  if ("succ" in l) return `(ls ${trLevel(l.succ, lc)})`;
  if ("max" in l) return `(lmax ${trLevel(l.max[0], lc)} ${trLevel(l.max[1], lc)})`;
  if ("imax" in l) return `(limax ${trLevel(l.imax[0], lc)} ${trLevel(l.imax[1], lc)})`;
  const v = lc.get(l.param);
  if (!v) throw new Error(`unbound level param ${nameToString(l.param)} (id ${l.param})`);
  return v;
}

// =====================================================================
// 5a. Level AST + normalization + leq-witness builder.
//
//     Used by `tryEmitCheck` to wrap derivations in `of/conv` when the
//     outermost inferred level (from the of-rule used) doesn't
//     syntactically match the declared level, but is `leq`-equivalent.
//
//     Currently handles outermost-only conversions where the value is
//     a sort or a forall over computable-level sub-expressions.
// =====================================================================

type Lvl =
  | { kind: "z" }
  | { kind: "s"; inner: Lvl }
  | { kind: "max"; l: Lvl; r: Lvl }
  | { kind: "imax"; l: Lvl; r: Lvl }
  | { kind: "var"; name: string };

// Build a Lvl AST from a Lean level index.
function lvlAst(idx: number, lc: LvlCtx): Lvl {
  const l = idx === 0 ? "zero" : levels[idx];
  if (l === undefined) throw new Error(`level idx ${idx} undefined`);
  if (l === "zero") return { kind: "z" };
  if ("succ" in l) return { kind: "s", inner: lvlAst(l.succ, lc) };
  if ("max" in l) return { kind: "max", l: lvlAst(l.max[0], lc), r: lvlAst(l.max[1], lc) };
  if ("imax" in l) return { kind: "imax", l: lvlAst(l.imax[0], lc), r: lvlAst(l.imax[1], lc) };
  const v = lc.get(l.param);
  if (!v) throw new Error(`unbound level param ${nameToString(l.param)} (id ${l.param})`);
  return { kind: "var", name: v };
}

// Print a Lvl back as our LF surface syntax (matches `trLevel` output).
function lvlPrint(l: Lvl): string {
  switch (l.kind) {
    case "z":
      return "lz";
    case "s":
      return `(ls ${lvlPrint(l.inner)})`;
    case "max":
      return `(lmax ${lvlPrint(l.l)} ${lvlPrint(l.r)})`;
    case "imax":
      return `(limax ${lvlPrint(l.l)} ${lvlPrint(l.r)})`;
    case "var":
      return l.name;
  }
}

// Syntactic equality on Lvl ASTs.
function lvlEq(a: Lvl, b: Lvl): boolean {
  if (a.kind !== b.kind) return false;
  switch (a.kind) {
    case "z":
      return true;
    case "s":
      return lvlEq(a.inner, (b as typeof a).inner);
    case "max":
    case "imax":
      return lvlEq(a.l, (b as typeof a).l) && lvlEq(a.r, (b as typeof a).r);
    case "var":
      return a.name === (b as typeof a).name;
  }
}

// `(leq/trans w1 w2)` with absorption of `leq/refl` on either side.
function leqTrans(w1: string, w2: string): string {
  if (w1 === "leq/refl") return w2;
  if (w2 === "leq/refl") return w1;
  return `(leq/trans ${w1} ${w2})`;
}

// Simplify `lmax a b` where `a`, `b` are already normalized.
// Returns the simpler `form` and a witness `leq (lmax a b) form`.
function simplifyMax(a: Lvl, b: Lvl): { form: Lvl; witness: string } {
  if (a.kind === "z") return { form: b, witness: "leq/max-zL" };
  if (b.kind === "z") return { form: a, witness: "leq/max-zR" };
  if (lvlEq(a, b)) return { form: a, witness: "leq/max-idem" };
  // (lmax (s X) (s Y)) -> (s (lmax X Y)) -> (s simplify(X, Y))
  if (a.kind === "s" && b.kind === "s") {
    const inner = simplifyMax(a.inner, b.inner);
    const suc = inner.witness === "leq/refl" ? "leq/refl" : `(leq/suc ${inner.witness})`;
    return {
      form: { kind: "s", inner: inner.form },
      witness: leqTrans("leq/max-succ", suc),
    };
  }
  return { form: { kind: "max", l: a, r: b }, witness: "leq/refl" };
}

// Normalize a Lvl AST, returning a canonical form and an LF leq witness
// of `leq L form`.  Uses only equational simplifications expressible via
// our leq calculus; doesn't attempt deep max-normal-form.
function lvlNorm(l: Lvl): { form: Lvl; witness: string } {
  switch (l.kind) {
    case "z":
    case "var":
      return { form: l, witness: "leq/refl" };
    case "s": {
      const r = lvlNorm(l.inner);
      return {
        form: { kind: "s", inner: r.form },
        witness: r.witness === "leq/refl" ? "leq/refl" : `(leq/suc ${r.witness})`,
      };
    }
    case "max": {
      const ln = lvlNorm(l.l),
        rn = lvlNorm(l.r);
      const base =
        ln.witness === "leq/refl" && rn.witness === "leq/refl"
          ? "leq/refl"
          : `(leq/max ${ln.witness} ${rn.witness})`;
      const simp = simplifyMax(ln.form, rn.form);
      return { form: simp.form, witness: leqTrans(base, simp.witness) };
    }
    case "imax": {
      const ln = lvlNorm(l.l),
        rn = lvlNorm(l.r);
      const base =
        ln.witness === "leq/refl" && rn.witness === "leq/refl"
          ? "leq/refl"
          : `(leq/imax ${ln.witness} ${rn.witness})`;
      if (rn.form.kind === "z") {
        return { form: { kind: "z" }, witness: leqTrans(base, "leq/imax-zR") };
      }
      if (rn.form.kind === "s") {
        // (limax a (s X)) -> (lmax a (s X))  via leq/imax-sR
        const simp = simplifyMax(ln.form, rn.form);
        const inner = leqTrans("leq/imax-sR", simp.witness);
        return { form: simp.form, witness: leqTrans(base, inner) };
      }
      return {
        form: { kind: "imax", l: ln.form, r: rn.form },
        witness: base,
      };
    }
  }
}

// Build an LF witness for `leq L1 L2`, or throw if the engine can't
// prove them equivalent.  Strategy: normalize both, require syntactic
// match on the canonical form.
function proveLeq(l1: Lvl, l2: Lvl): string {
  const n1 = lvlNorm(l1);
  const n2 = lvlNorm(l2);
  if (!lvlEq(n1.form, n2.form)) {
    throw new Error(
      `level mismatch: ${lvlPrint(l1)} normalizes to ${lvlPrint(n1.form)}, ` +
        `${lvlPrint(l2)} normalizes to ${lvlPrint(n2.form)}`,
    );
  }
  if (n1.witness === "leq/refl" && n2.witness === "leq/refl") return "leq/refl";
  if (n2.witness === "leq/refl") return n1.witness;
  if (n1.witness === "leq/refl") return `(leq/sym ${n2.witness})`;
  return `(leq/trans ${n1.witness} (leq/sym ${n2.witness}))`;
}

// Compute the universe-level `L` such that `<exprIdx as type> : univ L`,
// or throw if the engine can't determine it.  Used for outermost
// conversion only.  `ctxLvls[i]` is the level at which the i-th binder
// (innermost at end) "lives" as a type, i.e. if the binder's type is
// `sort u` then its entry is `lvlAst(u)`; `null` means the binder isn't
// a universe (and so the bvar can't be used as a type-position term).
function levelOfType(idx: number, ctxLvls: (Lvl | null)[], lc: LvlCtx): Lvl {
  const e = exprs[idx];
  if (e === undefined) throw new Error(`expr ${idx} undefined`);
  if ("mdata" in e) return levelOfType(e.mdata.expr, ctxLvls, lc);
  if ("sort" in e) {
    return { kind: "s", inner: lvlAst(e.sort, lc) };
  }
  if ("bvar" in e) {
    const i = ctxLvls.length - 1 - e.bvar;
    if (i < 0) throw new Error(`bvar ${e.bvar} out of range`);
    const v = ctxLvls[i];
    if (v === null) throw new Error(`bvar ${e.bvar} binder is not a universe`);
    return v;
  }
  if ("forallE" in e) {
    const L1 = levelOfType(e.forallE.type, ctxLvls, lc);
    // Push the level the binder *lives at* into ctx:
    //   binder type = sort u  ⇒  binder : univ u  ⇒  push u.
    //   binder type = forall ... ⇒ binder lives at the limax level.
    //   else: push null (binder isn't a universe; can't use as type later).
    let binderLevel: Lvl | null;
    try {
      binderLevel = levelOfBinder(e.forallE.type, ctxLvls, lc);
    } catch {
      binderLevel = null;
    }
    const L2 = levelOfType(e.forallE.body, [...ctxLvls, binderLevel], lc);
    return { kind: "imax", l: L1, r: L2 };
  }
  throw new Error(`levelOfType: unhandled head ${Object.keys(e).join(",")}`);
}

// Given a type-expression T, return the level X such that any inhabitant
// `x : T` lives in universe X (i.e. `x : univ X`).  This is `T`'s
// "inner level": if T = sort u then X = u; if T = forall ... then X is
// the imax; else throw.  Used to seed `ctxLvls` when entering a binder.
function levelOfBinder(idx: number, ctxLvls: (Lvl | null)[], lc: LvlCtx): Lvl {
  const e = exprs[idx];
  if (e === undefined) throw new Error(`expr ${idx} undefined`);
  if ("mdata" in e) return levelOfBinder(e.mdata.expr, ctxLvls, lc);
  if ("sort" in e) return lvlAst(e.sort, lc);
  if ("forallE" in e) {
    const L1 = levelOfType(e.forallE.type, ctxLvls, lc);
    let binderLevel: Lvl | null;
    try {
      binderLevel = levelOfBinder(e.forallE.type, ctxLvls, lc);
    } catch {
      binderLevel = null;
    }
    const L2 = levelOfType(e.forallE.body, [...ctxLvls, binderLevel], lc);
    return { kind: "imax", l: L1, r: L2 };
  }
  throw new Error(`levelOfBinder: unhandled head ${Object.keys(e).join(",")}`);
}

// Peel an app chain.  Transparently follows `mdata`.
// Returns the head expression and arguments in left-to-right Lean order.
function peelApps(idx: number): { head: Expr; args: number[] } {
  const args: number[] = [];
  let cur = idx;
  while (true) {
    const e = exprs[cur];
    if ("mdata" in e) {
      cur = e.mdata.expr;
      continue;
    }
    if (!("app" in e)) return { head: e, args };
    args.unshift(e.app.arg);
    cur = e.app.fn;
  }
}

function freshVar(ctx: ExprCtx): string {
  return `b${ctx.length}`;
}

function trExpr(idx: number, ctx: ExprCtx, lc: LvlCtx): string {
  const e = exprs[idx];
  if (e === undefined) throw new Error(`expr idx ${idx} undefined`);

  if ("mdata" in e) return trExpr(e.mdata.expr, ctx, lc);

  if ("bvar" in e) {
    const i = ctx.length - 1 - e.bvar;
    if (i < 0 || i >= ctx.length)
      throw new Error(`bvar ${e.bvar} out of range (ctx size ${ctx.length})`);
    return ctx[i];
  }

  if ("sort" in e) return `(univ ${trLevel(e.sort, lc)})`;

  if ("const" in e) return trConstHead(e.const.name, e.const.us, [], ctx, lc);

  if ("app" in e) {
    const peeled = peelApps(idx);
    if ("const" in peeled.head)
      return trConstHead(peeled.head.const.name, peeled.head.const.us, peeled.args, ctx, lc);
    return `(app ${trExpr(e.app.fn, ctx, lc)} ${trExpr(e.app.arg, ctx, lc)})`;
  }

  if ("lam" in e) {
    const v = freshVar(ctx);
    return (
      `(lam ${trExpr(e.lam.type, ctx, lc)} ` + `([${v}] ${trExpr(e.lam.body, [...ctx, v], lc)}))`
    );
  }

  if ("forallE" in e) {
    const v = freshVar(ctx);
    return (
      `(pi ${trExpr(e.forallE.type, ctx, lc)} ` +
      `([${v}] ${trExpr(e.forallE.body, [...ctx, v], lc)}))`
    );
  }

  if ("letE" in e) {
    const v = freshVar(ctx);
    return (
      `(letx ${trExpr(e.letE.type, ctx, lc)} ` +
      `${trExpr(e.letE.value, ctx, lc)} ` +
      `([${v}] ${trExpr(e.letE.body, [...ctx, v], lc)}))`
    );
  }

  if ("proj" in e) {
    const sn = nameToString(e.proj.typeName);
    const spec = projSpecs[sn];
    if (spec) {
      const which = e.proj.idx === 0 ? spec.fst : e.proj.idx === 1 ? spec.snd : null;
      if (which) return `(${which} ${trExpr(e.proj.struct, ctx, lc)})`;
    }
    const stub = ensureProjStub(e.proj.typeName, e.proj.idx);
    return `(${stub} ${trExpr(e.proj.struct, ctx, lc)})`;
  }

  if ("natVal" in e) return `(natLit ${e.natVal})`;
  if ("strVal" in e) return `(strLit ${twelfString(e.strVal)})`;

  throw new Error(`internal: expr ${idx} matched no kind`);
}

// =====================================================================
// 5b. Derivation construction (step 3: derivation witnesses)
// =====================================================================
//
// `deriveOf(idx, ctx, derCtx, lc)` builds an LF derivation term that
// proves `of <trExpr(idx)> <T>` for *some* inferable T — that is, an
// applied chain of `of/...` rule constants from the trusted signature.
// Twelf reconstructs T from the rule signatures, so we don't need to
// track it explicitly.
//
// Parallel contexts:
//   * ctx    — LF term variables (b0, b1, ...) for each enclosing
//              binder; same as `trExpr`'s ctx.
//   * derCtx — LF derivation variables (hb0, hb1, ...) that witness
//              `of bᵢ Aᵢ` for the i-th enclosing binder.
//
// Tier-0 scope (this iteration):
//   * Handles: bvar, sort, lam, forallE, letE, mdata, natVal, strVal,
//              and const / app-of-const for NON-kernel-primitive heads.
//   * Punts (throws):
//       - app whose head reduces to a kernel primitive (would need a
//         parallel `deriveConstHead` mirroring `trConstHead`),
//       - app of non-const head (would generally need an of/conv to
//         line up the arg's type with the function's binder type),
//       - Expr.proj,
//       - bare Expr.const for a kernel primitive (rare; usually inside
//         an app chain).
//
// `tryEmitCheck` wraps a call to this in a try/catch so that a punt on
// one declaration doesn't abort the file; instead a comment is emitted
// recording the case that failed.

function deriveOf(idx: number, ctx: ExprCtx, derCtx: string[], lc: LvlCtx): string {
  const e = exprs[idx];
  if (e === undefined) throw new Error(`expr idx ${idx} undefined`);

  if ("mdata" in e) return deriveOf(e.mdata.expr, ctx, derCtx, lc);

  if ("bvar" in e) {
    const i = ctx.length - 1 - e.bvar;
    if (i < 0 || i >= derCtx.length)
      throw new Error(`bvar ${e.bvar} out of range (ctx size ${ctx.length})`);
    return derCtx[i];
  }

  if ("sort" in e) return `of/univ`;

  if ("const" in e) return deriveConstHead(e.const.name, e.const.us, [], ctx, derCtx, lc);

  if ("app" in e) {
    const peeled = peelApps(idx);
    if ("const" in peeled.head) {
      return deriveConstHead(
        peeled.head.const.name,
        peeled.head.const.us,
        peeled.args,
        ctx,
        derCtx,
        lc,
      );
    }
    // Non-const head: trust that arg's type lines up with function's
    // binder type syntactically.  This is the conversion-free fast
    // path; it fails on terms that need defeq to bridge a syntactic
    // mismatch.
    const pfF = deriveOf(e.app.fn, ctx, derCtx, lc);
    const pfA = deriveOf(e.app.arg, ctx, derCtx, lc);
    return `(of/app ${pfF} ${pfA})`;
  }

  if ("lam" in e) {
    const v = freshVar(ctx);
    const hv = `h${v}`;
    const A = trExpr(e.lam.type, ctx, lc);
    const pfA = deriveOf(e.lam.type, ctx, derCtx, lc);
    const pfBody = deriveOf(e.lam.body, [...ctx, v], [...derCtx, hv], lc);
    return `(of/lam ${pfA} ([${v}:exp] [${hv}: of ${v} ${A}] ${pfBody}))`;
  }

  if ("forallE" in e) {
    const v = freshVar(ctx);
    const hv = `h${v}`;
    const A = trExpr(e.forallE.type, ctx, lc);
    const pfA = deriveOf(e.forallE.type, ctx, derCtx, lc);
    const pfBody = deriveOf(e.forallE.body, [...ctx, v], [...derCtx, hv], lc);
    return `(of/pi ${pfA} ([${v}:exp] [${hv}: of ${v} ${A}] ${pfBody}))`;
  }

  if ("letE" in e) {
    const v = freshVar(ctx);
    const hv = `h${v}`;
    const A = trExpr(e.letE.type, ctx, lc);
    const pfA = deriveOf(e.letE.type, ctx, derCtx, lc);
    const pfV = deriveOf(e.letE.value, ctx, derCtx, lc);
    const pfBody = deriveOf(e.letE.body, [...ctx, v], [...derCtx, hv], lc);
    return `(of/let ${pfA} ${pfV} ([${v}:exp] [${hv}: of ${v} ${A}] ${pfBody}))`;
  }

  if ("natVal" in e) {
    if (!natLitOf) throw new Error("natVal seen but Nat inductive not yet declared");
    return `(${natLitOf} ${e.natVal})`;
  }
  if ("strVal" in e) {
    if (!strLitOf) throw new Error("strVal seen but String inductive not yet declared");
    return `(${strLitOf} ${twelfString(e.strVal)})`;
  }

  if ("proj" in e) throw new Error(`proj derivation not yet implemented`);

  throw new Error(`deriveOf: unhandled expr kind ${Object.keys(e).join(", ")}`);
}

// Build a HOAS-slot derivation `([x:exp] [hx:of x A] <pf>)`, where
// `<pf>` is the derivation of the Lean lam's body in the extended
// context.  Used for primitives like PSigma whose second arg is a
// dependent type family encoded as a function.  If the Lean arg isn't
// syntactically a `lam`, we eta-expand the way `emitHoas` does at the
// term level.
function deriveHoas(
  argIdx: number,
  binderTypeLF: string,
  ctx: ExprCtx,
  derCtx: string[],
  lc: LvlCtx,
): string {
  const v = freshVar(ctx);
  const hv = `h${v}`;
  const e = exprs[argIdx];
  if (e !== undefined && "lam" in e) {
    const body = deriveOf(e.lam.body, [...ctx, v], [...derCtx, hv], lc);
    return `([${v}:exp] [${hv}: of ${v} ${binderTypeLF}] ${body})`;
  }
  // eta-expand: ([x][hx] of/app <pf-arg> hx).  Note this assumes the
  // arg derivation's inferred type pi A B aligns with binderTypeLF — A.
  const argDer = deriveOf(argIdx, ctx, derCtx, lc);
  return `([${v}:exp] [${hv}: of ${v} ${binderTypeLF}] (of/app ${argDer} ${hv}))`;
}

// Derive an `of`-judgment for a const-headed application chain (or a
// bare const, when args is empty).  Kernel primitives dispatch through
// the primitive's `derive` callback (which knows how to invoke the
// rule's specific arity and which args to derive); non-primitives use
// the registered axiom `of/${mangle(nameIdx)}` and app-chain.
function deriveConstHead(
  nameIdx: number,
  us: number[],
  args: number[],
  ctx: ExprCtx,
  derCtx: string[],
  lc: LvlCtx,
): string {
  const name = nameToString(nameIdx);
  const prim = kernelPrims[name];

  if (prim) {
    if (!prim.derive) throw new Error(`kernel-primitive head ${name} has no derive callback`);
    if (us.length !== prim.lvlArity)
      throw new Error(`prim ${name}: expected ${prim.lvlArity} levels, got ${us.length}`);
    if (args.length < prim.argMask.length)
      throw new Error(`prim ${name}: partial application not yet supported in derivations`);

    const lvlStrs = us.map((u) => trLevel(u, lc));
    // Build the primitive's head derivation using only the argMask-many
    // leading args; any extras app-chain on top below.
    const slotArgs = args.slice(0, prim.argMask.length);
    let pf = prim.derive(slotArgs, lvlStrs, ctx, derCtx, lc);
    for (let i = prim.argMask.length; i < args.length; i++) {
      pf = `(of/app ${pf} ${deriveOf(args[i], ctx, derCtx, lc)})`;
    }
    return pf;
  }

  // Non-kernel-primitive constant: route through the per-kind of-rule.
  //   def → of/defn  (env fact defn/n_X, body witness check/n_X)
  //   thm → of/thm   (env fact thm/n_X, body witness check/n_X, prop witness prop/n_X)
  //   opq → of/opq   (env fact opq/n_X, body witness check/n_X)
  //   ax  → of/ax    (env fact ax/n_X — inductive members, axioms, projections)
  const lfName = mangle(nameIdx);
  const lvlStrs = us.map((u) => trLevel(u, lc));
  const apply = (head: string, args: string[]) =>
    args.length === 0 ? head : `(${head} ${args.join(" ")})`;
  const kind = declKinds.get(nameIdx) ?? "ax";
  let pf: string;
  if (kind === "def" || kind === "thm" || kind === "opq") {
    // Env fact binds every level param; check/n_X binds only those
    // that appear in V or T; prop/n_X (thms only) binds only those
    // that appear in T.  Consult checkLvlIdx / propLvlIdx for the
    // right subset.
    const checkIdx = checkLvlIdx.get(nameIdx) ?? [];
    const checkArgs = checkIdx.map((i) => lvlStrs[i]);
    if (kind === "def") {
      pf = `(of/defn ${apply("defn/" + lfName, lvlStrs)} ${apply("check/" + lfName, checkArgs)})`;
    } else if (kind === "opq") {
      pf = `(of/opq ${apply("opq/" + lfName, lvlStrs)} ${apply("check/" + lfName, checkArgs)})`;
    } else {
      // thm
      const propIdx = propLvlIdx.get(nameIdx) ?? [];
      const propArgs = propIdx.map((i) => lvlStrs[i]);
      pf = `(of/thm ${apply("thm/" + lfName, lvlStrs)} ${apply("check/" + lfName, checkArgs)} ${apply("prop/" + lfName, propArgs)})`;
    }
  } else {
    // `ax/n_X` binds every level param.
    pf = `(of/ax ${apply("ax/" + lfName, lvlStrs)})`;
  }
  for (const a of args) {
    pf = `(of/app ${pf} ${deriveOf(a, ctx, derCtx, lc)})`;
  }
  return pf;
}

// Translate a const-headed application (with the const's level args
// already extracted) into either a kernel primitive or a mangled
// user constant.
//
// Partial applications of kernel primitives are eta-expanded using
// the primitive's `slotTypes` metadata: each missing slot gets a
// fresh LF lambda binder whose type is computed from the slots that
// preceded it.  Lean treats `@Eq.{u} α a` as a function `α → Prop`;
// here it becomes `(lam α-tr ([b] (eq U α-tr a-tr b)))`.
function trConstHead(
  nameIdx: number,
  us: number[],
  args: number[],
  ctx: ExprCtx,
  lc: LvlCtx,
): string {
  const name = nameToString(nameIdx);
  const prim = kernelPrims[name];

  if (prim) {
    if (us.length !== prim.lvlArity)
      throw new Error(`prim ${name}: expected ${prim.lvlArity} levels, got ${us.length}`);

    const Us = us.map((u) => trLevel(u, lc));

    // Walk argMask slot-by-slot.  For each slot we either translate
    // the Lean-provided argument or synthesize a fresh LF variable
    // (eta-expansion).  `As[i]` is the LF translation of slot i; it
    // is used both for substitution into subsequent `slotTypes` and
    // (when the slot is keep/hoas) for the actual head application.
    const As: string[] = [];
    const headArgs: string[] = [...Us];
    const synth: { v: string; ty: string }[] = [];
    const ext: ExprCtx = [...ctx];

    for (let i = 0; i < prim.argMask.length; i++) {
      const slot = prim.argMask[i];

      let translated: string;
      if (i < args.length) {
        translated = slot === "hoas" ? emitHoas(args[i], ext, lc) : trExpr(args[i], ext, lc);
      } else {
        if (!prim.slotTypes)
          throw new Error(
            `prim ${name}: partial application not yet supported ` +
              `(got ${args.length} arg(s), needs ${prim.argMask.length})`,
          );
        const v = `b${ext.length}`;
        const ty = prim.slotTypes[i](Us, As);
        synth.push({ v, ty });
        ext.push(v);
        translated = v;
      }

      As.push(translated);
      if (slot !== "drop") headArgs.push(translated);
    }

    let s = headArgs.length === 0 ? prim.ctor : `(${prim.ctor} ${headArgs.join(" ")})`;

    // Any Lean args beyond argMask.length are applied via LF `app`.
    for (let i = prim.argMask.length; i < args.length; i++)
      s = `(app ${s} ${trExpr(args[i], ctx, lc)})`;

    // Wrap synthesized slots in lambdas (outermost binder is the
    // earliest missing slot, so we wrap in reverse).
    for (let i = synth.length - 1; i >= 0; i--) s = `(lam ${synth[i].ty} ([${synth[i].v}] ${s}))`;

    return s;
  }

  // Non-primitive constant: emit as `(const n_X <lvl-list>)`.
  const ctor = mangle(nameIdx);
  const lvlList = lvlsLF(us.map((u) => trLevel(u, lc)));
  let head = `(const ${ctor} ${lvlList})`;
  for (const a of args) head = `(app ${head} ${trExpr(a, ctx, lc)})`;
  return head;
}

// Emit an LF higher-order argument `([x] body)` for a HOAS slot.
function emitHoas(argIdx: number, ctx: ExprCtx, lc: LvlCtx): string {
  const e = exprs[argIdx];
  if (e !== undefined && "lam" in e) {
    const v = freshVar(ctx);
    return `([${v}] ${trExpr(e.lam.body, [...ctx, v], lc)})`;
  }
  // Not a `lam` --- eta-expand: ([x] (app <argTr> x))
  const v = freshVar(ctx);
  return `([${v}] (app ${trExpr(argIdx, ctx, lc)} ${v}))`;
}

// =====================================================================
// 6. Output buffering and on-demand projection stubs
// =====================================================================
//
// Each top-level declaration's lines are accumulated in `mainBuf`.  If
// expression translation needs an on-demand projection stub, that goes
// into `preBuf` so it's emitted BEFORE the declaration that needs it.

const mainBuf: string[] = [];
const preBuf: string[] = [];
const emittedProjs = new Set<string>();

function line(s: string): void {
  mainBuf.push(s);
}

function ensureProjStub(typeNameIdx: number, idx: number): string {
  const stubName = `c_proj_${typeNameIdx}_${idx}`;
  if (!emittedProjs.has(stubName)) {
    emittedProjs.add(stubName);
    const sn = nameToString(typeNameIdx);
    preBuf.push(`${stubName} : exp -> exp.   % stub for proj ${sn}.${idx} (untyped)`);
  }
  return stubName;
}

function flush(): void {
  for (const l of preBuf) console.log(l);
  for (const l of mainBuf) console.log(l);
  preBuf.length = 0;
  mainBuf.length = 0;
}

// =====================================================================
// 7. Declaration emission
// =====================================================================

const declaredConsts = new Set<string>();

// Per-Lean-name kind, populated as declarations are emitted.  Used by
// `deriveConstHead` to choose between the `of/const + check` path (for
// value-carrying decls — def/thm/opaque) and the `of/ax` path (for
// axioms, inductive types/ctors/recursors, projection stubs).
type DeclKind = "def" | "thm" | "opq" | "ax";
const declKinds = new Map<number, DeclKind>();

// For each value-carrying decl, the POSITIONAL indices (into the
// decl's levelParams) of the level params that actually occur inside
// V or T — these are the levels that `check/n_X` binds.  At use
// sites we apply exactly these levels to `check/n_X`; applying more
// or fewer would oversaturate the term or break Twelf's strict-
// variable reconstruction.  Populated by `tryEmitCheck`.
const checkLvlIdx = new Map<number, number[]>();

// For each thm, the positional indices (into levelParams) of the
// level params that occur inside T (the stated type) — these bind
// `prop/n_X`, the witness that T : Prop.  Empty for non-thm decls
// (they don't need a prop check).
const propLvlIdx = new Map<number, number[]>();

// =====================================================================
// Trust tracking
// =====================================================================
//
// In a verification setting, a translated file's outcome falls into
// one of three buckets relative to the Twelf signature:
//
//   * "verified"  — every Lean declaration in the file has its `of V T`
//                   obligation discharged by a Twelf-checkable derivation
//                   (i.e. `check/n_X = body.`).  No new axioms added.
//
//   * "trusted"   — one or more `check/n_X` entries fell back to AXIOM
//                   form because our engine could not build a derivation.
//                   Twelf will still accept the file, but the of-claim
//                   for that declaration rests on a new axiom — morally
//                   the same axiom Lean's kernel discharged for us, but
//                   we're trusting Lean's discharge rather than
//                   reproducing it.
//
//   * "failed"    — translator threw on a Lean declaration, or Twelf
//                   rejected the result.  Nothing trusted, just
//                   unverified.
//
// `axiomsAdded`       — mangled names whose check fell back to axiom.
// `translationErrors` — labels for declarations the translator could
//                       not emit at all (trExpr/withErrCtx/processItem).
//
// `flushTrustSummary` emits these as a comment block the harness can
// grep to classify the file.

const axiomsAdded: string[] = [];
const translationErrors: string[] = [];

// Names of the per-Lean-inductive literal-typing rules, set the first
// time the relevant inductive is encountered.  Used by `deriveOf` to
// build a derivation for `Expr.lit (NatVal n)` / `(StrVal s)`.
let natLitOf: string | null = null;
let strLitOf: string | null = null;

// Buffer for `check/...` derivations.  They're emitted in a separate
// block at the end of the output, AFTER all assertion-level content
// (the `of/c_X` and `deq/c_X` declarations).  Reasons:
//   * Twelf aborts a file on the first type error, so a failing
//     `check/...` should not be allowed to halt the loading of any
//     assertion-level content that downstream tooling might rely on.
//   * Deferring keeps the assertion output stable across iterations
//     where we extend `deriveOf` to handle new cases.
// Each entry is a fully-formatted multi-line check declaration
// (without the trailing blank line); `flushChecks()` writes them all
// out at the end of `main`.
const checksBuf: string[] = [];

function buildLvlCtx(levelParams: number[]): { ctx: LvlCtx; vars: string[] } {
  const ctx: LvlCtx = new Map();
  const vars: string[] = [];
  for (let i = 0; i < levelParams.length; i++) {
    const v = `U${i}`;
    ctx.set(levelParams[i], v);
    vars.push(v);
  }
  return { ctx, vars };
}

// In v2 representation each Lean declaration introduces:
//   * a `name` atom        (`n_X : name.`)
//   * one env-fact constant — `def/n_X : ... decl ... .` for declarations
//     carrying a value (def/thm/opaque), or `ax/n_X : ... ax ... .` for
//     axioms and inductive members.
//   * (for declarations with a value) a `check/n_X` deferred to the
//     end-of-file block — either a definition (when our checker can
//     derive `of V T`) or an axiom fallback.

function emitName(name: string): void {
  line(`${name} : name.`);
}

function emitDefnEnv(name: string, vars: string[], valLF: string, tyLF: string): void {
  const binders = vars.map((v) => `{${v}:level}`).join(" ");
  const prefix = binders === "" ? "" : binders + " ";
  line(`defn/${name} : ${prefix}defn ${name} ${lvlsLF(vars)} ${valLF} ${tyLF}.`);
}

function emitThmEnv(name: string, vars: string[], valLF: string, tyLF: string): void {
  const binders = vars.map((v) => `{${v}:level}`).join(" ");
  const prefix = binders === "" ? "" : binders + " ";
  line(`thm/${name} : ${prefix}thm ${name} ${lvlsLF(vars)} ${valLF} ${tyLF}.`);
}

function emitOpqEnv(name: string, vars: string[], valLF: string, tyLF: string): void {
  const binders = vars.map((v) => `{${v}:level}`).join(" ");
  const prefix = binders === "" ? "" : binders + " ";
  line(`opq/${name} : ${prefix}opq ${name} ${lvlsLF(vars)} ${valLF} ${tyLF}.`);
}

function emitAxEnv(name: string, vars: string[], tyLF: string): void {
  const binders = vars.map((v) => `{${v}:level}`).join(" ");
  const prefix = binders === "" ? "" : binders + " ";
  line(`ax/${name} : ${prefix}ax ${name} ${lvlsLF(vars)} ${tyLF}.`);
}

// Best-effort: errors surface as Twelf comments inside the
// already-emitted block so a single bad declaration doesn't kill the
// pipeline.  The constant header is emitted unconditionally so
// downstream references stay resolved.
function withErrCtx(label: string, fn: () => void): void {
  try {
    fn();
  } catch (err: any) {
    translationErrors.push(label);
    line(`% TRANSLATION ERROR (${label}): ${err.message}`);
  }
}

function emitAxiom(a: Axiom["axiom"]): void {
  const declName = nameToString(a.name);
  if (skipDecls.has(declName)) {
    line(`% (axiom ${declName} skipped: kernel primitive)`);
    line("");
    flush();
    return;
  }
  const name = mangle(a.name);
  line(`% axiom ${declName}`);
  emitName(name);
  declaredConsts.add(name);
  declKinds.set(a.name, "ax");
  withErrCtx(`axiom ${declName}`, () => {
    const { ctx, vars } = buildLvlCtx(a.levelParams);
    emitAxEnv(name, vars, trExpr(a.type, [], ctx));
  });
  line("");
  flush();
}

function emitDef(d: Def["def"]): void {
  const declName = nameToString(d.name);
  if (skipDecls.has(declName)) {
    line(`% (def ${declName} skipped: kernel primitive)`);
    line("");
    flush();
    return;
  }
  const name = mangle(d.name);
  line(`% def ${declName}`);
  emitName(name);
  declaredConsts.add(name);
  declKinds.set(d.name, "def");
  withErrCtx(`def ${declName}`, () => {
    const { ctx, vars } = buildLvlCtx(d.levelParams);
    emitDefnEnv(name, vars, trExpr(d.value, [], ctx), trExpr(d.type, [], ctx));
  });
  tryEmitCheck(`def ${declName}`, d.name, name, "def", d.levelParams, d.type, d.value);
  line("");
  flush();
}

function emitThm(t: Thm["thm"]): void {
  const declName = nameToString(t.name);
  if (skipDecls.has(declName)) {
    line(`% (thm ${declName} skipped)`);
    line("");
    flush();
    return;
  }
  const name = mangle(t.name);
  line(`% theorem ${declName}`);
  emitName(name);
  declaredConsts.add(name);
  declKinds.set(t.name, "thm");
  withErrCtx(`thm ${declName}`, () => {
    const { ctx, vars } = buildLvlCtx(t.levelParams);
    emitThmEnv(name, vars, trExpr(t.value, [], ctx), trExpr(t.type, [], ctx));
  });
  tryEmitCheck(`thm ${declName}`, t.name, name, "thm", t.levelParams, t.type, t.value);
  line("");
  flush();
}

// Emit a `check/<name>` Twelf definition with the body-typing
// derivation, if one can be built without conversion bridging.  The
// definition uses `=` (not `:` alone), so it doesn't extend `of` —
// it's just a named witness that of/<value-translated> <type-translated>
// is inhabited.  On failure to build, leaves a (per-decl) comment;
// on success, queues the check for emission at the end of the file.
// In v2 the per-decl block contains the env fact (`def/n_X` or
// `ax/n_X`) but NOT the typing axiom — `of (const n_X LS) T` is
// derived at every use site via `(of/const def/n_X check/n_X)`.
// `check/n_X` is therefore an obligation: either a Twelf definition
// whose body is a kernel-checkable derivation of `of V T`, or an
// axiom fallback when our checker can't (yet) build one.
//
// Per-decl protocol:
//   * Always emit one `check/n_X` entry into `checksBuf`.
//   * Populate `checkLvlIdx` so use sites apply the right level args.
//   * Bind only the level params that actually appear in V or T —
//     otherwise Twelf's strict-variable check rejects the entry.
function tryEmitCheck(
  label: string,
  nameIdx: number,
  name: string,
  kind: "def" | "thm" | "opq",
  levelParams: number[],
  typeIdx: number,
  valueIdx: number,
): void {
  const { ctx: lc, vars } = buildLvlCtx(levelParams);

  let tyLF: string;
  let valLF: string;
  try {
    tyLF = trExpr(typeIdx, [], lc);
    valLF = trExpr(valueIdx, [], lc);
  } catch (err: any) {
    // Couldn't even translate V or T — leave a comment and skip the
    // check.  Downstream uses of n_X will fail to typecheck (no
    // check/n_X exists), so the rest of this file likely aborts.
    translationErrors.push(label);
    line(`% (check ${label}: trExpr failed: ${err.message})`);
    checkLvlIdx.set(nameIdx, []);
    if (kind === "thm") propLvlIdx.set(nameIdx, []);
    return;
  }

  // -------------------------------------------------------------------
  // Body-typing obligation: of V T
  // -------------------------------------------------------------------
  // Subset of `vars` actually appearing in V or T (whole-token match).
  const usedVars = levelVarsUsed(`${valLF} ${tyLF}`, vars);
  const usedIndices = usedVars.map((v) => vars.indexOf(v));
  checkLvlIdx.set(nameIdx, usedIndices);

  const binders = usedVars.map((v) => `{${v}:level}`).join(" ");
  const prefix = binders === "" ? "" : binders + " ";
  const absPrefix = usedVars.length === 0 ? "" : `[${usedVars.join("] [")}] `;

  try {
    let der = deriveOf(valueIdx, [], [], lc);

    // Phase A outermost-only level conversion: if the declared type
    // is a sort and the value's inferred outer level differs from the
    // declared level, wrap `der` in `of/conv` with a `deq/univ` over a
    // proveLeq witness.  Failure here is silent — fall back to the
    // unwrapped derivation, which is then Twelf's problem to discover.
    const tyExpr = exprs[typeIdx];
    if (tyExpr !== undefined && "sort" in tyExpr) {
      try {
        const declaredLvl = lvlAst(tyExpr.sort, lc);
        const inferredLvl = levelOfType(valueIdx, [], lc);
        if (!lvlEq(inferredLvl, declaredLvl)) {
          const leqW = proveLeq(inferredLvl, declaredLvl);
          der = `(of/conv ${der} (deq/univ ${leqW}) of/univ)`;
        }
      } catch (_) {
        /* fall back to unwrapped der */
      }
    }

    checksBuf.push(`check/${name} : ${prefix}of ${valLF} ${tyLF}`);
    checksBuf.push(`              = ${absPrefix}${der}.`);
    checksBuf.push("");
  } catch (err: any) {
    // Derivation engine punted on the body — emit as axiom so use
    // sites still typecheck.  Per our trust model, an axiom here is
    // an unresolved obligation that might be false.
    axiomsAdded.push(`check/${name}`);
    checksBuf.push(`% (check ${label}: derivation punted: ${err.message})`);
    checksBuf.push(`check/${name} : ${prefix}of ${valLF} ${tyLF}.`);
    checksBuf.push("");
  }

  // -------------------------------------------------------------------
  // Prop side-condition for thms: of T (univ lz)
  // -------------------------------------------------------------------
  // This is the Lean kernel obligation that a theorem's stated type
  // be a proposition.  `of/thm` requires it as a precondition; we
  // build a derivation here and emit as `prop/n_X`, axiomatizing on
  // engine failure (same trust model as the body check).
  if (kind === "thm") {
    const propUsedVars = levelVarsUsed(tyLF, vars);
    const propUsedIndices = propUsedVars.map((v) => vars.indexOf(v));
    propLvlIdx.set(nameIdx, propUsedIndices);

    const propBinders = propUsedVars.map((v) => `{${v}:level}`).join(" ");
    const propPrefix = propBinders === "" ? "" : propBinders + " ";
    const propAbsPrefix = propUsedVars.length === 0 ? "" : `[${propUsedVars.join("] [")}] `;

    try {
      let propDer = deriveOf(typeIdx, [], [], lc);

      // Phase A wrapping for the prop check: deriveOf produces
      // `of T (univ L_inf)` where L_inf is the inferred level (e.g.
      // `(limax L1 L2)` for a pi type).  The target is `of T (univ lz)`.
      // If L_inf ≠ lz syntactically, wrap with of/conv + deq/univ + leqW.
      // If levelOfType or proveLeq fails (e.g. the type has an `app`
      // head whose level our engine can't infer), we let the exception
      // propagate to the outer catch and axiomatize the prop check —
      // emitting a wrong-level derivation here would cascade into a
      // Twelf abort downstream.
      const inferredLvl = levelOfType(typeIdx, [], lc);
      const target: Lvl = { kind: "z" };
      if (!lvlEq(inferredLvl, target)) {
        const leqW = proveLeq(inferredLvl, target);
        propDer = `(of/conv ${propDer} (deq/univ ${leqW}) of/univ)`;
      }

      checksBuf.push(`prop/${name} : ${propPrefix}of ${tyLF} (univ lz)`);
      checksBuf.push(`             = ${propAbsPrefix}${propDer}.`);
      checksBuf.push("");
    } catch (err: any) {
      // The type's of-claim couldn't be built.  Two reasons this
      // could happen: (1) our engine is incomplete for this type, or
      // (2) the obligation is actually false (T is not a Prop).  Per
      // our trust model we cannot distinguish these — both yield an
      // axiom that might be false.
      axiomsAdded.push(`prop/${name}`);
      checksBuf.push(`% (prop ${label}: derivation punted: ${err.message})`);
      checksBuf.push(`prop/${name} : ${propPrefix}of ${tyLF} (univ lz).`);
      checksBuf.push("");
    }
  }
}

// Emit all queued check declarations.  Called once at end of main(),
// after all NDJSON has been processed and assertion-level output has
// been flushed.
function flushChecks(): void {
  if (checksBuf.length === 0) return;
  console.log();
  console.log("% =====================================================================");
  console.log("% CHECK DERIVATIONS");
  console.log("% =====================================================================");
  console.log("% Twelf-checked witnesses for the body of each Lean def / thm / opaque.");
  console.log("% Best-effort: produced by `deriveOf` without conversion bridging.  A");
  console.log("% failing check (Twelf type mismatch) here aborts the rest of the file");
  console.log("% but does NOT affect the assertion-level signature above.");
  console.log();
  for (const l of checksBuf) console.log(l);
}

// Emit the trust summary as a structured comment block at the end of
// the output file.  The harness parses these lines (prefix-matched
// against `% TRUST_SUMMARY:` and `% TRUST_FIELD:`) to classify each
// translated case as verified / trusted / failed without rerunning
// the translator.
//
// Always emitted, even when both counts are zero, so the harness can
// distinguish "translator ran to completion with no flagged issues"
// from "translator never reached end of stream" (in which case no
// summary block appears at all and we treat the file as failed).
function flushTrustSummary(): void {
  console.log();
  console.log("% =====================================================================");
  console.log("% TRUST_SUMMARY");
  console.log("% =====================================================================");
  console.log(`% TRUST_FIELD axioms_added: ${axiomsAdded.length}`);
  console.log(`% TRUST_FIELD translation_errors: ${translationErrors.length}`);
  if (axiomsAdded.length > 0) {
    console.log(`% TRUST_FIELD axiom_names: ${axiomsAdded.join(", ")}`);
  }
  if (translationErrors.length > 0) {
    console.log(`% TRUST_FIELD error_labels: ${translationErrors.join(" | ")}`);
  }
}

function emitOpaque(o: Opaque["opaque"]): void {
  const declName = nameToString(o.name);
  if (skipDecls.has(declName)) {
    flush();
    return;
  }
  const name = mangle(o.name);
  line(`% opaque ${declName}`);
  emitName(name);
  declaredConsts.add(name);
  declKinds.set(o.name, "opq");
  withErrCtx(`opaque ${declName}`, () => {
    const { ctx, vars } = buildLvlCtx(o.levelParams);
    // `opq` is its own env-fact family in the signature — there's no
    // `deq/delta` rule for it, so the value is structurally hidden
    // from δ-conversion (rather than relying on a translator convention).
    emitOpqEnv(name, vars, trExpr(o.value, [], ctx), trExpr(o.type, [], ctx));
  });
  tryEmitCheck(`opaque ${declName}`, o.name, name, "opq", o.levelParams, o.type, o.value);
  line("");
  flush();
}

function emitQuotDecl(q: QuotDecl["quot"]): void {
  const declName = nameToString(q.name);
  // The four members of Quot's package have kind type/ctor/lift/ind.
  // Three are LF kernel primitives (quot, qmk, qlift) handled via
  // kernelPrims, so we skip their emission.  Quot.ind has no LF
  // counterpart, so we emit it as a regular user-axiom — its type
  // references `Quot` and `Quot.mk` which map back to `quot` and `qmk`,
  // so the result is well-formed LF.
  if (q.kind === "ind") {
    const name = mangle(q.name);
    line(`% quot ${declName} (kind=ind, emitted as user-axiom)`);
    emitName(name);
    declaredConsts.add(name);
    declKinds.set(q.name, "ax");
    withErrCtx(`quot ${declName}`, () => {
      const { ctx, vars } = buildLvlCtx(q.levelParams);
      emitAxEnv(name, vars, trExpr(q.type, [], ctx));
    });
    line("");
  } else {
    line(`% (quot ${declName} skipped: in lean-core-v2.elf as ${q.kind})`);
  }
  flush();
}

function emitInductiveMember(
  v: InductiveVal | ConstructorVal | RecursorVal,
  kind: "type" | "ctor" | "recursor",
): void {
  const declName = nameToString(v.name);
  if (skipDecls.has(declName)) {
    line(`%   (${kind} ${declName} skipped)`);
    return;
  }
  const name = mangle(v.name);
  line(`%   ${kind} ${declName}`);
  emitName(name);
  declaredConsts.add(name);
  declKinds.set(v.name, "ax");
  withErrCtx(`${kind} ${declName}`, () => {
    const { ctx, vars } = buildLvlCtx(v.levelParams);
    emitAxEnv(name, vars, trExpr(v.type, [], ctx));
  });
}

function emitInductiveDecl(ind: InductiveDecl["inductive"]): void {
  const typeNames = ind.types.map((v) => nameToString(v.name));
  // Do NOT short-circuit when every type is a kernel primitive: the
  // type and its ctor may be mapped (e.g. PSigma -> sig, PSigma.mk ->
  // mkpair) while the recursor (e.g. PSigma.rec) is NOT mapped and
  // needs to fall through to user-constant emission for downstream
  // references to resolve.  Individual `emitInductiveMember` calls
  // check skipDecls per-member.
  line(`% inductive {${typeNames.join(", ")}}`);
  for (const v of ind.types) emitInductiveMember(v, "type");
  for (const v of ind.ctors) emitInductiveMember(v, "ctor");
  for (const v of ind.recs) emitInductiveMember(v, "recursor");
  emitIotaRules(ind);

  // If this inductive is one whose values can appear as Expr.lit, emit
  // a typing rule connecting the literal constructor to the user's
  // mangled LF constant.  This is what makes `natLit 5 : c_X_Nat`
  // and `strLit "..." : c_Y_String` typecheck downstream.
  for (const v of ind.types) {
    const name = nameToString(v.name);
    if (name === "Nat") {
      line(`of/lit/${mangle(v.name)} : {N:integer} of (natLit N) (const ${mangle(v.name)} lnil).`);
      natLitOf = `of/lit/${mangle(v.name)}`;
    }
    if (name === "String") {
      line(`of/lit/${mangle(v.name)} : {S:string}  of (strLit S) (const ${mangle(v.name)} lnil).`);
      strLitOf = `of/lit/${mangle(v.name)}`;
    }
  }

  line("");
  flush();
}

// Emit one iota (recursor-reduction) rule per RecursorRule in this
// inductive block.  For each rule of a recursor R for inductive I with
// constructor c, the iota rule is:
//
//   defeq
//     (R.{Us} p_1..p_p  m_1..m_m  n_1..n_n  i_1..i_i  (c.{Us'} p_1..p_p  f_1..f_F))
//     (rhs.{Us}     p_1..p_p  m_1..m_m  n_1..n_n  f_1..f_F)
//
// where:
//   * Us  = recursor's level params,  Us' = ctor's (subset, sharing names)
//   * p   = numParams, m = numMotives, n = numMinors, i = numIndices
//   * F   = rule.nfields  (ctor's fields, excluding shared params)
//   * rhs = rule.rhs translated under the recursor's level context
//
// All non-level binders are universally quantified at the LF level;
// indices in particular are quantified freely even though the
// constructor's signature determines them.  Twelf reconstructs the
// binding at rule-use time.
//
// Skipped: recursors of nested inductives (the ctor's parameter count
// differs from the recursor's), and any rule whose recursor or ctor is
// already a kernel primitive in our LF signature.
function emitIotaRules(ind: InductiveDecl["inductive"]): void {
  if (ind.recs.length === 0) return;

  // Map: ctor name id -> ConstructorVal (for level-param lookup)
  const ctorByName = new Map<number, ConstructorVal>();
  for (const c of ind.ctors) ctorByName.set(c.name, c);

  // Map: inductive name id -> InductiveVal (for the numNested check)
  const indByName = new Map<number, InductiveVal>();
  for (const t of ind.types) indByName.set(t.name, t);

  for (const rec of ind.recs) {
    const recName = nameToString(rec.name);
    if (skipDecls.has(recName)) continue;

    if (rec.rules.length === 0) continue;

    // Find the inductive this recursor is for, via any of its rules'
    // constructors.  (Mutual-block recursors may have rules over ctors
    // of different inductives in the block, but each rule's ctor maps
    // back to a unique inductive.)
    const firstCtor = ctorByName.get(rec.rules[0].ctor);
    const indVal = firstCtor ? indByName.get(firstCtor.induct) : undefined;
    if (!indVal) {
      line(
        `% (iota for ${recName}: ctor refers to an inductive outside this block (likely a nested-recursor helper), skipped)`,
      );
      continue;
    }
    if (indVal.numNested > 0) {
      line(`% (iota for ${recName}: nested inductive, skipped)`);
      continue;
    }

    for (const rule of rec.rules) emitIotaRule(rec, rule, ctorByName);
  }
}

function emitIotaRule(
  rec: RecursorVal,
  rule: RecursorRule,
  ctorByName: Map<number, ConstructorVal>,
): void {
  const recName = nameToString(rec.name);
  const ctorName = nameToString(rule.ctor);
  if (skipDecls.has(ctorName)) {
    line(`% (iota ${recName}/${ctorName}: ctor is kernel primitive, skipped)`);
    return;
  }
  const ctor = ctorByName.get(rule.ctor);
  if (!ctor) {
    line(`% (iota ${recName}/${ctorName}: ctor val not in block, skipped)`);
    return;
  }

  const ruleName = `${mangle(rec.name)}__${mangle(rule.ctor)}`;
  withErrCtx(`iota ${recName}/${ctorName}`, () => {
    const recLfName = mangle(rec.name);
    const ctorLfName = mangle(rule.ctor);

    // Level context is the recursor's level params.  The rhs and the
    // ctor application both interpret level params through this lc;
    // the ctor's levelParams are a subset (sharing name-ids).
    const { ctx: lc, vars: uvars } = buildLvlCtx(rec.levelParams);
    const ctorUVars = ctor.levelParams.map((p) => {
      const v = lc.get(p);
      if (!v) throw new Error(`ctor uses level ${nameToString(p)} not in recursor's params`);
      return v;
    });

    // Choose binder names that won't collide with anything trExpr emits.
    // trExpr generates b0, b1, ... so we use prefixes outside that family.
    const pVars = Array.from({ length: rec.numParams }, (_, i) => `pp${i}`);
    const mVars = Array.from({ length: rec.numMotives }, (_, i) => `mm${i}`);
    const nVars = Array.from({ length: rec.numMinors }, (_, i) => `nn${i}`);
    const iVars = Array.from({ length: rec.numIndices }, (_, i) => `ii${i}`);
    const fVars = Array.from({ length: rule.nfields }, (_, i) => `ff${i}`);

    // Constructor application: (const n_ctor <lvls>) P0..F0..F(nfields-1).
    // Non-nested case: ctor's param count == recursor's numParams.
    let ctorApp = `(const ${ctorLfName} ${lvlsLF(ctorUVars)})`;
    for (const v of [...pVars, ...fVars]) ctorApp = `(app ${ctorApp} ${v})`;

    // LHS: (const n_rec <lvls>) P0..C0..N0..I0..ctorApp
    let lhs = `(const ${recLfName} ${lvlsLF(uvars)})`;
    for (const v of [...pVars, ...mVars, ...nVars, ...iVars, ctorApp]) lhs = `(app ${lhs} ${v})`;

    // RHS: trExpr(rhs) P0..C0..N0..F0..  (note: no indices)
    let rhs = trExpr(rule.rhs, [], lc);
    for (const v of [...pVars, ...mVars, ...nVars, ...fVars]) rhs = `(app ${rhs} ${v})`;

    const binders = [
      ...uvars.map((v) => `{${v}:level}`),
      ...[...pVars, ...mVars, ...nVars, ...iVars, ...fVars].map((v) => `{${v}:exp}`),
    ].join(" ");
    line(`%   iota ${recName} on ${ctorName}`);
    line(`deq/${ruleName} : ${binders}`);
    line(`  defeq ${lhs}`);
    line(`        ${rhs}.`);
  });
}

function emitMeta(m: Meta["meta"]): void {
  console.log(
    `% Translated from lean4export ${m.exporter.version} ` +
      `(Lean ${m.lean.version}, format ${m.format.version})`,
  );
  console.log(`% Append to lean-core-v2.elf for kernel-primitive support.`);
  console.log();
}

// =====================================================================
// 8. NDJSON dispatch
// =====================================================================

function processItem(item: Item): void {
  if ("meta" in item) return emitMeta(item.meta);

  // Indexed primitives
  if ("in" in item) {
    names[item.in] = item;
    return;
  }
  if ("il" in item) {
    levels[item.il] = item;
    return;
  }
  if ("ie" in item) {
    exprs[item.ie] = item;
    return;
  }

  // Declarations
  if ("axiom" in item) return emitAxiom(item.axiom);
  if ("def" in item) return emitDef(item.def);
  if ("thm" in item) return emitThm(item.thm);
  if ("opaque" in item) return emitOpaque(item.opaque);
  if ("quot" in item) return emitQuotDecl(item.quot);
  if ("inductive" in item) return emitInductiveDecl(item.inductive);

  throw new Error(`internal: item matched no shape: ${Object.keys(item).join(", ")}`);
}

// =====================================================================
// 9. Main
// =====================================================================

async function main(): Promise<void> {
  const rl = readline.createInterface({ input: process.stdin, terminal: false });
  let lineNo = 0;
  for await (const raw of rl) {
    lineNo++;
    const t = raw.trim();
    if (t === "") continue;
    let parsed: any;
    try {
      parsed = JSON.parse(t);
    } catch (err: any) {
      process.stderr.write(`line ${lineNo}: JSON parse error: ${err.message}\n`);
      translationErrors.push(`NDJSON line ${lineNo}: JSON parse`);
      continue;
    }
    const result = zItem.safeParse(parsed);
    if (!result.success) {
      const issues = result.error.issues
        .slice(0, 3)
        .map((i) => `${i.path.join(".")}: ${i.message}`)
        .join("; ");
      process.stderr.write(
        `line ${lineNo}: schema mismatch [${issues}]: ` + `${t.slice(0, 120)}\n`,
      );
      translationErrors.push(`NDJSON line ${lineNo}: schema mismatch`);
      continue;
    }
    try {
      processItem(result.data);
    } catch (err: any) {
      process.stderr.write(`line ${lineNo}: ${err.message}\n`);
      translationErrors.push(`NDJSON line ${lineNo}`);
      console.log(`% TRANSLATION ERROR at NDJSON line ${lineNo}: ${err.message}`);
    }
  }
  flushChecks();
  flushTrustSummary();
}

main().catch((err) => {
  process.stderr.write(`Fatal: ${err}\n`);
  process.exit(1);
});
