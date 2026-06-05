// synth.ts — type synthesizer and principled definitional-equality prover.
//
// UNTRUSTED. The generator only consumes the `Fmt` proof terms produced here,
// and validates every atom/binder (ppFmt in generate-twelf.ts). This module
// discharges proof obligations for the "closed fragment" (sorts, Π, λ, bvars)
// and, when an EnvMap is supplied, for constants, applications, and
// β/δ-reduction obligations. Anything unhandled → null (→ HOLE), never wrong.

import { freshVar, levelParamIndices, mangle, recordStringNeq } from "./render.ts";
import type { Expr, Fmt, Level, Name, ParsedEnv } from "./shared.ts";
import { app, atom, lam, nameToString } from "./shared.ts";

const ANON: Name = { kind: "anon" };

// ---------------------------------------------------------------------------
// Environment map (for const lookup and δ-reduction)
// ---------------------------------------------------------------------------

export interface EnvEntry {
  type: Expr;
  value: Expr | null; // null for axiom/opaque/thm/inductive — no δ-reduction
  levelParams: Name[];
  mangleName: string; // LF constant name prefix, e.g. "constType" or "PN_succ"
  // True iff this entry is a recursor.  Recursors are TCB-derived
  // (not env-declared), so when synthRec encounters `(econst "<rec>" Lvls)`
  // it must NOT fall through to `<rec>/decl` (no such constant); instead
  // it must inline-construct a `rec-derived-declared`-shaped witness.
  // If `recursorOf` is also set, the witness builder has the info it
  // needs; otherwise (non-enum shape) the lookup must fail outright so
  // the obligation HOLEs rather than emitting a dangling reference.
  isRecursor?: boolean;
  recursorOf?: {
    indMangleName: string;     // parent inductive's mangled name (for /decl, /rec-name, /eisl)
    ctors: { name: string; type: Expr; numFields: number }[];
    indUInd: Level;            // parent inductive's sort
    motiveU: Level;            // recursor's motive target sort (from T's structure)
  };
}

export type EnvMap = Map<string, EnvEntry>;

// Walk a type to find its result-sort universe level — used for recursor
// recognition (recursorOf.indUInd).  Same shape as generate-twelf.ts's
// `inductiveResultUniverse` but kept here to avoid a cycle.
function inductiveResultUniverse(t: Expr): Level | null {
  let cur = t;
  while (cur.kind === "forallE") cur = cur.body;
  return cur.kind === "sort" ? cur.level : null;
}

export function buildEnvMap(env: ParsedEnv): EnvMap {
  const m: EnvMap = new Map();
  for (const d of env.decls) {
    if (d.kind === "inductive") {
      // Register every inductive member (type former, constructor, recursor)
      // as a value-less entry: synth can reference it via defeq/const using the
      // `<mangle>/decl` witness the generator emits, but it is not δ-reducible
      // (no defn body — `value: null`). This unlocks recursor type-wf and
      // value-typed obligations that mention the inductive's constants.
      for (const t of d.types) {
        m.set(nameToString(t.name), {
          type: t.type,
          value: null,
          levelParams: t.levelParams,
          mangleName: mangle(t.name),
        });
      }
      for (const c of d.ctors) {
        m.set(nameToString(c.name), {
          type: c.type,
          value: null,
          levelParams: c.levelParams,
          mangleName: mangle(c.name),
        });
      }
      for (const r of d.recursors) {
        // Recursors are TCB-derived: the env-supplied type/rules are
        // ignored, but we record the recursor in the EnvMap so the
        // prover can synthesize a rec-derived-declared witness inline
        // when discharging `econst "<rec>" Lvls` references.
        //
        // Restrict to enum-shaped recursors (no params, no indices, no
        // level params on the inductive, no ctor fields) — the only
        // shape rec-derived/enum currently covers.  Other shapes leave
        // recursorOf undefined → recursor decl synth fails → env
        // declines.  (Phase 2 in completeness-plan §3.6.)
        const recName = nameToString(r.name);
        const parentIndN = recName.endsWith(".rec") ? recName.slice(0, -4) : null;
        const parentInd = parentIndN
          ? d.types.find((t) => nameToString(t.name) === parentIndN)
          : undefined;
        const ctorsForInd = parentIndN
          ? d.ctors.filter((c) => nameToString(c.induct) === parentIndN)
          : [];
        // Stage 2 (Phase 2): non-parametric, non-indexed, no level params,
        // ctors with ≤ 2 non-recursive non-dependent fields.  The
        // per-field-count `enum-rec-body/minor-Nf` rules in tcb.elf
        // cover this shape; recursive ctors (Nat.succ : Nat → Nat,
        // RTree → RTree, ...) need an extra IH binder per recursive
        // field, which is Stage 4 — exclude them here.
        const enumShaped =
          parentInd !== undefined &&
          parentInd.numParams === 0 &&
          parentInd.numIndices === 0 &&
          parentInd.levelParams.length === 0 &&
          ctorsForInd.every(
            (c) =>
              c.numFields <= 2 && !ctorHasRecursiveField(c.type, c.numFields, parentIndN!),
          );
        // Extract motive U from r.type's outer-binder structure.
        let motiveU: Level | null = null;
        if (r.type.kind === "forallE" && r.type.type.kind === "forallE") {
          const motiveResultType = r.type.type.body;
          if (motiveResultType.kind === "sort") motiveU = motiveResultType.level;
        }
        const indUInd =
          parentInd !== undefined ? inductiveResultUniverse(parentInd.type) : null;
        let recursorOf: EnvEntry["recursorOf"] = undefined;
        if (
          enumShaped &&
          parentInd !== undefined &&
          motiveU !== null &&
          indUInd !== null
        ) {
          recursorOf = {
            indMangleName: mangle(parentInd.name),
            ctors: ctorsForInd.map((c) => ({
              name: nameToString(c.name),
              type: c.type,
              numFields: c.numFields,
            })),
            indUInd,
            motiveU,
          };
        }
        m.set(recName, {
          type: r.type,
          value: null,
          levelParams: r.levelParams,
          mangleName: mangle(r.name),
          isRecursor: true,
          recursorOf,
        });
      }
      continue;
    }
    if (d.kind === "quot") continue;
    const key = nameToString(d.name);
    m.set(key, {
      type: d.type,
      value: d.kind === "def" ? d.value : null,
      levelParams: d.levelParams,
      mangleName: mangle(d.name),
    });
  }
  return m;
}

// ---------------------------------------------------------------------------
// Structural equality (alpha: binder names ignored)
// ---------------------------------------------------------------------------

function levelEq(a: Level, b: Level): boolean {
  if (a.kind !== b.kind) return false;
  switch (a.kind) {
    case "zero":
      return true;
    case "succ":
      return levelEq(a.arg, (b as Level & { kind: "succ" }).arg);
    case "max":
    case "imax": {
      const bb = b as Level & { kind: "max" | "imax" };
      return levelEq(a.l, bb.l) && levelEq(a.r, bb.r);
    }
    case "param":
      return nameToString(a.name) === nameToString((b as Level & { kind: "param" }).name);
  }
}

function exprEq(a: Expr, b: Expr): boolean {
  if (a.kind !== b.kind) return false;
  switch (a.kind) {
    case "bvar":
      return a.deBruijn === (b as Expr & { kind: "bvar" }).deBruijn;
    case "sort":
      return levelEq(a.level, (b as Expr & { kind: "sort" }).level);
    case "const": {
      const bb = b as Expr & { kind: "const" };
      return (
        nameToString(a.name) === nameToString(bb.name) &&
        a.us.length === bb.us.length &&
        a.us.every((u, i) => {
          const v = bb.us[i];
          return v !== undefined && levelEq(u, v);
        })
      );
    }
    case "app": {
      const bb = b as Expr & { kind: "app" };
      return exprEq(a.fn, bb.fn) && exprEq(a.arg, bb.arg);
    }
    case "lam":
    case "forallE": {
      const bb = b as Expr & { kind: "lam" | "forallE" };
      return exprEq(a.type, bb.type) && exprEq(a.body, bb.body);
    }
    case "letE": {
      const bb = b as Expr & { kind: "letE" };
      return exprEq(a.type, bb.type) && exprEq(a.value, bb.value) && exprEq(a.body, bb.body);
    }
    case "proj": {
      const bb = b as Expr & { kind: "proj" };
      return (
        nameToString(a.typeName) === nameToString(bb.typeName) &&
        a.idx === bb.idx &&
        exprEq(a.struct, bb.struct)
      );
    }
    case "natLit":
      return a.value === (b as Expr & { kind: "natLit" }).value;
    case "strLit":
      return a.value === (b as Expr & { kind: "strLit" }).value;
  }
}

// ---------------------------------------------------------------------------
// De Bruijn shift and substitution
// ---------------------------------------------------------------------------

// Lift free variables (index >= cutoff) by `by`.
function shift(e: Expr, by: number, cutoff = 0): Expr {
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

// Substitute `r` for `bvar(depth)` in `e`, decrementing deeper free vars.
function subst(e: Expr, depth: number, r: Expr): Expr {
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
      return { ...e, type: subst(e.type, depth, r), body: subst(e.body, depth + 1, r) };
    case "forallE":
      return { ...e, type: subst(e.type, depth, r), body: subst(e.body, depth + 1, r) };
    case "app":
      return { kind: "app", fn: subst(e.fn, depth, r), arg: subst(e.arg, depth, r) };
    case "letE":
      return {
        ...e,
        type: subst(e.type, depth, r),
        value: subst(e.value, depth, r),
        body: subst(e.body, depth + 1, r),
      };
    case "proj":
      return { ...e, struct: subst(e.struct, depth, r) };
  }
}

// ---------------------------------------------------------------------------
// Level instantiation (substitute level params by index)
// ---------------------------------------------------------------------------

function instantiateLevel(l: Level, sub: Map<string, Level>): Level {
  switch (l.kind) {
    case "zero":
      return l;
    case "succ":
      return { kind: "succ", arg: instantiateLevel(l.arg, sub) };
    case "max":
      return { kind: "max", l: instantiateLevel(l.l, sub), r: instantiateLevel(l.r, sub) };
    case "imax":
      return { kind: "imax", l: instantiateLevel(l.l, sub), r: instantiateLevel(l.r, sub) };
    case "param": {
      const v = sub.get(nameToString(l.name));
      return v !== undefined ? v : l;
    }
  }
}

function instantiateExprLevels(e: Expr, sub: Map<string, Level>): Expr {
  switch (e.kind) {
    case "sort":
      return { kind: "sort", level: instantiateLevel(e.level, sub) };
    case "const":
      return { kind: "const", name: e.name, us: e.us.map((u) => instantiateLevel(u, sub)) };
    case "app":
      return {
        kind: "app",
        fn: instantiateExprLevels(e.fn, sub),
        arg: instantiateExprLevels(e.arg, sub),
      };
    case "lam":
      return {
        ...e,
        type: instantiateExprLevels(e.type, sub),
        body: instantiateExprLevels(e.body, sub),
      };
    case "forallE":
      return {
        ...e,
        type: instantiateExprLevels(e.type, sub),
        body: instantiateExprLevels(e.body, sub),
      };
    case "letE":
      return {
        ...e,
        type: instantiateExprLevels(e.type, sub),
        value: instantiateExprLevels(e.value, sub),
        body: instantiateExprLevels(e.body, sub),
      };
    case "proj":
      return { ...e, struct: instantiateExprLevels(e.struct, sub) };
    case "bvar":
    case "natLit":
    case "strLit":
      return e;
  }
}

function instantiateLevels(e: Expr, lpNames: Name[], ls: Level[]): Expr {
  const sub = new Map<string, Level>();
  for (let i = 0; i < lpNames.length; i++) {
    const l = ls[i];
    const p = lpNames[i];
    if (l !== undefined && p !== undefined) sub.set(nameToString(p), l);
  }
  return instantiateExprLevels(e, sub);
}

// ---------------------------------------------------------------------------
// inst-expr proof builders
// ---------------------------------------------------------------------------

function buildLvlNth(i: number): Fmt {
  if (i === 0) return atom("nth-lvl/z");
  return app(atom("nth-lvl/s"), buildLvlNth(i - 1));
}

function buildLvlInst(l: Level, lpNames: Name[]): Fmt {
  switch (l.kind) {
    case "zero":
      return atom("inst-lvl/zero");
    case "succ":
      return app(atom("inst-lvl/succ"), buildLvlInst(l.arg, lpNames));
    case "max":
      // `<-` is left-associative: source-order premises appear in REVERSE
      // arrow order, so we emit R-proof FIRST then L-proof.  inst-lvl/max
      // source: `<- inst-lvl LS L1 L1' <- inst-lvl LS L2 L2'`.
      return app(atom("inst-lvl/max"), buildLvlInst(l.r, lpNames), buildLvlInst(l.l, lpNames));
    case "imax":
      return app(atom("inst-lvl/imax"), buildLvlInst(l.r, lpNames), buildLvlInst(l.l, lpNames));
    case "param": {
      const i = lpNames.findIndex((p) => nameToString(p) === nameToString(l.name));
      if (i < 0) return atom("inst-lvl/zero"); // fallback; shouldn't occur in well-formed schemas
      return app(atom("inst-lvl/var"), buildLvlNth(i));
    }
  }
}

function buildLvlsInst(us: Level[], lpNames: Name[]): Fmt {
  if (us.length === 0) return atom("inst-lvls/nil");
  // inst-lvls/cons source: `<- inst-lvl LS L' L'' <- inst-lvls LS LS' LS''`.
  // Reverse: rest-proof FIRST, then head-proof.
  return app(
    atom("inst-lvls/cons"),
    buildLvlsInst(us.slice(1), lpNames),
    buildLvlInst(us[0]!, lpNames),
  );
}

// ieScope[k] = the LF hypothesis name for `inst-expr bvar_k LS bvar_k` at depth k.
function buildInstExpr(e: Expr, lpNames: Name[], ieScope: string[], used: string[]): Fmt | null {
  switch (e.kind) {
    case "bvar": {
      const hyp = ieScope[e.deBruijn];
      return hyp !== undefined ? atom(hyp) : null;
    }
    case "sort":
      return app(atom("inst-expr/sort"), buildLvlInst(e.level, lpNames));
    case "const":
      return app(atom("inst-expr/const"), buildLvlsInst(e.us, lpNames));
    case "app": {
      const fn = buildInstExpr(e.fn, lpNames, ieScope, used);
      const ag = buildInstExpr(e.arg, lpNames, ieScope, used);
      return fn && ag ? app(atom("inst-expr/app"), fn, ag) : null;
    }
    case "forallE": {
      const domPf = buildInstExpr(e.type, lpNames, ieScope, used);
      if (!domPf) return null;
      const x = freshVar(used);
      const ix = freshHyp([x, ...used]);
      const bodyPf = buildInstExpr(e.body, lpNames, [ix, ...ieScope], [ix, x, ...used]);
      if (!bodyPf) return null;
      return app(atom("inst-expr/forall"), domPf, lam(x, lam(ix, bodyPf)));
    }
    case "lam": {
      const domPf = buildInstExpr(e.type, lpNames, ieScope, used);
      if (!domPf) return null;
      const x = freshVar(used);
      const ix = freshHyp([x, ...used]);
      const bodyPf = buildInstExpr(e.body, lpNames, [ix, ...ieScope], [ix, x, ...used]);
      if (!bodyPf) return null;
      return app(atom("inst-expr/lam"), domPf, lam(x, lam(ix, bodyPf)));
    }
    case "proj": {
      const spf = buildInstExpr(e.struct, lpNames, ieScope, used);
      return spf ? app(atom("inst-expr/proj"), spf) : null;
    }
    case "natLit":
      return atom("inst-expr/natlit");
    case "strLit":
      return atom("inst-expr/strlit");
    case "letE":
      return null; // no inst-expr/letE rule in TCB
  }
}

// ---------------------------------------------------------------------------
// level → Fmt
// ---------------------------------------------------------------------------

function lidxFmt(i: number): Fmt {
  let acc = atom("z");
  for (let k = 0; k < i; k++) acc = app(atom("s"), acc);
  return acc;
}

export function levelToFmt(l: Level, levelParams: Name[]): Fmt {
  switch (l.kind) {
    case "zero":
      return atom("lzero");
    case "succ":
      return app(atom("lsucc"), levelToFmt(l.arg, levelParams));
    case "max":
      return app(atom("lmax"), levelToFmt(l.l, levelParams), levelToFmt(l.r, levelParams));
    case "imax":
      return app(atom("limax"), levelToFmt(l.l, levelParams), levelToFmt(l.r, levelParams));
    case "param": {
      const i = levelParams.findIndex((p) => nameToString(p) === nameToString(l.name));
      if (i < 0) throw new Error(`unbound level param: ${nameToString(l.name)}`);
      return app(atom("lvar"), lidxFmt(i));
    }
  }
}

// ---------------------------------------------------------------------------
// Directed lvl-eq solver
// ---------------------------------------------------------------------------

function sortLevel(e: Expr): Level | null {
  return e.kind === "sort" ? e.level : null;
}

// --- Carneiro's algorithmic level inequality (see `leq-lvl` in levels.elf) --
//
// `proveMleq a b n` builds a `leq-lvl a b n` proof term (a ≤ b + n for every
// valuation) as an Fmt, or null.  The offset `n` is a non-negative integer
// in TS; the emitted LF term uses `nat`-encoded offsets (`z`/`s`).  Twelf
// reconstructs the offset by unification when applying each rule.
//
// `leq-lvl/sL` and `leq-lvl/sR` are the "tight" forms (matching Mario's
// thesis): premise has offset `(s N)`, conclusion has offset `N` (sL) or
// the dual on the other side.  The prover recurses with `n - 1` (for sL,
// when the LHS is lsucc-headed and n > 0) and `n + 1` (for sR).  Negative
// recursion is unreachable because sL only fires when n > 0; for the
// non-zero check on sL the recursion would need an offset of `s _`, which
// `z` can't unify with.  No `n >= 0` premise is needed at the leaves —
// the offset is `nat`-encoded and structurally non-negative.
//
// Completeness-only routine: a wrong or missing proof becomes a HOLE,
// never an unsound acceptance.

// The four LHS `imax` rewrites (imaxLz/Ls/Li/Lm): given `a = limax a.l r`,
// return the level `a` rewrites to and the rule atom.  `null` for `r` a
// bare param (the unencoded variable-elimination case → HOLE).
function imaxRewriteL(al: Level, r: Level): { newL: Level; ctor: string } | null {
  switch (r.kind) {
    case "zero":
      return { newL: { kind: "zero" }, ctor: "leq-lvl/imaxLz" };
    case "succ":
      return { newL: { kind: "max", l: al, r }, ctor: "leq-lvl/imaxLs" };
    case "imax": // limax L1 (limax L2 L3) → lmax (limax L1 L3) (limax L2 L3)
      return {
        newL: {
          kind: "max",
          l: { kind: "imax", l: al, r: r.r },
          r: { kind: "imax", l: r.l, r: r.r },
        },
        ctor: "leq-lvl/imaxLi",
      };
    case "max": // limax L1 (lmax L2 L3) → lmax (limax L1 L2) (limax L1 L3)
      return {
        newL: {
          kind: "max",
          l: { kind: "imax", l: al, r: r.l },
          r: { kind: "imax", l: al, r: r.r },
        },
        ctor: "leq-lvl/imaxLm",
      };
    default:
      return null;
  }
}

// The RHS `imax` rewrites (imaxRi/Rm), dual to the LHS ones for the `imax-
// of-imax` and `imax-of-max` cases.  No imaxRz/imaxRs counterparts: those
// are absent from Mario's thesis, and case analysis on the LHS (combined
// with `leq-lvl/split` for `lvar`) covers any goal that would otherwise
// need them.
function imaxRewriteR(bl: Level, r: Level): { newR: Level; ctor: string } | null {
  switch (r.kind) {
    case "imax": // limax L1 (limax L2 L3) → lmax (limax L1 L3) (limax L2 L3)
      return {
        newR: {
          kind: "max",
          l: { kind: "imax", l: bl, r: r.r },
          r: { kind: "imax", l: r.l, r: r.r },
        },
        ctor: "leq-lvl/imaxRi",
      };
    case "max": // limax L1 (lmax L2 L3) → lmax (limax L1 L2) (limax L1 L3)
      return {
        newR: {
          kind: "max",
          l: { kind: "imax", l: bl, r: r.l },
          r: { kind: "imax", l: bl, r: r.r },
        },
        ctor: "leq-lvl/imaxRm",
      };
    default:
      return null;
  }
}

function proveMleq(a: Level, b: Level, n: number, depth = 0): Fmt | null {
  if (depth > 40) return null;
  // Leaves: leq-lvl/self covers a ≡ b, leq-lvl/lz covers lzero ≤ _.
  // Both fire at any nat offset (no >= 0 premise needed).
  if (n >= 0 && levelEq(a, b)) return atom("leq-lvl/self");
  if (n >= 0 && a.kind === "zero") return atom("leq-lvl/lz");
  // Deterministic LHS rewrites: imax-elimination then succ-on-left.
  if (a.kind === "imax") {
    const rw = imaxRewriteL(a.l, a.r);
    if (rw) {
      const p = proveMleq(rw.newL, b, n, depth + 1);
      if (p) return app(atom(rw.ctor), p);
    }
  }
  if (a.kind === "succ" && n > 0) {
    const p = proveMleq(a.arg, b, n - 1, depth + 1);
    if (p) return app(atom("leq-lvl/sL"), p);
  }
  // Deterministic RHS rewrites: imax-elimination (only Ri/Rm, see comment
  // on imaxRewriteR) then succ-on-right (the "tight" form — premise has
  // offset n+1, conclusion has offset n; absorbs one lsucc from b into
  // the offset).
  if (b.kind === "imax") {
    const rw = imaxRewriteR(b.l, b.r);
    if (rw) {
      const p = proveMleq(a, rw.newR, n, depth + 1);
      if (p) return app(atom(rw.ctor), p);
    }
  }
  if (b.kind === "succ") {
    const p = proveMleq(a, b.arg, n + 1, depth + 1);
    if (p) return app(atom("leq-lvl/sR"), p);
  }
  // Branching: decompose an LHS max (both halves), or pick an RHS max disjunct.
  if (a.kind === "max") {
    const l = proveMleq(a.l, b, n, depth + 1);
    if (l) {
      const r = proveMleq(a.r, b, n, depth + 1);
      // leq-lvl/maxL source: `<- leq-lvl L1 L N <- leq-lvl L2 L N`.
      // Left-assoc reverses: r (L2-proof) FIRST, then l (L1-proof).
      if (r) return app(atom("leq-lvl/maxL"), r, l);
    }
  }
  if (b.kind === "max") {
    const l = proveMleq(a, b.l, n, depth + 1);
    if (l) return app(atom("leq-lvl/maxR1"), l);
    const r = proveMleq(a, b.r, n, depth + 1);
    if (r) return app(atom("leq-lvl/maxR2"), r);
  }
  // Last resort: eliminate a universe variable blocking as an imax second-arg
  // (the thesis' 14th rule).  Case-split it via `leq-lvl/split` (levels.elf).
  const i = findImaxBlockingIndex(a) ?? findImaxBlockingIndex(b);
  if (i !== null) {
    const ve = proveVarElim(a, b, n, i, depth);
    if (ve) return ve;
  }
  return null;
}

// de Bruijn index of a universe parameter in the current declaration, or null.
function paramIndex(name: Name): number | null {
  const i = levelParamIndices.get(nameToString(name));
  return i === undefined ? null : i;
}

// First universe-parameter index occurring as an imax SECOND argument anywhere
// in `l` — the only position where a bare variable blocks the structural mleq
// rules (and thus the one `var-elim` needs to case-split on).
function findImaxBlockingIndex(l: Level): number | null {
  switch (l.kind) {
    case "zero":
    case "param":
      return null;
    case "succ":
      return findImaxBlockingIndex(l.arg);
    case "max":
      return findImaxBlockingIndex(l.l) ?? findImaxBlockingIndex(l.r);
    case "imax": {
      if (l.r.kind === "param") {
        const j = paramIndex(l.r.name);
        if (j !== null) return j;
      }
      return findImaxBlockingIndex(l.l) ?? findImaxBlockingIndex(l.r);
    }
  }
}

// Substitute the parameter at de Bruijn index `i` throughout `l`: with `lzero`
// (mode "zero") or with `lsucc` of itself (mode "succ").  Mirrors the TCB
// `lvl-subst` judgment; `buildLvlSubst` builds the matching proof.
function substLevel(l: Level, i: number, mode: "zero" | "succ"): Level {
  switch (l.kind) {
    case "zero":
      return l;
    case "succ":
      return { kind: "succ", arg: substLevel(l.arg, i, mode) };
    case "max":
      return { kind: "max", l: substLevel(l.l, i, mode), r: substLevel(l.r, i, mode) };
    case "imax":
      return { kind: "imax", l: substLevel(l.l, i, mode), r: substLevel(l.r, i, mode) };
    case "param":
      if (paramIndex(l.name) !== i) return l;
      return mode === "zero" ? { kind: "zero" } : { kind: "succ", arg: l };
  }
}

// `lvl-subst V I L L'` proof for substituting at index `i` over `l`.  The new
// (levels.elf) rule for the variable case is unified: `lvl-subst/var`
// consumes `ord-nat I J O` + `if-eq-lvl O V (lvar J) L`.  Both are
// %total/%mode-d functional families, so we emit `_ _` and let Twelf
// reconstruct the witnesses from the conclusion's structure.
// `null` if a parameter has no known index.
function buildLvlSubst(l: Level, i: number): Fmt | null {
  switch (l.kind) {
    case "zero":
      return atom("lvl-subst/zero");
    case "succ": {
      const p = buildLvlSubst(l.arg, i);
      return p && app(atom("lvl-subst/succ"), p);
    }
    case "max": {
      const lp = buildLvlSubst(l.l, i);
      const rp = lp && buildLvlSubst(l.r, i);
      // <- L1 sub <- L2 sub → arg order is L2 first, then L1.
      return lp && rp && app(atom("lvl-subst/max"), rp, lp);
    }
    case "imax": {
      const lp = buildLvlSubst(l.l, i);
      const rp = lp && buildLvlSubst(l.r, i);
      return lp && rp && app(atom("lvl-subst/imax"), rp, lp);
    }
    case "param": {
      const j = paramIndex(l.name);
      if (j === null) return null;
      // `lvl-subst/var` source: `<- ord-nat I J O <- if-eq-lvl O V (lvar J) L`.
      // Left-assoc reverses: if-eq-lvl FIRST, then ord-nat.  Both anonymous —
      // Twelf reconstructs from the typed context.
      return app(atom("lvl-subst/var"), atom("_"), atom("_"));
    }
  }
}

// Prove `leq-lvl a b n` by eliminating the universe variable at index `i`:
// it suffices to prove the goal with that variable set to 0 and to S(itself).
function proveVarElim(a: Level, b: Level, n: number, i: number, depth: number): Fmt | null {
  const aSubZ = buildLvlSubst(a, i);
  const bSubZ = buildLvlSubst(b, i);
  if (!aSubZ || !bSubZ) return null;
  const aSubS = buildLvlSubst(a, i);
  const bSubS = buildLvlSubst(b, i);
  if (!aSubS || !bSubS) return null;
  const p0 = proveMleq(substLevel(a, i, "zero"), substLevel(b, i, "zero"), n, depth + 1);
  if (!p0) return null;
  const p1 = proveMleq(substLevel(a, i, "succ"), substLevel(b, i, "succ"), n, depth + 1);
  if (!p1) return null;
  // `leq-lvl/split` source-order premises (after the {I} binder):
  //   1. lvl-subst lzero I A Az
  //   2. lvl-subst lzero I B Bz
  //   3. leq-lvl Az Bz N
  //   4. lvl-subst (lsucc (lvar I)) I A As
  //   5. lvl-subst (lsucc (lvar I)) I B Bs
  //   6. leq-lvl As Bs N
  // `<-` is left-associative, so explicit-arg order is the REVERSE of
  // source order: succ-branch leq first, then succ B-sub, succ A-sub, then
  // zero-branch leq, zero B-sub, zero A-sub.
  return app(atom("leq-lvl/split"), lidxFmt(i), p1, bSubS, aSubS, p0, bSubZ, aSubZ);
}

export function proveLvlEq(a: Level, b: Level): Fmt | null {
  if (levelEq(a, b)) return atom("eq-lvl/refl"); // fast path, keeps proof terms small
  const le = proveMleq(a, b, 0);
  if (le === null) return null;
  const ge = proveMleq(b, a, 0);
  if (ge === null) return null;
  // eq-lvl/le source: `<- leq-lvl L L' z <- leq-lvl L' L z`.  Left-assoc
  // reverses: ge (L' ≤ L) first, then le (L ≤ L').
  return app(atom("eq-lvl/le"), ge, le);
}

// ---------------------------------------------------------------------------
// Scope and hypothesis helpers
// ---------------------------------------------------------------------------

interface Hyp {
  hyp: string;
  ty: Expr;
}

function freshHyp(used: string[]): string {
  if (!used.includes("h")) return "h";
  for (let i = 1; ; i++) {
    const c = `h${i}`;
    if (!used.includes(c)) return c;
  }
}

// ---------------------------------------------------------------------------
// Type synthesis  synthRec: defeq e e ty
// ---------------------------------------------------------------------------

interface Synthed {
  ty: Expr;
  proof: Fmt;
}

function synthRec(e: Expr, scope: Hyp[], used: string[], envMap?: EnvMap): Synthed | null {
  switch (e.kind) {
    case "sort":
      return {
        ty: { kind: "sort", level: { kind: "succ", arg: e.level } },
        proof: atom("defeq/sort-refl"),
      };

    case "bvar": {
      const h = scope[e.deBruijn];
      if (h === undefined) return null;
      return { ty: shift(h.ty, e.deBruijn + 1), proof: atom(h.hyp) };
    }

    case "const": {
      if (!envMap) return null;
      const entry = envMap.get(nameToString(e.name));
      if (!entry) return null;
      if (e.us.length !== entry.levelParams.length) return null;
      const instType = instantiateLevels(entry.type, entry.levelParams, e.us);
      const ie = buildInstExpr(entry.type, entry.levelParams, [], []);
      if (!ie) return null;
      // For recursors, inline-construct the `declared` witness from the
      // TCB's rec-derived family — see EnvEntry.recursorOf and CLAUDE.md
      // "Derive, don't check."  For non-recursors, the env-emitted
      // `<mn>/decl` constant is the witness as before.
      //
      // If the entry IS a recursor but `recursorOf` isn't set, the
      // recursor's shape is outside what `buildRecursorDeclared` covers
      // (Phase 1 = enum-only).  We MUST return null rather than fall
      // back to `<mn>/decl` — the translator doesn't emit a `<rec>/decl`
      // constant under the derive-canonical pivot, so falling back
      // would emit a dangling reference that Twelf rejects with a
      // confusing "typing ambiguous" error.
      let declProof: Fmt;
      if (entry.isRecursor) {
        if (!entry.recursorOf) return null;
        const built = buildRecursorDeclared(entry.recursorOf, envMap);
        if (built === null) return null;
        declProof = built;
      } else {
        declProof = atom(entry.mangleName + "/decl");
      }
      return {
        ty: instType,
        proof: app(atom("defeq/const"), declProof, ie),
      };
    }

    case "app": {
      const rF = synthRec(e.fn, scope, used, envMap);
      if (!rF) return null;
      let fnProof = rF.proof;
      let fnForall: Expr & { kind: "forallE" };
      if (rF.ty.kind === "forallE") {
        fnForall = rF.ty;
      } else {
        if (!envMap) return null;
        const r = reduceToForall(rF.ty, fnProof, envMap, scope, used);
        if (!r) return null;
        fnForall = r.forall;
        fnProof = r.proof;
      }
      const rA = synthRec(e.arg, scope, used, envMap);
      if (!rA) return null;
      let argProof = rA.proof;
      if (!exprEq(rA.ty, fnForall.type)) {
        const coerce = bridgeInternal(rA.ty, fnForall.type, scope, used, envMap, 0);
        if (!coerce) return null;
        argProof = app(atom("defeq/conv"), coerce.proof, rA.proof);
      }
      return {
        ty: subst(fnForall.body, 0, e.arg),
        proof: app(atom("defeq/app"), fnProof, argProof),
      };
    }

    case "forallE": {
      const rA = synthRec(e.type, scope, used, envMap);
      if (!rA) return null;
      let domProof = rA.proof;
      let u = sortLevel(rA.ty);
      if (!u) {
        if (!envMap) return null;
        const r = reduceToSort(rA.ty, rA.proof, envMap, scope, used);
        if (!r) return null;
        domProof = r.proof;
        u = r.level;
      }
      const x = freshVar(used);
      const usedX = [x, ...used];
      const h = freshHyp(usedX);
      const usedH = [h, ...usedX];
      const rB = synthRec(e.body, [{ hyp: h, ty: e.type }, ...scope], usedH, envMap);
      if (!rB) return null;
      let bodyProof = rB.proof;
      let v = sortLevel(rB.ty);
      if (!v) {
        if (!envMap) return null;
        const r = reduceToSort(rB.ty, rB.proof, envMap, scope, usedH);
        if (!r) return null;
        bodyProof = r.proof;
        v = r.level;
      }
      return {
        ty: { kind: "sort", level: { kind: "imax", l: u, r: v } },
        proof: app(atom("defeq/forall"), domProof, lam(x, lam(h, bodyProof))),
      };
    }

    case "lam": {
      const rA = synthRec(e.type, scope, used, envMap);
      if (!rA) return null;
      let domProof = rA.proof;
      if (!sortLevel(rA.ty)) {
        if (!envMap) return null;
        const r = reduceToSort(rA.ty, rA.proof, envMap, scope, used);
        if (!r) return null;
        domProof = r.proof;
      }
      const x = freshVar(used);
      const usedX = [x, ...used];
      const h = freshHyp(usedX);
      const usedH = [h, ...usedX];
      const rB = synthRec(e.body, [{ hyp: h, ty: e.type }, ...scope], usedH, envMap);
      if (!rB) return null;
      return {
        ty: { kind: "forallE", name: ANON, type: e.type, body: rB.ty },
        proof: app(atom("defeq/lam"), domProof, lam(x, lam(h, rB.proof))),
      };
    }

    default:
      return null;
  }
}

// ---------------------------------------------------------------------------
// Principled definitional equality  defeqProof: defeq a b ty
// ---------------------------------------------------------------------------

interface DefeqResult {
  proof: Fmt;
  ty: Expr; // type index of the proof
}

// Reduce the type of `e` (given as `proof : defeq e e ty`) to a sort.
// Returns {level, proof: defeq e e (esort level)} or null.
function reduceToSort(
  ty: Expr,
  proof: Fmt,
  envMap: EnvMap,
  scope: Hyp[],
  used: string[],
  depth = 0,
): { level: Level; proof: Fmt } | null {
  if (depth > 8) return null;
  const u = sortLevel(ty);
  if (u !== null) return { level: u, proof };
  const step = whnfStep(ty, envMap, scope, used, depth);
  if (!step) return null;
  return reduceToSort(
    step.result,
    app(atom("defeq/conv"), step.proof, proof),
    envMap,
    scope,
    used,
    depth + 1,
  );
}

// Reduce the type of `e` (given as `proof : defeq e e ty`) to a forallE.
// Returns {forall: ..., proof: defeq e e (forall ...)} or null.
function reduceToForall(
  ty: Expr,
  proof: Fmt,
  envMap: EnvMap,
  scope: Hyp[],
  used: string[],
  depth = 0,
): { forall: Expr & { kind: "forallE" }; proof: Fmt } | null {
  if (depth > 8) return null;
  if (ty.kind === "forallE") return { forall: ty, proof };
  const step = whnfStep(ty, envMap, scope, used, depth);
  if (!step) return null;
  return reduceToForall(
    step.result,
    app(atom("defeq/conv"), step.proof, proof),
    envMap,
    scope,
    used,
    depth + 1,
  );
}

// One-step head reduction: β (app of lam) or δ (const with defn).
// Returns {result, proof: defeq e result ty, ty} or null if no redex.
function whnfStep(
  e: Expr,
  envMap: EnvMap,
  scope: Hyp[],
  used: string[],
  depth: number,
): (DefeqResult & { result: Expr }) | null {
  if (depth > 24) return null;

  if (e.kind === "app") {
    const fn = e.fn;
    // β: fn is already a lam
    if (fn.kind === "lam") {
      // defeq/beta : ({x}{h} defeq (Body x)(Body x)(Bty x)) -> defeq E' E' A
      //           -> defeq (eapp (elam A Body) E')(Body E')(Bty E')
      const A = fn.type;
      const x = freshVar(used);
      const usedX = [x, ...used];
      const h = freshHyp(usedX);
      const usedH = [h, ...usedX];
      const bodyS = synthRec(fn.body, [{ hyp: h, ty: A }, ...scope], usedH, envMap);
      if (!bodyS) return null;
      // motive: lam x lam h bodyS.proof
      const motive = lam(x, lam(h, bodyS.proof));
      // arg proof: defeq E' E' A — synth and coerce
      const argS = synthRec(e.arg, scope, used, envMap);
      if (!argS) return null;
      let argProof = argS.proof;
      if (!exprEq(argS.ty, A)) {
        const br = bridgeInternal(argS.ty, A, scope, used, envMap, depth + 1);
        if (!br) return null;
        argProof = app(atom("defeq/conv"), br.proof, argS.proof);
      }
      const result = subst(fn.body, 0, e.arg);
      const ty = subst(bodyS.ty, 0, e.arg);
      return { result, proof: app(atom("defeq/beta"), motive, argProof), ty };
    }

    // lift: whnf fn one step and wrap with defeq/app
    const sf = whnfStep(fn, envMap, scope, used, depth + 1);
    if (sf && sf.ty.kind === "forallE") {
      const argS = synthRec(e.arg, scope, used, envMap);
      if (!argS) return null;
      let argProof = argS.proof;
      if (!exprEq(argS.ty, sf.ty.type)) {
        const br = bridgeInternal(argS.ty, sf.ty.type, scope, used, envMap, depth + 1);
        if (!br) return null;
        argProof = app(atom("defeq/conv"), br.proof, argS.proof);
      }
      const result: Expr = { kind: "app", fn: sf.result, arg: e.arg };
      const ty = subst(sf.ty.body, 0, e.arg);
      return { result, proof: app(atom("defeq/app"), sf.proof, argProof), ty };
    }
    return null;
  }

  if (e.kind === "const") {
    const entry = envMap.get(nameToString(e.name));
    if (!entry || !entry.value) return null; // axiom/opaque/thm: no δ
    if (e.us.length !== entry.levelParams.length) return null;
    const T = instantiateLevels(entry.type, entry.levelParams, e.us);
    const V = instantiateLevels(entry.value, entry.levelParams, e.us);
    const ieT = buildInstExpr(entry.type, entry.levelParams, [], []);
    const ieV = buildInstExpr(entry.value, entry.levelParams, [], []);
    if (!ieT || !ieV) return null;
    return {
      result: V,
      proof: app(atom("defeq/delta"), atom(entry.mangleName + "/decl"), ieT, ieV),
      ty: T,
    };
  }

  return null;
}

// Combine two proofs via defeq/trans, inserting defeq/conv if type indices differ.
// p1 : defeq a m ty1   p2 : defeq m b ty2   →   defeq a b ty1
function transAt(
  p1: Fmt,
  ty1: Expr,
  p2: Fmt,
  ty2: Expr,
  envMap: EnvMap,
  scope: Hyp[],
  used: string[],
  depth: number,
): DefeqResult | null {
  if (exprEq(ty1, ty2)) {
    return { proof: app(atom("defeq/trans"), p1, p2), ty: ty1 };
  }
  // Convert p2 from ty2 to ty1 via defeq/conv.
  const conv = defeqProofInternal(ty2, ty1, envMap, scope, used, depth + 1);
  if (!conv) return null;
  const p2c = app(atom("defeq/conv"), conv.proof, p2);
  return { proof: app(atom("defeq/trans"), p1, p2c), ty: ty1 };
}

// Core principled defeq prover: produces proof of `defeq a b ty` or null.
function defeqProofInternal(
  a: Expr,
  b: Expr,
  envMap: EnvMap,
  scope: Hyp[],
  used: string[],
  depth: number,
): DefeqResult | null {
  if (depth > 20) return null;

  // 1. Reflexivity
  if (exprEq(a, b)) {
    const s = synthRec(a, scope, used, envMap);
    return s ? { proof: s.proof, ty: s.ty } : null;
  }

  // 2. Both sorts: level equality
  if (a.kind === "sort" && b.kind === "sort") {
    const le = proveLvlEq(a.level, b.level);
    if (!le) return null;
    return {
      proof: app(atom("defeq/sort-eq"), le),
      ty: { kind: "sort", level: { kind: "succ", arg: a.level } },
    };
  }

  // 3. Reduce a one step, recurse
  const sa = whnfStep(a, envMap, scope, used, depth + 1);
  if (sa) {
    const rest = defeqProofInternal(sa.result, b, envMap, scope, used, depth + 1);
    if (rest) {
      const combined = transAt(
        sa.proof,
        sa.ty,
        rest.proof,
        rest.ty,
        envMap,
        scope,
        used,
        depth + 1,
      );
      if (combined) return combined;
    }
  }

  // 4. Reduce b one step, recurse (symm on b's step)
  const sb = whnfStep(b, envMap, scope, used, depth + 1);
  if (sb) {
    const rest = defeqProofInternal(a, sb.result, envMap, scope, used, depth + 1);
    if (rest) {
      const bSymm = app(atom("defeq/symm"), sb.proof);
      const combined = transAt(rest.proof, rest.ty, bSymm, sb.ty, envMap, scope, used, depth + 1);
      if (combined) return combined;
    }
  }

  // 5. Structural congruence for matching heads (neutral / no redex)
  if (a.kind === "forallE" && b.kind === "forallE") {
    const dom = defeqProofInternal(a.type, b.type, envMap, scope, used, depth + 1);
    if (!dom) return null;
    const domSort = sortLevel(dom.ty);
    if (!domSort) return null;
    const x = freshVar(used);
    const usedX = [x, ...used];
    const h = freshHyp(usedX);
    const usedH = [h, ...usedX];
    const bodyScope = [{ hyp: h, ty: a.type }, ...scope];
    const body = defeqProofInternal(a.body, b.body, envMap, bodyScope, usedH, depth + 1);
    if (!body) return null;
    const bodySort = sortLevel(body.ty);
    if (!bodySort) return null;
    return {
      proof: app(atom("defeq/forall"), dom.proof, lam(x, lam(h, body.proof))),
      ty: { kind: "sort", level: { kind: "imax", l: domSort, r: bodySort } },
    };
  }

  if (a.kind === "lam" && b.kind === "lam") {
    const dom = defeqProofInternal(a.type, b.type, envMap, scope, used, depth + 1);
    if (!dom) return null;
    const x = freshVar(used);
    const usedX = [x, ...used];
    const h = freshHyp(usedX);
    const usedH = [h, ...usedX];
    const bodyScope = [{ hyp: h, ty: a.type }, ...scope];
    const body = defeqProofInternal(a.body, b.body, envMap, bodyScope, usedH, depth + 1);
    if (!body) return null;
    return {
      proof: app(atom("defeq/lam"), dom.proof, lam(x, lam(h, body.proof))),
      ty: { kind: "forallE", name: ANON, type: a.type, body: body.ty },
    };
  }

  if (a.kind === "app" && b.kind === "app") {
    const fn = defeqProofInternal(a.fn, b.fn, envMap, scope, used, depth + 1);
    if (!fn || fn.ty.kind !== "forallE") return null;
    let argProof: Fmt;
    const argR = defeqProofInternal(a.arg, b.arg, envMap, scope, used, depth + 1);
    if (!argR) return null;
    if (!exprEq(argR.ty, fn.ty.type)) {
      const br = bridgeInternal(argR.ty, fn.ty.type, scope, used, envMap, depth + 1);
      if (!br) return null;
      argProof = app(atom("defeq/conv"), br.proof, argR.proof);
    } else {
      argProof = argR.proof;
    }
    return {
      proof: app(atom("defeq/app"), fn.proof, argProof),
      ty: subst(fn.ty.body, 0, a.arg),
    };
  }

  return null;
}

// ---------------------------------------------------------------------------
// Type coercion  bridge / bridgeInternal
// ---------------------------------------------------------------------------

// Prove `defeq from to (esort _)` — both arguments are types.
// Returns the proof or null.
function bridgeInternal(
  from: Expr,
  to: Expr,
  scope: Hyp[],
  used: string[],
  envMap: EnvMap | undefined,
  depth: number,
): DefeqResult | null {
  if (depth > 8) return null;

  // Pure-sort / Π-congruence path (no env needed)
  const lf = sortLevel(from);
  const lt = sortLevel(to);
  if (lf && lt) {
    const le = proveLvlEq(lf, lt);
    if (!le) return null;
    return {
      proof: app(atom("defeq/sort-eq"), le),
      ty: { kind: "sort", level: { kind: "succ", arg: lf } },
    };
  }

  if (from.kind === "forallE" && to.kind === "forallE") {
    const dom = bridgeInternal(from.type, to.type, scope, used, envMap, depth + 1);
    if (!dom) return null;
    const x = freshVar(used);
    const usedX = [x, ...used];
    const h = freshHyp(usedX);
    const usedH = [h, ...usedX];
    const innerScope = [{ hyp: h, ty: from.type }, ...scope];
    const body = bridgeInternal(from.body, to.body, innerScope, usedH, envMap, depth + 1);
    if (!body) return null;
    return {
      proof: app(atom("defeq/forall"), dom.proof, lam(x, lam(h, body.proof))),
      ty: { kind: "sort", level: { kind: "zero" } }, // sort level computed by Twelf
    };
  }

  if (!envMap) return null;
  // General: use defeqProofInternal with reduction
  return defeqProofInternal(from, to, envMap, scope, used, depth);
}

export function bridge(from: Expr, to: Expr, envMap?: EnvMap): ((pf: Fmt) => Fmt) | null {
  if (exprEq(from, to)) return (pf) => pf;
  const p = bridgeInternal(from, to, [], [], envMap, 0);
  if (!p) return null;
  return (pf) => app(atom("defeq/conv"), p.proof, pf);
}

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

export function synth(e: Expr, envMap?: EnvMap): Synthed | null {
  return synthRec(e, [], [], envMap);
}

export function synthSort(e: Expr, envMap?: EnvMap): Level | null {
  const r = synth(e, envMap);
  return r ? sortLevel(r.ty) : null;
}

// ---------------------------------------------------------------------------
// Track C: ends-in-sort + ctor-positive (strict positivity) proof builders
// ---------------------------------------------------------------------------
//
// These are purely structural ports from the (now-deleted) lean2lf.ts: they
// build `Fmt` witnesses for the soundness gates Lean requires on inductive
// declarations. As with everything in this module, they return null (→ HOLE)
// whenever the shape isn't handled — never an unsound proof.

// `ends-in-sort T`: T is a Π-chain ending in a sort. Structural only (no
// reduction), matching Lean's own ends-in-sort check.
export function endsInSortProof(t: Expr, scope: string[] = []): Fmt | null {
  if (t.kind === "sort") return atom("ends-in-sort/sort");
  if (t.kind === "forallE") {
    const v = freshVar(scope);
    const inner = endsInSortProof(t.body, [v, ...scope]);
    if (!inner) return null;
    return app(atom("ends-in-sort/forall"), lam(v, inner));
  }
  return null;
}

// Does `t` syntactically equal the inductive's self-reference
// `econst selfName selfLevels`?
function isSelfRef(t: Expr, selfName: string, selfLevels: Level[]): boolean {
  if (t.kind !== "const") return false;
  if (nameToString(t.name) !== selfName) return false;
  if (t.us.length !== selfLevels.length) return false;
  return t.us.every((u, i) => {
    const sl = selfLevels[i];
    return sl !== undefined && levelEq(u, sl);
  });
}

// Does `t` syntactically mention the self-reference anywhere?
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

// Render a `lvls` list to Fmt: (lcons L0 (lcons L1 ... lnil)).
function lvlsToFmt(us: Level[], levelParams: Name[]): Fmt {
  let acc = atom("lnil");
  for (let i = us.length - 1; i >= 0; i--) {
    acc = app(atom("lcons"), levelToFmt(us[i]!, levelParams), acc);
  }
  return acc;
}

// Render an Expr to an LF `expr` term as Fmt (the data-level encoding, not a
// proof). Mirrors render.ts's `lfExpr` but produces Fmt and, when `self` is
// supplied, replaces occurrences of the self-reference with `atom(self.varName)`
// (used to build the HOAS `T_HOAS` argument to ctor-positive/intro).
// Returns null for shapes outside the representable fragment (letE/proj/lits)
// so callers degrade to a HOLE rather than emit something wrong.
function exprToFmt(
  t: Expr,
  boundVars: string[],
  levelParams: Name[],
  self?: { name: string; levels: Level[]; varName: string },
): Fmt | null {
  if (self && isSelfRef(t, self.name, self.levels)) return atom(self.varName);
  switch (t.kind) {
    case "bvar": {
      const name = boundVars[t.deBruijn];
      return name !== undefined ? atom(name) : null;
    }
    case "sort":
      return app(atom("esort"), levelToFmt(t.level, levelParams));
    case "const":
      return app(atom("econst"), atom(`"${nameToString(t.name)}"`), lvlsToFmt(t.us, levelParams));
    case "app": {
      const fn = exprToFmt(t.fn, boundVars, levelParams, self);
      const ag = exprToFmt(t.arg, boundVars, levelParams, self);
      return fn && ag ? app(atom("eapp"), fn, ag) : null;
    }
    case "lam":
    case "forallE": {
      const ty = exprToFmt(t.type, boundVars, levelParams, self);
      if (!ty) return null;
      const v = freshVar(boundVars);
      const body = exprToFmt(t.body, [v, ...boundVars], levelParams, self);
      if (!body) return null;
      return app(atom(t.kind === "forallE" ? "eforall" : "elam"), ty, lam(v, body));
    }
    default:
      return null; // letE / proj / natLit / strLit — conservative
  }
}

// `applies-self ([S] T)`: T's head, after S-substitution, is the bound S.
function buildAppliesSelf(t: Expr, selfName: string, selfLevels: Level[]): Fmt | null {
  if (isSelfRef(t, selfName, selfLevels)) return atom("applies-self/refl");
  if (t.kind === "app") {
    const inner = buildAppliesSelf(t.fn, selfName, selfLevels);
    return inner ? app(atom("applies-self/app"), inner) : null;
  }
  return null;
}

// `no-self-ref N0 E`: the constant `econst N0` (at ANY level instantiation) is
// absent from E.  Discharges each `econst N` leaf with a posited `string-neq N
// N0` fact (recordStringNeq → the open `string-neq` family, audited globally by
// final-checks.elf), and each bound-variable leaf with the `no-self-ref N0 y`
// hypothesis carried in `nsScope` (parallel to the expr-var `scope`).  Returns
// null on a genuine self-occurrence (N === selfName — absence is unprovable, so
// the obligation degrades to a HOLE rather than a query-tripping lie) or on any
// node outside the rendered fragment.  Only ever reached on exprs `exprToFmt`
// already renders (sort / const / app / lam / forallE / bvar).
function buildNoSelfRef(
  t: Expr,
  selfName: string,
  scope: string[],
  nsScope: string[],
  levelParams: Name[],
): Fmt | null {
  switch (t.kind) {
    case "bvar": {
      const h = nsScope[t.deBruijn];
      return h !== undefined ? atom(h) : null;
    }
    case "sort":
      return atom("no-self-ref/sort");
    case "const": {
      const n = nameToString(t.name);
      if (n === selfName) return null; // a real self-occurrence: cannot prove absence
      return app(atom("no-self-ref/const"), atom(recordStringNeq(n, selfName)));
    }
    case "app": {
      const f = buildNoSelfRef(t.fn, selfName, scope, nsScope, levelParams);
      const a = buildNoSelfRef(t.arg, selfName, scope, nsScope, levelParams);
      return f && a ? app(atom("no-self-ref/app"), f, a) : null;
    }
    case "lam":
    case "forallE": {
      const ty = buildNoSelfRef(t.type, selfName, scope, nsScope, levelParams);
      if (!ty) return null;
      const y = freshVar([...scope, ...nsScope]);
      const ny = freshVar([y, ...scope, ...nsScope]);
      const body = buildNoSelfRef(t.body, selfName, [y, ...scope], [ny, ...nsScope], levelParams);
      if (!body) return null;
      const c = t.kind === "forallE" ? "no-self-ref/forall" : "no-self-ref/lam";
      return app(atom(c), ty, lam(y, lam(ny, body)));
    }
    default:
      return null; // proj / natLit / strLit / letE — outside the rendered fragment
  }
}

// `strict-pos N0 ([S] T)`: head / no-occur / Π cases.  `nsScope` carries the
// `no-self-ref N0 y` hypothesis for each enclosing Π-bound variable (parallel
// to `scope`), threaded so the no-occur/forall leaves can prove the inductive
// absent from closed domains.
function buildStrictPos(
  t: Expr,
  selfName: string,
  selfLevels: Level[],
  scope: string[],
  nsScope: string[],
  levelParams: Name[],
): Fmt | null {
  const head = buildAppliesSelf(t, selfName, selfLevels);
  if (head) return app(atom("strict-pos/head"), head);
  if (!exprMentions(t, selfName, selfLevels)) {
    const e = exprToFmt(t, scope, levelParams);
    if (!e) return null;
    const nsr = buildNoSelfRef(t, selfName, scope, nsScope, levelParams);
    return nsr ? app(atom("strict-pos/no-occur"), e, nsr) : null;
  }
  if (t.kind === "forallE") {
    if (exprMentions(t.type, selfName, selfLevels)) return null;
    const A = exprToFmt(t.type, scope, levelParams);
    if (!A) return null;
    const nsrA = buildNoSelfRef(t.type, selfName, scope, nsScope, levelParams);
    if (!nsrA) return null;
    const y = freshVar([...scope, ...nsScope]);
    const ny = freshVar([y, ...scope, ...nsScope]);
    const inner = buildStrictPos(
      t.body,
      selfName,
      selfLevels,
      [y, ...scope],
      [ny, ...nsScope],
      levelParams,
    );
    if (!inner) return null;
    return app(atom("strict-pos/forall"), A, nsrA, lam(y, lam(ny, inner)));
  }
  return null;
}

// `ctor-spine N0 ([S] T)`: Π-bodies via ctor-spine/arg; leaf must be S-applied.
//
// This is the *spine* proof that ctor-positive/intro consumes.  The matching
// `T_HOAS` argument is NOT built here: the trusted generator computes it
// directly (render.ts `lfExpr` with a SelfSubst).  Soundness no longer hinges
// on that T_HOAS being correct — the TCB's `no-self-ref` premises (discharged
// by buildNoSelfRef above, audited by the global `%query`) reject any residual
// self-constant in a closed position regardless — so an ill-formed spine can
// only lose completeness, never soundness.
export function buildCtorSpine(
  t: Expr,
  selfName: string,
  selfLevels: Level[],
  scope: string[],
  nsScope: string[],
  levelParams: Name[],
): Fmt | null {
  if (t.kind === "forallE") {
    const argSP = buildStrictPos(t.type, selfName, selfLevels, scope, nsScope, levelParams);
    if (!argSP) return null;
    const y = freshVar([...scope, ...nsScope]);
    const ny = freshVar([y, ...scope, ...nsScope]);
    const bodyCS = buildCtorSpine(
      t.body,
      selfName,
      selfLevels,
      [y, ...scope],
      [ny, ...nsScope],
      levelParams,
    );
    if (!bodyCS) return null;
    return app(atom("ctor-spine/arg"), argSP, lam(y, lam(ny, bodyCS)));
  }
  const result = buildAppliesSelf(t, selfName, selfLevels);
  return result ? app(atom("ctor-spine/result"), result) : null;
}

// ---------------------------------------------------------------------------
// Decide-then-refute helper for safe/narrow fail-on-purpose
// ---------------------------------------------------------------------------

// Evaluate a closed (param-free) level to its concrete universe number, or
// null if any level parameter appears (then we can't decide it numerically).
function evalClosedLevel(l: Level): number | null {
  switch (l.kind) {
    case "zero":
      return 0;
    case "param":
      return null;
    case "succ": {
      const a = evalClosedLevel(l.arg);
      return a === null ? null : a + 1;
    }
    case "max": {
      const a = evalClosedLevel(l.l);
      const b = evalClosedLevel(l.r);
      return a === null || b === null ? null : Math.max(a, b);
    }
    case "imax": {
      const b = evalClosedLevel(l.r);
      if (b === null) return null;
      if (b === 0) return 0;
      const a = evalClosedLevel(l.l);
      return a === null ? null : Math.max(a, b);
    }
  }
}

// True only when `a` and `b` are both concrete closed sorts at *different*
// universe levels — i.e. the obligation `defeq a b _` is provably false, not
// merely unproven. Used to emit a genuine refutation (failOnPurpose) rather
// than a HOLE. Conservative: returns false whenever either side is open or
// non-sort, so it can never false-reject a dischargeable obligation.
export function provablyDistinctSorts(a: Expr, b: Expr): boolean {
  if (a.kind !== "sort" || b.kind !== "sort") return false;
  const la = evalClosedLevel(a.level);
  const lb = evalClosedLevel(b.level);
  return la !== null && lb !== null && la !== lb;
}

// ---------------------------------------------------------------------------
// `field-universes-ok-skip-params N T UInd` builder (§3.2 / §3.5)
// ---------------------------------------------------------------------------
//
// Strategy: walk T's Π chain.
//
//   * For the first `nParams` binders (the inductive's params + indices,
//     re-bound on the ctor), emit `field-universes-ok-skip-params/skip`
//     and recurse under a fresh `(x : expr) (h : defeq x x A)` HOAS pair.
//   * For each subsequent binder (a real field), emit `field-universes-
//     ok/forall <domProof> <mleq> ([x][h] body)`, where:
//       - `domProof : defeq A A (esort UA)` comes from `synthRec` on A
//         (falling back to `reduceToSort` if A's synthesized type isn't
//         literally a sort).
//       - `mleq : mleq UA UInd 0` comes from `proveMleq`.
//   * The walk terminates at the first non-forall expression (the result
//     type — the inductive applied to params/indices/fields).  Emit
//     `field-universes-ok/done <not-forall/<kind>>`.
//
// `nParams` here = inductive's `numParams + numIndices` (total leading-Π
// count), matching the indt payload `count-leading-foralls` pins via
// `declared/ok-indt`.  The generator computes this from the parent
// inductive's IR.

function notForallAtom(t: Expr): Fmt | null {
  switch (t.kind) {
    case "sort":
      return atom("not-forall/sort");
    case "const":
      return atom("not-forall/const");
    case "app":
      return atom("not-forall/app");
    case "lam":
      return atom("not-forall/lam");
    case "proj":
      return atom("not-forall/proj");
    case "natLit":
      return atom("not-forall/nat");
    case "strLit":
      return atom("not-forall/str");
    case "forallE":
    case "bvar":
    case "letE":
      return null;
  }
}

// Helper: build the field-universes-ok proof for the residual Π chain
// (after skip-params has consumed the first nParams binders).  `scope`
// is the synth-side Hyp chain accumulated under the skipped binders.
function buildFieldUniversesOk(
  t: Expr,
  uInd: Level,
  scope: Hyp[],
  used: string[],
  envMap: EnvMap,
): Fmt | null {
  if (t.kind !== "forallE") {
    const nf = notForallAtom(t);
    if (nf === null) return null;
    return app(atom("field-universes-ok/done"), nf);
  }
  // Step 1: defeq A A (esort UA).  synthRec gives `defeq A A (synth.ty)`;
  // if synth.ty isn't a sort, whnf-step it to one.
  const rA = synthRec(t.type, scope, used, envMap);
  if (!rA) return null;
  let domProof = rA.proof;
  let uA = sortLevel(rA.ty);
  if (uA === null) {
    const r = reduceToSort(rA.ty, rA.proof, envMap, scope, used);
    if (!r) return null;
    domProof = r.proof;
    uA = r.level;
  }
  // Step 2: mleq UA UInd 0.
  // The TCB rule is `mleq (limax UA UInd) UInd 0` — Lean's actual
  // `imax`-form of the field-universe constraint, which gives Prop
  // impredicativity for free (Eq.refl's polymorphic field is fine since
  // imax u 0 = 0 ≤ 0).  See tcb.elf §field-universes-ok for the
  // rationale.
  const imaxLevel: Level = { kind: "imax", l: uA, r: uInd };
  const mleqProof = proveMleq(imaxLevel, uInd, 0);
  if (mleqProof === null) return null;
  // Step 3: introduce HOAS binders for the field, recurse on body.
  const x = freshVar(used);
  const usedX = [x, ...used];
  const h = freshHyp(usedX);
  const usedH = [h, ...usedX];
  const body = buildFieldUniversesOk(
    t.body,
    uInd,
    [{ hyp: h, ty: t.type }, ...scope],
    usedH,
    envMap,
  );
  if (body === null) return null;
  return app(
    atom("field-universes-ok/forall"),
    domProof,
    mleqProof,
    lam(x, lam(h, body)),
  );
}

// ---------------------------------------------------------------------------
// `dkind-ok/irec` premises (§3.1): enum-rec-type + le-eligible
// ---------------------------------------------------------------------------
//
// `dkind-ok/irec` (post-§3.1) requires the recursor's stored type T to (a)
// match the canonical schema for its inductive (via `enum-rec-type`) and
// (b) satisfy Lean's large-elimination restriction (via `le-eligible`).
// Phase 1 supports only non-parametric inductives: `enum-rec-type T IndN
// lnil Ctors U` requires FooLvls = lnil, so parametric inductives (Eq,
// List, …) have no witness and their recursors decline.  This is a
// completeness regression on the corpus but closes the recursor-type
// soundness gaps.

// Structural witness for `enum-rec-body M Body FooName lnil Ctors`,
// where `Body` is the body of an enum recursor's type under the bound
// motive M.  Walks the chain of minor premises (one per ctor in cidx
// order) and terminates at `∀ t : Foo, M t`.  For each ctor we emit
// `enum-rec-body/minor-Nf` where N is the ctor's field count; for
// N ≥ 1 we synthesize `defeq A_i A_i (esort UA_i)` for each field
// type using the env map.  The translator emits Body's expr by
// substitution; here we just emit the structural witness.
//
// Returns null if a field's domain type can't be synthesized to a
// sort (e.g. dependent fields whose type mentions earlier args — not
// yet supported by the Stage-2 LF rules).
function buildEnumRecBody(
  ctors: NonNullable<EnvEntry["recursorOf"]>["ctors"],
  used: string[],
  envMap: EnvMap,
): Fmt | null {
  if (ctors.length === 0) {
    return atom("enum-rec-body/done");
  }
  const c = ctors[0]!;
  const fieldTypes = ctorFieldTypes(c.type, c.numFields);
  if (fieldTypes === null) return null;
  // For non-dependent fields, each A_i is a closed expression: we
  // synthesize `defeq A_i A_i (esort UA_i)` against the empty scope.
  // For dependent fields this would need a per-field accumulating
  // scope, which Stage 2 doesn't support.
  const domProofs: Fmt[] = [];
  for (const a of fieldTypes) {
    const rA = synthRec(a, [], used, envMap);
    if (rA === null) return null;
    let dom = rA.proof;
    let uA = sortLevel(rA.ty);
    if (uA === null) {
      const r = reduceToSort(rA.ty, rA.proof, envMap, [], used);
      if (r === null) return null;
      dom = r.proof;
      uA = r.level;
    }
    domProofs.push(dom);
  }
  // Each minor (regardless of field count) binds ONE motive m, whose
  // type is `∀ a_1...a_n, M (c a_1...a_n)`.  The field binders live
  // inside that type, not as separate minor binders.
  const m = freshVar(used);
  const usedM = [m, ...used];
  const hm = freshHyp(usedM);
  const usedH = [hm, ...usedM];
  const rest = buildEnumRecBody(ctors.slice(1), usedH, envMap);
  if (rest === null) return null;
  const inner: Fmt = lam(m, lam(hm, rest));
  const ruleName =
    c.numFields === 0
      ? "enum-rec-body/minor"
      : `enum-rec-body/minor-${c.numFields}f`;
  return app(atom(ruleName), ...domProofs, inner);
}

// Peel `numFields` leading binders off a ctor's type; return each
// binder's domain.  Returns null if the type has fewer than
// `numFields` leading Π's.  For non-dependent fields the domains are
// closed expressions; for dependent fields the i-th domain may
// contain bvars referring to earlier args, which this helper does
// NOT close over — Stage 2 only handles closed (non-dependent)
// fields, and the downstream synthRec call will fail cleanly if a
// field actually depends on its predecessors.
function ctorFieldTypes(t: Expr, numFields: number): Expr[] | null {
  const out: Expr[] = [];
  let cur = t;
  for (let i = 0; i < numFields; i++) {
    if (cur.kind !== "forallE") return null;
    out.push(cur.type);
    cur = cur.body;
  }
  return out;
}

// True if any field type in the ctor's leading Π chain (up to
// numFields binders) mentions the inductive `indName` as a `const`
// reference.  Used to gate Stage-2 enum recognition: recursive
// ctors (Nat.succ : Nat → Nat, ...) need an IH binder per recursive
// field, which Stage 2's `enum-rec-body/minor-Nf` rules don't
// emit — exclude them so they decline cleanly (🩹) rather than
// emitting a witness that fails to typecheck (❌).
function ctorHasRecursiveField(t: Expr, numFields: number, indName: string): boolean {
  const fields = ctorFieldTypes(t, numFields);
  if (fields === null) return true; // shape-broken → conservatively recursive
  for (const f of fields) {
    if (exprMentionsConst(f, indName)) return true;
  }
  return false;
}

function exprMentionsConst(e: Expr, name: string): boolean {
  switch (e.kind) {
    case "const":
      return nameToString(e.name) === name;
    case "app":
      return exprMentionsConst(e.fn, name) || exprMentionsConst(e.arg, name);
    case "lam":
    case "forallE":
      return exprMentionsConst(e.type, name) || exprMentionsConst(e.body, name);
    case "letE":
      return (
        exprMentionsConst(e.type, name) ||
        exprMentionsConst(e.value, name) ||
        exprMentionsConst(e.body, name)
      );
    case "proj":
      return exprMentionsConst(e.struct, name);
    case "sort":
    case "bvar":
    case "natLit":
    case "strLit":
      return false;
  }
}

// Structural witness for `enum-rec-type T IndN lnil Ctors U`.  The rule's
// single constructor `enum-rec-type/intro` takes an enum-rec-body
// derivation under the motive binder + its typing hypothesis.
export function buildEnumRecType(
  ctors: NonNullable<EnvEntry["recursorOf"]>["ctors"],
  envMap: EnvMap,
): Fmt | null {
  const M = freshVar([]);
  const usedM = [M];
  const hM = freshHyp(usedM);
  const usedH = [hM, ...usedM];
  const body = buildEnumRecBody(ctors, usedH, envMap);
  if (body === null) return null;
  return app(atom("enum-rec-type/intro"), lam(M, lam(hM, body)));
}

// Structural witness for `le-eligible UInd Ctors U`.  Pattern-matches on
// Ctors first (subsingleton cases need no mleq), then if ≥2 ctors decides
// between `non-prop` (UInd ≥ 1) and `prop-prop` (UInd ≡ 0 ∧ U ≡ 0) via
// `proveMleq` (each call's offset is concrete = 0).
//
// Returns null when neither rule's premises can be proved — e.g.
// non-Prop UInd that's not statically ≥ 1 (parametric), or ≥2-ctor Prop
// where U is statically non-Prop (the large-elim attack).  Null → HOLE →
// freeze rejects → the recursor declines.  That's exactly the desired
// soundness behavior.
export function buildLeEligible(uInd: Level, numCtors: number, u: Level): Fmt | null {
  if (numCtors <= 1) {
    return atom(numCtors === 0 ? "le-eligible/cnil" : "le-eligible/csingle");
  }
  // ≥2 ctors.  Try non-prop first: mleq 1 UInd 0.
  const one: Level = { kind: "succ", arg: { kind: "zero" } };
  const zero: Level = { kind: "zero" };
  const nonPropProof = proveMleq(one, uInd, 0);
  if (nonPropProof !== null) {
    return app(atom("le-eligible/non-prop"), nonPropProof);
  }
  // Fall back to prop-prop: UInd ≡ 0 ∧ U ≡ 0 (both via two-sided mleq).
  const uIndLeZ = proveMleq(uInd, zero, 0);
  const zLeUInd = proveMleq(zero, uInd, 0);
  const uLeZ = proveMleq(u, zero, 0);
  const zLeU = proveMleq(zero, u, 0);
  if (uIndLeZ === null || zLeUInd === null || uLeZ === null || zLeU === null) {
    return null;
  }
  return app(atom("le-eligible/prop-prop"), uIndLeZ, zLeUInd, uLeZ, zLeU);
}

// Build the `declared <rec> _ (irec <ind>)` witness inline, by way of the
// TCB's `rec-derived-declared (rec-derived/enum ...)` chain.  Called from
// synthRec's const case when the name is a recursor.  Returns null if the
// le-eligible witness can't be constructed (the recursor's claimed motive
// universe doesn't satisfy Lean's elimination-universe restriction).
function buildRecursorDeclared(
  rec: NonNullable<EnvEntry["recursorOf"]>,
  envMap: EnvMap,
): Fmt | null {
  const ert = buildEnumRecType(rec.ctors, envMap);
  if (ert === null) return null;
  const lee = buildLeEligible(rec.indUInd, rec.ctors.length, rec.motiveU);
  if (lee === null) return null;
  const recDerived = app(
    atom("rec-derived/enum"),
    atom(rec.indMangleName + "/decl"),
    atom(rec.indMangleName + "/rec-name"),
    ert,
    atom(rec.indMangleName + "/eisl"),
    lee,
  );
  return app(
    atom("rec-derived-declared"),
    recDerived,
    atom(rec.indMangleName + "/rec-name"),
  );
}

export function buildFieldUniverses(
  t: Expr,
  // nParams unused under the no-skip-params design — kept in the
  // signature for backward compatibility with `Prover.fieldUniverses`
  // callers.  See tcb.elf §field-universes-ok for why we walk every
  // leading binder rather than skipping NParams of them.
  _nParams: number,
  uInd: Level,
  envMap: EnvMap,
): Fmt | null {
  return buildFieldUniversesOk(t, uInd, [], [], envMap);
}
