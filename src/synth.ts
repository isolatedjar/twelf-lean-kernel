// synth.ts — closed sort/Pi/λ type-synthesizer for RealProver.
//
// UNTRUSTED. Like prover.ts, nothing here is part of the trusted base: the
// generator only consumes the `Fmt` proof terms produced here, and validates
// every atom/binder (ppFmt in generate-twelf.ts). This module discharges the
// "closed fragment" of type checking — declarations whose type and value are
// built only from sorts, Π-types, λ-abstractions, and bound variables (no
// constants, reduction, or inductives). Anything outside the fragment yields
// `null` (→ a HOLE), so it can only ever turn 🩹 into ✅, never regress.

import { freshVar } from "./render.ts";
import type { Expr, Fmt, Level, Name } from "./shared.ts";
import { app, atom, lam, nameToString } from "./shared.ts";

const ANON: Name = { kind: "anon" };

// --- structural equality (alpha: binder names ignored) ------------------

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

// de Bruijn shift: lift free variables (index >= cutoff) by `by`. Used to bring
// a binder's stored type into the scope of a deeper bound-variable reference.
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

// --- level → Fmt (the one place a level is emitted as a proof term) ------
//
// Mirrors lfLevel (render.ts) but builds an Fmt tree rather than text, so the
// generator's ppFmt validator sees individual atoms/apps. Only used for the
// type-wf `sort` field. Level params render as de Bruijn `(lvar i)` data,
// matching withLevelParams/lidxLit in generate-twelf.ts.

function lidxFmt(i: number): Fmt {
  let acc = atom("liz");
  for (let k = 0; k < i; k++) acc = app(atom("lis"), acc);
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

// --- directed lvl-eq derivation -----------------------------------------
//
// Build a proof of `lvl-eq a b` from the lvl-eq rules in tcb.elf. Directed:
// reduce each side toward normal form (reduceLevel/stepLevel), joining the
// chains with lvl-eq/trans (and lvl-eq/symm for the `to` side), then fall back
// to structural congruence. Returns null when no rule applies (→ the obligation
// stays a HOLE, never a wrong proof).
//
// NOTE: this is a deliberately incomplete stopgap, NOT a decision procedure —
// both this and the underlying tcb.elf `lvl-eq` family (an ad-hoc identity set)
// are slated for replacement by a complete treatment (cf. lean4lean / mm0-lean).

function sortLevel(e: Expr): Level | null {
  return e.kind === "sort" ? e.level : null;
}

// One-step top-level reduction; each rule corresponds to an lvl-eq constructor
// in tcb.elf. Returns null when no top-level rule applies.
function reduceLevel(l: Level): { result: Level; proof: Fmt } | null {
  if (l.kind === "imax" && l.r.kind === "zero") {
    return { result: { kind: "zero" }, proof: atom("lvl-eq/imax-zero") };
  }
  if (l.kind === "imax" && l.r.kind === "succ") {
    return { result: { kind: "max", l: l.l, r: l.r }, proof: atom("lvl-eq/imax-succ") };
  }
  if (l.kind === "imax" && levelEq(l.l, l.r)) {
    return { result: l.l, proof: atom("lvl-eq/imax-idem") };
  }
  if (l.kind === "max" && levelEq(l.l, l.r)) {
    return { result: l.l, proof: atom("lvl-eq/max-idem") };
  }
  if (l.kind === "max" && l.l.kind === "zero") {
    return { result: l.r, proof: atom("lvl-eq/max-zero-l") };
  }
  if (l.kind === "max" && l.r.kind === "zero") {
    return { result: l.l, proof: atom("lvl-eq/max-zero-r") };
  }
  if (l.kind === "max" && l.l.kind === "succ" && l.r.kind === "succ") {
    return {
      result: { kind: "succ", arg: { kind: "max", l: l.l.arg, r: l.r.arg } },
      proof: atom("lvl-eq/max-succ"),
    };
  }
  return null;
}

// One-step reduction at any position, wrapping a sub-position step in the
// matching congruence rule. Returns null only when `l` is in normal form.
function stepLevel(l: Level): { result: Level; proof: Fmt } | null {
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
        proof: app(atom("lvl-eq/lsucc-cong"), inner.proof),
      };
    }
    case "max": {
      const ls = stepLevel(l.l);
      if (ls !== null) {
        return {
          result: { kind: "max", l: ls.result, r: l.r },
          proof: app(atom("lvl-eq/lmax-cong"), ls.proof, atom("lvl-eq/refl")),
        };
      }
      const rs = stepLevel(l.r);
      if (rs !== null) {
        return {
          result: { kind: "max", l: l.l, r: rs.result },
          proof: app(atom("lvl-eq/lmax-cong"), atom("lvl-eq/refl"), rs.proof),
        };
      }
      return null;
    }
    case "imax": {
      const ls = stepLevel(l.l);
      if (ls !== null) {
        return {
          result: { kind: "imax", l: ls.result, r: l.r },
          proof: app(atom("lvl-eq/limax-cong"), ls.proof, atom("lvl-eq/refl")),
        };
      }
      const rs = stepLevel(l.r);
      if (rs !== null) {
        return {
          result: { kind: "imax", l: l.l, r: rs.result },
          proof: app(atom("lvl-eq/limax-cong"), atom("lvl-eq/refl"), rs.proof),
        };
      }
      return null;
    }
  }
}

export function proveLvlEq(a: Level, b: Level, depth = 0): Fmt | null {
  if (depth > 12) return null;
  if (levelEq(a, b)) return atom("lvl-eq/refl");

  // Reduce `a` one step and recurse: lvl-eq/trans of the step with the rest.
  const ra = stepLevel(a);
  if (ra !== null) {
    const rest = proveLvlEq(ra.result, b, depth + 1);
    if (rest !== null) return app(atom("lvl-eq/trans"), ra.proof, rest);
  }
  // Reduce `b` one step and recurse, flipping the step via lvl-eq/symm.
  const rb = stepLevel(b);
  if (rb !== null) {
    const rest = proveLvlEq(a, rb.result, depth + 1);
    if (rest !== null) {
      return app(atom("lvl-eq/trans"), rest, app(atom("lvl-eq/symm"), rb.proof));
    }
  }
  // Structural congruence (when neither side reduces but heads agree).
  if (a.kind === "succ" && b.kind === "succ") {
    const sub = proveLvlEq(a.arg, b.arg, depth + 1);
    return sub && app(atom("lvl-eq/lsucc-cong"), sub);
  }
  if (a.kind === "imax" && b.kind === "imax") {
    const l = proveLvlEq(a.l, b.l, depth + 1);
    const r = proveLvlEq(a.r, b.r, depth + 1);
    return l && r && app(atom("lvl-eq/limax-cong"), l, r);
  }
  if (a.kind === "max" && b.kind === "max") {
    const l = proveLvlEq(a.l, b.l, depth + 1);
    const r = proveLvlEq(a.r, b.r, depth + 1);
    return l && r && app(atom("lvl-eq/lmax-cong"), l, r);
  }
  return null;
}

// --- type coercion ------------------------------------------------------
//
// `bridgeProof(from, to)` builds a proof of `defeq from to (esort _)` — that the
// two TYPES are definitionally equal at some sort. Two sorts: defeq/sort-eq over
// a lvl-eq derivation. Two Π-types: defeq/forall congruence — bridge the domains,
// then the codomains under a fresh `defeq x x from.type` hypothesis (the
// hypothesis is typed at the left/`from` domain, per defeq/forall in tcb.elf).
// `bridge(from, to)` turns that into a wrapper retyping a `defeq E E from` proof
// into `defeq E E to` via defeq/conv. Anything else → null (stays a HOLE).

function bridgeProof(from: Expr, to: Expr, used: string[], depth = 0): Fmt | null {
  if (depth > 6) return null;

  const lf = sortLevel(from);
  const lt = sortLevel(to);
  if (lf && lt) {
    const le = proveLvlEq(lf, lt);
    return le && app(atom("defeq/sort-eq"), le);
  }

  if (from.kind === "forallE" && to.kind === "forallE") {
    const dom = bridgeProof(from.type, to.type, used, depth + 1);
    if (!dom) return null;
    const x = freshVar(used);
    const usedX = [x, ...used];
    const h = freshHyp(usedX);
    const body = bridgeProof(from.body, to.body, [h, ...usedX], depth + 1);
    if (!body) return null;
    return app(atom("defeq/forall"), dom, lam(x, lam(h, body)));
  }

  return null;
}

export function bridge(from: Expr, to: Expr): ((pf: Fmt) => Fmt) | null {
  if (exprEq(from, to)) return (pf) => pf;
  const p = bridgeProof(from, to, []);
  if (!p) return null;
  return (pf) => app(atom("defeq/conv"), p, pf);
}

// --- type synthesis -----------------------------------------------------
//
// synth(e, scope) returns the inferred type of `e` (as IR, for further
// synthesis) together with an Fmt proving `defeq e e ty`, or null if `e`
// falls outside the closed fragment. `scope` holds, innermost-first, the
// defeq hypothesis variable and binder type for each Π/λ in view; a bound
// variable's proof is exactly its hypothesis.

interface Hyp {
  hyp: string; // name of the `defeq x x A` hypothesis bound at this binder
  ty: Expr; // the binder's type A
}

interface Synthed {
  ty: Expr;
  proof: Fmt;
}

// Used names = every LF-bound identifier in scope (both the `x` term vars and
// the `h` hypothesis vars), so fresh names collide with neither.
function freshHyp(used: string[]): string {
  if (!used.includes("h")) return "h";
  for (let i = 1; ; i++) {
    const c = `h${i}`;
    if (!used.includes(c)) return c;
  }
}

function synthRec(e: Expr, scope: Hyp[], used: string[]): Synthed | null {
  switch (e.kind) {
    case "sort":
      return {
        ty: { kind: "sort", level: { kind: "succ", arg: e.level } },
        proof: atom("defeq/sort-refl"),
      };

    case "bvar": {
      const h = scope[e.deBruijn];
      if (h === undefined) return null;
      // The stored type was captured `e.deBruijn + 1` binders shallower; shift
      // its free variables into the current (deeper) scope.
      return { ty: shift(h.ty, e.deBruijn + 1), proof: atom(h.hyp) };
    }

    case "forallE": {
      const rA = synthRec(e.type, scope, used);
      if (!rA) return null;
      const u = sortLevel(rA.ty);
      if (!u) return null;
      const x = freshVar(used);
      const usedX = [x, ...used];
      const h = freshHyp(usedX);
      const usedH = [h, ...usedX];
      const rB = synthRec(e.body, [{ hyp: h, ty: e.type }, ...scope], usedH);
      if (!rB) return null;
      const v = sortLevel(rB.ty);
      if (!v) return null;
      return {
        ty: { kind: "sort", level: { kind: "imax", l: u, r: v } },
        proof: app(atom("defeq/forall"), rA.proof, lam(x, lam(h, rB.proof))),
      };
    }

    case "lam": {
      const rA = synthRec(e.type, scope, used);
      if (!rA) return null;
      if (!sortLevel(rA.ty)) return null;
      const x = freshVar(used);
      const usedX = [x, ...used];
      const h = freshHyp(usedX);
      const usedH = [h, ...usedX];
      const rB = synthRec(e.body, [{ hyp: h, ty: e.type }, ...scope], usedH);
      if (!rB) return null;
      return {
        ty: { kind: "forallE", name: ANON, type: e.type, body: rB.ty },
        proof: app(atom("defeq/lam"), rA.proof, lam(x, lam(h, rB.proof))),
      };
    }

    default:
      // const, app, proj, letE, natLit, strLit — outside the fragment.
      return null;
  }
}

export function synth(e: Expr): Synthed | null {
  return synthRec(e, [], []);
}

export function synthSort(e: Expr): Level | null {
  const r = synth(e);
  return r ? sortLevel(r.ty) : null;
}
