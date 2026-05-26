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
// Build a proof of `lvl-eq a b` from the lvl-eq rules in tcb.elf. Directed
// (no symm/trans search): match the identities, else recurse through the
// congruences. Returns null when no rule applies (→ the obligation stays a
// HOLE, never a wrong proof).

function sortLevel(e: Expr): Level | null {
  return e.kind === "sort" ? e.level : null;
}

export function proveLvlEq(a: Level, b: Level): Fmt | null {
  if (levelEq(a, b)) return atom("lvl-eq/refl");

  // lvl-eq/imax-zero : lvl-eq (limax L lzero) lzero.
  if (a.kind === "imax" && a.r.kind === "zero" && b.kind === "zero") {
    return atom("lvl-eq/imax-zero");
  }
  // lvl-eq/imax-idem : lvl-eq (limax L L) L.
  if (a.kind === "imax" && levelEq(a.l, a.r) && levelEq(b, a.l)) {
    return atom("lvl-eq/imax-idem");
  }
  // lvl-eq/max-idem : lvl-eq (lmax L L) L.
  if (a.kind === "max" && levelEq(a.l, a.r) && levelEq(b, a.l)) {
    return atom("lvl-eq/max-idem");
  }
  // lvl-eq/max-zero-l : lvl-eq (lmax lzero L) L.
  if (a.kind === "max" && a.l.kind === "zero" && levelEq(b, a.r)) {
    return atom("lvl-eq/max-zero-l");
  }
  // lvl-eq/max-zero-r : lvl-eq (lmax L lzero) L.
  if (a.kind === "max" && a.r.kind === "zero" && levelEq(b, a.l)) {
    return atom("lvl-eq/max-zero-r");
  }
  // lvl-eq/lsucc-cong : lvl-eq L1 L2 -> lvl-eq (lsucc L1) (lsucc L2).
  if (a.kind === "succ" && b.kind === "succ") {
    const sub = proveLvlEq(a.arg, b.arg);
    return sub && app(atom("lvl-eq/lsucc-cong"), sub);
  }
  // lvl-eq/limax-cong : congruence on both arguments.
  if (a.kind === "imax" && b.kind === "imax") {
    const l = proveLvlEq(a.l, b.l);
    const r = proveLvlEq(a.r, b.r);
    return l && r && app(atom("lvl-eq/limax-cong"), l, r);
  }
  // lvl-eq/lmax-cong : congruence on both arguments.
  if (a.kind === "max" && b.kind === "max") {
    const l = proveLvlEq(a.l, b.l);
    const r = proveLvlEq(a.r, b.r);
    return l && r && app(atom("lvl-eq/lmax-cong"), l, r);
  }
  return null;
}

// --- type coercion ------------------------------------------------------
//
// Given a proof of `defeq E E from`, return a wrapper producing a proof of
// `defeq E E to`. Identity when the types are syntactically equal; for two
// sorts, retype via defeq/conv + defeq/sort-eq using a lvl-eq derivation.
// (Only sort-to-sort coercion is needed in the closed fragment.)

export function bridge(from: Expr, to: Expr): ((pf: Fmt) => Fmt) | null {
  if (exprEq(from, to)) return (pf) => pf;
  const lf = sortLevel(from);
  const lt = sortLevel(to);
  if (lf && lt) {
    const le = proveLvlEq(lf, lt);
    if (!le) return null;
    return (pf) => app(atom("defeq/conv"), app(atom("defeq/sort-eq"), le), pf);
  }
  return null;
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
      return { ty: h.ty, proof: atom(h.hyp) };
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
