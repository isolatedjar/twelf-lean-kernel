#!/usr/bin/env -S node --experimental-strip-types
// generate-twelf.ts — the single, trusted Twelf generator.
//
// Reads a ParsedEnv JSON on stdin, emits a Twelf signature on stdout.
// Parameterized by a Prover (see shared.ts): for every proof obligation
// the generator raises, it asks the prover for an `Fmt` proof.
//   - prover returns Fmt  → `<const> : <type> = <proof>.`   (discharged; if
//                            the Fmt is `failOnPurpose`, the proof is the
//                            undeclared atom `fail-on-purpose`, which Twelf
//                            rejects → the env is rejected on purpose)
//   - prover returns null → `%%% HOLE` + `<const> : <type>.` (declared by
//                            fiat; rejected by %freeze in the full load)
//
//   .render.elf = this generator with the NullProver (every obligation a HOLE)
//   .full.elf   = this generator with makeRealProver(env)
//
// Because both files come from THIS generator, `.render.elf` structurally
// contains every fact `.full.elf` does — that is the adequacy property.
// The Prover (prover.ts) is untrusted; auditing shared.ts + parse.ts + this
// file suffices.

import { makeRealProver, NullProver } from "./prover.ts";
import { levelParamBindings, lfExpr, mangle, natLiteralsSeen } from "./render.ts";
import type {
  Decl,
  Expr,
  Fmt,
  IndType,
  Level,
  Name,
  ParsedEnv,
  Prover,
  TypeWfResult,
} from "./shared.ts";
import { nameToString, transformNamesFromJSON } from "./shared.ts";

// =====================================================================
// Output + Fmt pretty-printer (trusted, anti-injection)
// =====================================================================

const out: string[] = [];
function emit(s: string): void {
  out.push(s);
}

// Pretty-print an Fmt proof term.  Validates every atom and binder so an
// untrusted prover cannot smuggle a declaration terminator (`.`), whitespace,
// or a newline into the output: atoms are either Twelf identifiers (which use
// `/`, never `.`) or quoted string literals; binders are plain identifiers.
function ppFmt(f: Fmt): string {
  switch (f.kind) {
    case "atom": {
      const t = f.text;
      const okIdent = /^[A-Za-z0-9_/+*<>=~^!?-]+$/.test(t);
      const okString = /^"[^"\\\n]*"$/.test(t);
      if (!okIdent && !okString) {
        throw new Error(`Fmt atom rejected (possible injection): ${JSON.stringify(t)}`);
      }
      return t;
    }
    case "app":
      return `(${ppFmt(f.fn)} ${f.args.map(ppFmt).join(" ")})`;
    case "lam": {
      if (!/^[A-Za-z0-9_]+$/.test(f.binder)) {
        throw new Error(`Fmt binder rejected: ${JSON.stringify(f.binder)}`);
      }
      return `([${f.binder}] ${ppFmt(f.body)})`;
    }
  }
}

// =====================================================================
// Level-parameter helpers
// =====================================================================

// A de Bruijn level index as a unary `lidx` literal: liz, (lis liz), ...
function lidxLit(i: number): string {
  let acc = "liz";
  for (let k = 0; k < i; k++) acc = `(lis ${acc})`;
  return acc;
}

// The canonical formal level list for an `n`-parameter declaration:
// `(lcons (lvar liz) (lcons (lvar (lis liz)) ... lnil))`.  Used where a rule
// still takes an explicit `lvls` of the declaration's own parameters.
function formalLvls(n: number): string {
  let acc = "lnil";
  for (let i = n - 1; i >= 0; i--) acc = `(lcons (lvar ${lidxLit(i)}) ${acc})`;
  return acc;
}

// Bind each universe parameter to its de Bruijn level variable `(lvar i)` for
// the duration of `fn`.  Stored declarations are *schemas* over these `lvar`s
// (see tcb.elf), so every term the generator emits is ground — there are no
// `{u:lvl}` LF binders and instantiation happens at use sites in the TCB.
function withLevelParams<T>(params: Name[], fn: () => T): T {
  params.forEach((p, i) => {
    levelParamBindings.set(nameToString(p), `(lvar ${lidxLit(i)})`);
  });
  try {
    return fn();
  } finally {
    for (const p of params) levelParamBindings.delete(nameToString(p));
  }
}

// =====================================================================
// Obligation emission
// =====================================================================

// Emit a Twelf constant: a definition (`<const> : <type> = <term>.`) when
// `term` is non-null, or a declaration with a HOLE warning (`%%% HOLE` then
// `<const> : <type>.`) when it is null.
function emitDefn(constName: string, type: string, term: Fmt | null): void {
  if (term === null) {
    emit(`%%% HOLE`);
    emit(`${constName} : ${type}.`);
  } else {
    emit(`${constName} : ${type}`);
    emit(`   = ${ppFmt(term)}.`);
  }
  emit(``);
}

// Render a single proof obligation and return a reference to it for the
// enclosing `dkind-ok` witness.  `null` → a HOLE (a bare decl rejected by
// %freeze); an `Fmt` → a definition.  A prover that wants to reject the
// environment supplies the `failOnPurpose` Fmt as its proof; it flows
// through like any term and Twelf rejects it as an undeclared identifier
// (no special-casing).  Everything is ground: the obligation's type is a
// schema over `lvar`, so there are no level binders or lambdas.
function emitObligation(result: Fmt | null, constName: string, judgmentType: string): string {
  emitDefn(constName, judgmentType, result);
  return constName;
}

// Emit the type-wf obligation `defeq T T (esort U)`.
//
// For `thm` the kernel forces U = lzero (the type must be a Prop), so we emit
// the literal and no universe obligation.  Otherwise U is *synthesized* (the
// Sort that T inhabits — not in the NDJSON), so we emit it as its own
// obligation on `lvl`: `lvl` is freezable, so the universe HOLE is itself
// detectable.  (T may mention `lvar` schema variables; the obligation type
// stays ground because those are data, not LF binders.)
function emitTypeWf(result: TypeWfResult, mn: string, T: string, isThm: boolean): string {
  if (isThm) {
    const proof = result === null ? null : result.proof;
    return emitObligation(proof, `${mn}/type-wf`, `defeq ${T} ${T} (esort lzero)`);
  }
  const sortRef = emitObligation(result === null ? null : result.sort, `${mn}/type-wf-sort`, `lvl`);
  return emitObligation(
    result === null ? null : result.proof,
    `${mn}/type-wf`,
    `defeq ${T} ${T} (esort ${sortRef})`,
  );
}

// Emit the `ctor-positive` obligation for a constructor and return its name.
//
// SOUNDNESS BOUNDARY.  The proof is `ctor-positive/intro ([S] T_HOAS) <spine>`.
// The generator (trusted) computes T_HOAS itself — the ctor type with the
// inductive's self-reference `(econst IndName IndLevels)` abstracted to the
// bound `S` — via render.ts `lfExpr` with a SelfSubst.  The prover supplies
// ONLY the `<spine>` (a `ctor-spine T_HOAS` derivation).  Were the prover to
// supply T_HOAS, it could hide a negative self-occurrence in a closed (S-free)
// position and so fake positivity for a non-strictly-positive inductive (the
// `strict-pos/forall`/`strict-pos/no-occur` rules accept any closed domain,
// including one mentioning the self-constant).  By fixing T_HOAS here, Twelf
// checks the prover's spine against the *correct* abstraction, under which a
// negative occurrence makes `ctor-spine` uninhabited — so a bad spine can only
// produce a HOLE/reject, never an unsound acceptance.
function emitCtorPositive(
  prover: Prover,
  c: { type: Expr; induct: Name; levelParams: Name[] },
  indName: string,
  indLevels: Level[],
  mn: string,
  T: string,
): string {
  const posName = `${mn}/positivity`;
  const posType = `ctor-positive "${indName}" ${formalLvls(c.levelParams.length)} ${T}`;
  const spine = prover.ctorPositive({
    ctorType: c.type,
    indName: c.induct,
    indLevels,
    levelParams: c.levelParams,
  });
  // Compute the trusted T_HOAS body: render the ctor type, abstracting the
  // self-reference to S.  `selfStr` is the rendering of (econst IndName
  // IndLevels) in the current level-param scope; rendering is injective on
  // (name, levels), so the substitution targets exactly the self-reference.
  let hoasBody: string | null;
  try {
    const selfStr = lfExpr({ kind: "const", name: c.induct, us: indLevels }, []);
    hoasBody = lfExpr(c.type, [], { selfStr, varName: "S" });
  } catch {
    hoasBody = null;
  }
  if (spine === null || hoasBody === null) {
    emitDefn(posName, posType, null); // HOLE
    return posName;
  }
  emit(`${posName} : ${posType}`);
  emit(`   = (ctor-positive/intro ([S] ${hoasBody}) ${ppFmt(spine)}).`);
  emit(``);
  return posName;
}

// Emit a complete declaration: the open `name` reservation plus the closed
// `declared` definition that consumes it.
//
//   <mn>/name : name "<decl>" (is-decl T K).        (open family)
//   <mn>/decl : declared "<decl>" T K
//             = declared/ok <mn>/name <okWitness>.  (frozen family)
//
// `name` is open (`%thaw name`), so the reservation is a plain constant — not
// a HOLE — and `%unique name` (final-checks.elf) rejects any string reserved
// twice with conflicting meanings (duplicate declarations).  Because `T`/`K`
// are ground schemas over `lvar`, the reservation's codomain is ground and the
// seal mode-checks.  `declared` is *closed* with the single constructor
// `declared/ok`, so `<mn>/decl` must be a definition (allowed on a frozen
// family); its body bundles the name reservation with the `dkind-ok`
// well-formedness witness, which is where the proof obligations (and their
// HOLEs) live.
function emitDeclared(
  mn: string,
  declName: string,
  T: string,
  kExpr: string,
  okWitness: string,
): void {
  emit(`${mn}/name : name "${declName}" (is-decl ${T} ${kExpr}).`);
  emit(``);
  emit(`${mn}/decl : declared "${declName}" ${T} ${kExpr}`);
  emit(`   = declared/ok ${mn}/name ${okWitness}.`);
  emit(``);
}

function skip(reason: string): void {
  emit(`%%% SKIP: ${reason}`);
  emit(``);
}

// =====================================================================
// Per-declaration emission
// =====================================================================

// Render an expr to LF text; null if it can't be represented at all.
function tryLf(e: Expr): string | null {
  try {
    return lfExpr(e, []);
  } catch {
    return null;
  }
}

function generateDecl(prover: Prover, d: Decl): void {
  // Lean requires distinct universe-parameter names on every declaration; we
  // can't represent the distinctness constraint in the implicit-level encoding,
  // so any duplicate is outside our representable fragment → 🤷 SKIP.
  // (Inductive blocks store levelParams per-member, not at the block level.)
  if (d.kind !== "inductive") {
    const lpNames = d.levelParams.map(nameToString);
    if (new Set(lpNames).size < lpNames.length) {
      skip(
        `${d.kind} ${nameToString(d.name)} — duplicate universe parameter names [${lpNames.join(", ")}]`,
      );
      return;
    }
  }
  switch (d.kind) {
    case "def":
    case "opaque":
    case "thm":
      generateValDecl(prover, d);
      break;
    case "axiom":
      generateAxiom(prover, d);
      break;
    case "inductive":
      generateInductive(prover, d);
      break;
    case "quot":
      // Deferred: quot members carry a type on this
      // branch, but representing the Quot family + its kernel reductions is
      // its own task.  Declining keeps these tests 🤷 for now.
      skip(`quot ${nameToString(d.name)} (${d.quotKind}) — not yet represented`);
      break;
  }
}

function generateValDecl(prover: Prover, d: Decl & { kind: "def" | "opaque" | "thm" }): void {
  const declName = nameToString(d.name);
  const mn = mangle(d.name);
  withLevelParams(d.levelParams, () => {
    const T = tryLf(d.type);
    const V = tryLf(d.value);
    if (T === null || V === null) {
      skip(`${d.kind} ${declName} — type/value not representable in LF`);
      return;
    }
    emit(`%% ${d.kind} ${declName}`);

    const tw = emitTypeWf(
      prover.typeWellFormed({ type: d.type, levelParams: d.levelParams, isThm: d.kind === "thm" }),
      mn,
      T,
      d.kind === "thm",
    );
    const vt = emitObligation(
      prover.valueHasType({ value: d.value, type: d.type, levelParams: d.levelParams }),
      `${mn}/value-typed`,
      `defeq ${V} ${V} ${T}`,
    );

    const dkindCtor = d.kind === "def" ? "defn" : d.kind === "opaque" ? "opq" : "thm";
    const okCtor =
      d.kind === "def" ? "dkind-ok/defn" : d.kind === "opaque" ? "dkind-ok/opq" : "dkind-ok/thm";
    emitDeclared(mn, declName, T, `(${dkindCtor} ${V})`, `(${okCtor} ${tw} ${vt})`);
  });
}

function generateAxiom(prover: Prover, d: Decl & { kind: "axiom" }): void {
  const declName = nameToString(d.name);
  const mn = mangle(d.name);
  withLevelParams(d.levelParams, () => {
    const T = tryLf(d.type);
    if (T === null) {
      skip(`axiom ${declName} — type not representable in LF`);
      return;
    }
    emit(`%% axiom ${declName}`);
    const tw = emitTypeWf(
      prover.typeWellFormed({ type: d.type, levelParams: d.levelParams }),
      mn,
      T,
      false,
    );
    emitDeclared(mn, declName, T, `ax`, `(dkind-ok/ax ${tw})`);
  });
}

// =====================================================================
// Inductive pre-flight checks
// =====================================================================
//
// Soundness invariants Lean's kernel enforces on an inductive block that are
// NOT encoded in the LF signature (so Twelf can't see them). Once the prover
// can discharge `ends-in-sort`/`ctor-positive` and synth the recursor/ctor
// obligations, a malformed block would otherwise sail through (the missing
// check was previously masked by those obligations being HOLEs). These checks
// reproduce the translator-side rejections the old lean2lf.ts performed:
//   (a) numParams ≤ #leading Π binders of the type former        → 042
//   (b) ctor result applies the inductive to its param binders    → 043 / 044
//       in canonical order
//   (c) ctor result-type index args don't mention the inductive   → 046
//   (d) concrete ctor field universe ≤ inductive universe − 1     → 054
//   (e) a primitive recursor is named `<type>.rec`                → 124
//   (f) a Prop inductive with ≥2 ctors does not large-eliminate   → 127
//   plus: no duplicate universe-parameter names on any member     → 041
//
// On violation we SKIP (🤷): Twelf isn't checking the condition, so this is a
// translator-side decline, not a Twelf-verified rejection. All checks are
// conservative — they only fire on genuinely malformed blocks, never on a
// well-formed one.

// Count the leading Π binders of a type (the declaration "spine").
function countLeadingForalls(e: Expr): number {
  let n = 0;
  let cur = e;
  while (cur.kind === "forallE") {
    n++;
    cur = cur.body;
  }
  return n;
}

// Does any `const` subexpression of `e` carry the name `name`? Used for the
// index-occurrence check (c); name-only (ignores levels) so it's conservative.
function mentionsConst(e: Expr, name: string): boolean {
  switch (e.kind) {
    case "const":
      return nameToString(e.name) === name;
    case "app":
      return mentionsConst(e.fn, name) || mentionsConst(e.arg, name);
    case "lam":
    case "forallE":
      return mentionsConst(e.type, name) || mentionsConst(e.body, name);
    case "letE":
      return (
        mentionsConst(e.type, name) || mentionsConst(e.value, name) || mentionsConst(e.body, name)
      );
    case "proj":
      return mentionsConst(e.struct, name);
    default:
      return false; // bvar / sort / natLit / strLit
  }
}

// A chain of `succ` over `zero` as a number, else null (we don't reason about
// max/imax/param universes here).
function levelToNumber(l: Level): number | null {
  let n = 0;
  let cur = l;
  while (cur.kind === "succ") {
    cur = cur.arg;
    n++;
  }
  return cur.kind === "zero" ? n : null;
}

// The inductive's universe if its type signature ends in a concrete Sort.
function inductiveResultUniverse(t: Expr): Level | null {
  let cur = t;
  while (cur.kind === "forallE") cur = cur.body;
  return cur.kind === "sort" ? cur.level : null;
}

// The universe a recursor eliminates *into*: the Sort at the tail of the
// motive's type.  The recursor's type is
//   {params} (motive : {indices}{major} → Sort u) {minors} {indices} {major} → …
// so we skip `numParams` leading binders, take the next binder (the first
// motive), and read the Sort ending its Π-chain.  Returns null if the shape
// doesn't match (then we can't classify the elimination and stay conservative).
function motiveResultUniverse(recType: Expr, numParams: number): Level | null {
  let e = recType;
  for (let i = 0; i < numParams; i++) {
    if (e.kind !== "forallE") return null;
    e = e.body;
  }
  if (e.kind !== "forallE") return null; // the motive binder
  return inductiveResultUniverse(e.type);
}

// Checks (b), (c), (d) on a single ctor. Returns a mismatch reason or null.
function checkCtorStructure(
  ctorType: Expr,
  indName: string,
  indUniverse: Level | null,
  numParams: number,
  numFields: number,
): string | null {
  let e = ctorType;
  for (let i = 0; i < numParams; i++) {
    if (e.kind !== "forallE") {
      return `expected >= ${numParams + numFields} leading binders, found ${i}`;
    }
    e = e.body;
  }
  const indUnivN = indUniverse !== null ? levelToNumber(indUniverse) : null;
  for (let f = 0; f < numFields; f++) {
    if (e.kind !== "forallE") {
      return `expected >= ${numParams + numFields} leading binders, found ${numParams + f}`;
    }
    // (d) concrete-case field universe check.
    if (indUnivN !== null && indUnivN > 0 && e.type.kind === "sort") {
      const fieldLvlN = levelToNumber(e.type.level);
      if (fieldLvlN !== null && fieldLvlN + 1 > indUnivN) {
        return `field #${f + 1} has type Sort ${fieldLvlN} (lives at Sort ${fieldLvlN + 1}); inductive is at Sort ${indUnivN}`;
      }
    }
    e = e.body;
  }
  // e is the result type; decompose its application spine.
  const args: Expr[] = [];
  while (e.kind === "app") {
    args.unshift(e.arg);
    e = e.fn;
  }
  if (e.kind !== "const") {
    return `result-type head is not a constant (got ${e.kind})`;
  }
  // Wrong head: defer to Twelf — no `applies-self` rule fires on a bad head,
  // so ctor-positive can't be discharged and the obligation stays a HOLE.
  if (nameToString(e.name) !== indName) return null;
  if (args.length < numParams) {
    return `result-type has ${args.length} args, expected >= ${numParams}`;
  }
  // (b) param args must be the param binders, in canonical order.
  for (const [i, a] of args.slice(0, numParams).entries()) {
    const expected = numFields + numParams - 1 - i;
    if (a.kind !== "bvar" || a.deBruijn !== expected) {
      const got = a.kind === "bvar" ? `bvar(${a.deBruijn})` : a.kind;
      return `result-type param arg #${i + 1} should be bvar(${expected}), got ${got}`;
    }
  }
  // (c) index args must not mention the inductive.
  for (const [i, a] of args.slice(numParams).entries()) {
    if (mentionsConst(a, indName)) {
      return `result-type index arg #${i + 1} mentions the inductive "${indName}"`;
    }
  }
  return null;
}

function preflightInductiveReject(ind: Decl & { kind: "inductive" }): string | null {
  const dupLevels = (lps: Name[]): boolean => {
    const names = lps.map(nameToString);
    return new Set(names).size < names.length;
  };
  for (const t of ind.types) {
    if (dupLevels(t.levelParams)) {
      return `inductive ${nameToString(t.name)} — duplicate universe parameter names`;
    }
    if (t.numParams > countLeadingForalls(t.type)) {
      return `inductive ${nameToString(t.name)} — numParams=${t.numParams} exceeds the ${countLeadingForalls(t.type)} leading Π binders of its type`;
    }
  }
  for (const c of ind.ctors) {
    if (dupLevels(c.levelParams)) {
      return `ctor ${nameToString(c.name)} — duplicate universe parameter names`;
    }
    const indSpec = ind.types.find((t) => nameToString(t.name) === nameToString(c.induct));
    if (!indSpec) continue;
    const why = checkCtorStructure(
      c.type,
      nameToString(c.induct),
      inductiveResultUniverse(indSpec.type),
      c.numParams,
      c.numFields,
    );
    if (why !== null) return `ctor ${nameToString(c.name)} — ${why}`;
  }
  const typeNames = new Set(ind.types.map((t) => nameToString(t.name)));
  for (const r of ind.recursors) {
    if (dupLevels(r.levelParams)) {
      return `recursor ${nameToString(r.name)} — duplicate universe parameter names`;
    }
    // (e) a primitive recursor must be named `<type>.rec` for a type in the block.
    const rn = nameToString(r.name);
    const ok = rn.endsWith(".rec") && typeNames.has(rn.slice(0, -".rec".length));
    if (!ok) {
      return `recursor ${rn} — name is not <type>.rec for any type in the block`;
    }
  }
  // (f) Large-elimination gate.  A Prop (Sort 0) inductive may only eliminate
  // into Type if it is a subsingleton — at most one constructor (Lean also
  // requires that ctor's fields be propositions/indices, which we don't try to
  // verify structurally).  A Prop inductive with ≥2 constructors whose recursor
  // motive targets a universe other than Sort 0 is unsound (it would transport
  // a Prop case-distinction into Type).  The LF `dkind-ok/irec` rule checks only
  // that the recursor type is well-formed, so Twelf can't see this — we gate it
  // here.  Conservative: fires only when the inductive universe is concretely
  // Prop and the motive's target is concretely a non-Prop sort.
  for (const t of ind.types) {
    const indU = inductiveResultUniverse(t.type);
    if (indU === null || levelToNumber(indU) !== 0) continue; // only concrete Prop
    const tname = nameToString(t.name);
    const ctorCount = ind.ctors.filter((c) => nameToString(c.induct) === tname).length;
    if (ctorCount < 2) continue; // ≤1 ctor: may be a large-eliminating subsingleton
    const rec = ind.recursors.find((r) => nameToString(r.name) === `${tname}.rec`);
    if (!rec) continue;
    const motiveU = motiveResultUniverse(rec.type, rec.numParams);
    // motiveU.kind === "zero" → small elimination (into Prop), sound.  Anything
    // else (a concrete higher Sort, or a polymorphic Sort u) is large.
    if (motiveU !== null && motiveU.kind !== "zero") {
      return `recursor ${tname}.rec — large elimination (motive into a non-Prop sort) from a Prop inductive with ${ctorCount} constructors`;
    }
  }
  return null;
}

function generateInductive(prover: Prover, ind: Decl & { kind: "inductive" }): void {
  const reject = preflightInductiveReject(ind);
  if (reject !== null) {
    skip(reject);
    return;
  }
  // Type formers.
  for (const t of ind.types) {
    generateIndType(prover, t);
  }
  // Constructors.
  for (const c of ind.ctors) {
    const declName = nameToString(c.name);
    const mn = mangle(c.name);
    const indName = nameToString(c.induct);
    withLevelParams(c.levelParams, () => {
      const T = tryLf(c.type);
      if (T === null) {
        skip(`ctor ${declName} — type not representable in LF`);
        return;
      }
      const indLevels: Level[] = c.levelParams.map((name) => ({ kind: "param", name }));
      emit(`%% ctor ${declName} (of ${indName})`);
      const tw = emitTypeWf(
        prover.typeWellFormed({ type: c.type, levelParams: c.levelParams }),
        mn,
        T,
        false,
      );
      const cp = emitCtorPositive(prover, c, indName, indLevels, mn, T);
      emitDeclared(mn, declName, T, `ctor`, `(dkind-ok/ctor ${tw} ${cp})`);
    });
  }
  // Recursors.
  for (const r of ind.recursors) {
    const declName = nameToString(r.name);
    const mn = mangle(r.name);
    withLevelParams(r.levelParams, () => {
      const T = tryLf(r.type);
      if (T === null) {
        skip(`recursor ${declName} — type not representable in LF`);
        return;
      }
      emit(`%% recursor ${declName}`);
      const tw = emitTypeWf(
        prover.typeWellFormed({ type: r.type, levelParams: r.levelParams }),
        mn,
        T,
        false,
      );
      emitDeclared(mn, declName, T, `irec`, `(dkind-ok/irec ${tw})`);
    });
  }
}

function generateIndType(prover: Prover, t: IndType): void {
  const declName = nameToString(t.name);
  const mn = mangle(t.name);
  withLevelParams(t.levelParams, () => {
    const T = tryLf(t.type);
    if (T === null) {
      skip(`inductive ${declName} — type not representable in LF`);
      return;
    }
    emit(`%% inductive ${declName}`);
    const tw = emitTypeWf(
      prover.typeWellFormed({ type: t.type, levelParams: t.levelParams }),
      mn,
      T,
      false,
    );
    const eis = emitObligation(
      prover.endsInSort({ type: t.type, levelParams: t.levelParams }),
      `${mn}/ends-in-sort`,
      `ends-in-sort ${T}`,
    );
    emitDeclared(mn, declName, T, `indt`, `(dkind-ok/indt ${tw} ${eis})`);
  });
}

// =====================================================================
// Top-level
// =====================================================================

export function generateTwelf(prover: Prover, env: ParsedEnv): string {
  out.length = 0;
  natLiteralsSeen.clear();
  levelParamBindings.clear();

  for (const decl of env.decls) {
    try {
      generateDecl(prover, decl);
    } catch (e: unknown) {
      const msg = e instanceof Error ? e.message : String(e);
      skip(`${(decl as { kind?: string }).kind ?? "decl"} — generator error: ${msg}`);
    }
  }

  // Prelude: %solve witnesses for the n >= 0 premise of every nat literal.
  const prelude: string[] = [];
  if (natLiteralsSeen.size > 0) {
    for (const n of natLiteralsSeen) prelude.push(`%solve nonneg_${n} : ${n} >= 0.`);
    prelude.push(``);
  }
  return [...prelude, ...out].join("\n") + "\n";
}

async function readAllStdin(): Promise<string> {
  const chunks: Buffer[] = [];
  for await (const chunk of process.stdin) chunks.push(chunk as Buffer);
  return Buffer.concat(chunks).toString("utf8");
}

async function main(): Promise<void> {
  const which = process.argv.includes("--prover")
    ? process.argv[process.argv.indexOf("--prover") + 1]
    : "real";
  const raw = await readAllStdin();
  const env = transformNamesFromJSON(JSON.parse(raw)) as ParsedEnv;
  const prover = which === "null" ? NullProver : makeRealProver(env);
  process.stdout.write(generateTwelf(prover, env));
}

main().catch((err: unknown) => {
  // eslint-disable-next-line no-console
  console.error(err);
  process.exit(1);
});
