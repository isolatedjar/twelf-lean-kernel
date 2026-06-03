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
import {
  clearStringNeqFacts,
  fmtToDoc,
  levelParamBindings,
  levelParamIndices,
  lfExpr,
  lfExprDoc,
  lfLevel,
  mangle,
  natLiteralsSeen,
  stringNeqFacts,
} from "./render.ts";
import type { Doc } from "./pp.ts";
import { concat, group, line, nest, render, text } from "./pp.ts";
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
import { app, atom, lam, nameToString, transformNamesFromJSON } from "./shared.ts";
import { freshVar } from "./render.ts";

// =====================================================================
// Output + Fmt pretty-printer (trusted, anti-injection)
// =====================================================================

const out: string[] = [];
function emit(s: string): void {
  out.push(s);
}

// Pretty-print an Fmt proof term.  Validation lives in render.ts:fmtToDoc,
// layout in pp.ts:render.
//
// `hang` is the column the proof's first character will land at in the
// emitted file — i.e. the length of whatever prefix the caller has already
// printed on the current line.  We pass `80 - hang` as the budget so the
// fits-lookahead correctly accounts for the prefix, and we prepend `hang`
// spaces to every break the renderer emits so subsequent lines align under
// the proof's start rather than at column 0.
function ppFmt(f: Fmt, hang = 0): string {
  const raw = render(80 - hang, fmtToDoc(f));
  if (hang === 0) return raw;
  return raw.replace(/\n/g, "\n" + " ".repeat(hang));
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
    levelParamIndices.set(nameToString(p), i);
  });
  try {
    return fn();
  } finally {
    for (const p of params) {
      levelParamBindings.delete(nameToString(p));
      levelParamIndices.delete(nameToString(p));
    }
  }
}

// =====================================================================
// Obligation emission
// =====================================================================

// Target width for pretty-printed obligation types.  The HEAD baseline (no
// pretty-printing) emitted long single lines — ~99 chars was common — so
// using a strict 80-col budget would aggressively break medium-length types
// that the project previously left intact (a ~30% .elf size bloat for no
// readability win).  We pick a deliberately generous 200 so only truly large
// types (recursors, deep forall chains) break, and the common case stays on
// one line.
const TYPE_WIDTH = 200;

// Render an obligation-type Doc to a string with the right hanging indent for
// the "<constName> : " prefix already known by the caller.  Multi-line types
// align under the column where the type begins, not at column 0.
function ppType(typeDoc: Doc, hang: number): string {
  const raw = render(TYPE_WIDTH - hang, typeDoc);
  if (hang === 0) return raw;
  return raw.replace(/\n/g, "\n" + " ".repeat(hang));
}

// Emit a Twelf constant: a definition (`<const> : <type> = <term>.`) when
// `term` is non-null, or a declaration with a HOLE warning (`%%% HOLE` then
// `<const> : <type>.`) when it is null.  `type` is a `Doc`.
//
// Layout: the type's first line glues to the `${constName} : ` prefix, and
// continuation lines land at column-0 + nest (no hang under the prefix
// column).  So a wrapped `of T (esort U)` reads
//
//   N_rec/type-wf : of
//     <T-rendered>
//     (esort N_rec/type-wf-sort)
//
// rather than hanging the second `(esort ...)` argument under column 16.
// The proof on the `= ` line is still hung at 5 (under the `= ` itself),
// since proof terms read better that way.
function emitDefn(constName: string, type: Doc, term: Fmt | null): void {
  const typeStr = ppType(type, 0);
  if (term === null) {
    emit(`%%% HOLE`);
    emit(`${constName} : ${typeStr}.`);
  } else {
    emit(`${constName} : ${typeStr}`);
    emit(`   = ${ppFmt(term, 5)}.`);
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
function emitObligation(result: Fmt | null, constName: string, judgmentType: Doc): string {
  emitDefn(constName, judgmentType, result);
  return constName;
}

// Emit the type-wf obligation `of T (esort U)` — i.e. T is a well-formed
// type at sort U.  `of` is `derived.elf`'s transparent abbreviation for the
// diagonal `defeq T T (esort U)`; Twelf unfolds it when feeding the witness
// into `dkind-ok/{indt,ctor,irec,quot}`, which still take `defeq` premises.
// We use the abbreviation to halve the surface size of every type-wf line
// (T no longer appears twice) without changing any TCB rule.
//
// For `thm` the kernel forces U = lzero (the type must be a Prop), so we emit
// the literal and no universe obligation.  Otherwise U is *synthesized* (the
// Sort that T inhabits — not in the NDJSON), so we emit it as its own
// obligation on `lvl`: `lvl` is freezable, so the universe HOLE is itself
// detectable.  (T may mention `lvar` schema variables; the obligation type
// stays ground because those are data, not LF binders.)
function emitTypeWf(result: TypeWfResult, mn: string, T: Doc, isThm: boolean): string {
  // The obligation `of <T> (esort <U>)`: emit T as a Doc child so a big T
  // (the killer case: recursor types) breaks into a readable nested layout.
  // U is one token, kept inline.
  if (isThm) {
    const proof = result === null ? null : result.proof;
    return emitObligation(proof, `${mn}/type-wf`, ofSort(T, text("lzero")));
  }
  const sortRef = emitObligation(
    result === null ? null : result.sort,
    `${mn}/type-wf-sort`,
    text("lvl"),
  );
  return emitObligation(
    result === null ? null : result.proof,
    `${mn}/type-wf`,
    ofSort(T, text(sortRef)),
  );
}

// `of <T> (esort <U>)` as a Doc.  Top-level group with a break-after-`of`:
// short obligations fit flat as `of T (esort U)`; long ones break to
//
//   of
//     T
//     (esort U)
//
// with T's own subgroups breaking inside as needed.  Pairs with `ppType(.,
// hang=0)`: the obligation's args land at column 0 + nest (= column 2) on a
// continuation line rather than hung under the `: ` column of the prefix.
function ofSort(T: Doc, U: Doc): Doc {
  return group(concat(text("of"), nest(2, concat(line, T, line, text("(esort "), U, text(")")))));
}

// Same shape for `of <V> <T>` (value-has-type).
function ofValueType(V: Doc, T: Doc): Doc {
  return group(concat(text("of"), nest(2, concat(line, V, line, T))));
}

// Emit the `ctor-positive` obligation for a constructor and return its name.
//
// The proof is `ctor-positive/intro ([S] T_HOAS) <spine>`.  The generator
// computes T_HOAS — the ctor type with the inductive's self-reference
// `(econst IndName IndLevels)` abstracted to the bound `S` — via render.ts
// `lfExpr` with a SelfSubst, and the prover supplies the `<spine>` (a
// `ctor-spine N0 T_HOAS` derivation).
//
// This is NO LONGER a soundness boundary.  Earlier, T_HOAS correctness was
// load-bearing: a wrong abstraction that left a self-occurrence as the closed
// constant `(econst N0 _)` in a Π-domain would slip through
// `strict-pos/no-occur`/`strict-pos/forall` and fake positivity.  The TCB now
// guards every such domain with a `no-self-ref N0` premise (tcb.elf), whose
// `econst` leaves are discharged by posited `string-neq` facts audited by the
// global `%query 0 * string-neq X X` (final-checks.elf).  So a residual self-
// constant forces a reflexive `string-neq N0 N0` that sinks the load, and a
// wrong/adversarial T_HOAS or spine can now only lose completeness (a HOLE),
// never produce an unsound acceptance.  Computing T_HOAS here remains a
// convenience for discharging the obligation, not a trust dependency.
function emitCtorPositive(
  prover: Prover,
  c: { type: Expr; induct: Name; levelParams: Name[] },
  indName: string,
  indLevels: Level[],
  mn: string,
  T: string,
): string {
  const posName = `${mn}/positivity`;
  // ctor-positive "Foo" <lvls> <T>: the obligation type Doc.
  const posTypeDoc = concat(
    text(`ctor-positive "${indName}" ${formalLvls(c.levelParams.length)} `),
    // T came in as a flat string from the caller; treat it as a single text
    // node so the broader Doc layout doesn't try to break inside it.  (For
    // big T, the line might overflow 80 chars; that's a minor cost relative
    // to step 3's win on type-wf — emitCtorPositive's T appears only here.)
    text(T),
  );
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
    emitDefn(posName, posTypeDoc, null); // HOLE
    return posName;
  }
  // Render the obligation type ourselves rather than going through emitDefn
  // — we need a custom proof template (`(ctor-positive/intro ([S] {hoasBody})
  // {spine})`) that splices hoasBody mid-line.
  const posType = ppType(posTypeDoc, posName.length + 3);
  emit(`${posName} : ${posType}`);
  // The spine sits mid-line after `(ctor-positive/intro ([S] {hoasBody}) `.
  // We can't easily know that column without measuring hoasBody, so hang
  // multi-line spines under the proof-equals column (5) — slight under-
  // alignment but readable; if hoasBody later becomes a Doc, this can hang
  // precisely.
  emit(`   = (ctor-positive/intro ([S] ${hoasBody}) ${ppFmt(spine, 5)}).`);
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
  tDoc: Doc,
  kExpr: string,
  okWitness: string,
): void {
  // Both lines use the same "break-after-head, args at col 2" pattern that
  // `of T U` uses (see ofSort): short decls stay flat, long ones wrap as
  //
  //   N_rec/decl : declared "N.rec"
  //     (eforall ...)
  //     irec
  //      = declared/ok-irec ...
  //
  // and the name-line analogously with `(is-decl` ending the head.
  const nameDoc = group(
    concat(
      text(`name "${declName}" (is-decl`),
      nest(2, concat(line, tDoc, line, text(`${kExpr})`))),
    ),
  );
  emit(`${mn}/name : ${render(TYPE_WIDTH, nameDoc)}.`);
  emit(``);

  const declDoc = group(
    concat(text(`declared "${declName}"`), nest(2, concat(line, tDoc, line, text(kExpr)))),
  );
  emit(`${mn}/decl : ${render(TYPE_WIDTH, declDoc)}`);
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

// Render an expr as a `Doc`; null if it can't be represented at all.
// Callers that want a flat single-line string render it with effectively
// infinite width; callers that want pretty wrap-around pass the Doc to
// emitDefn/emitObligation where the right hanging-indent is computed.
function tryLfDoc(e: Expr): Doc | null {
  try {
    return lfExprDoc(e, []);
  } catch {
    return null;
  }
}

// Flat single-line rendering of a Doc — for embedding inside larger strings.
function flatStr(d: Doc): string {
  return render(1_000_000, d);
}

// Render an expr to LF text; null if it can't be represented at all.
function tryLf(e: Expr): string | null {
  const d = tryLfDoc(e);
  return d === null ? null : flatStr(d);
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
    const tDoc = tryLfDoc(d.type);
    const vDoc = tryLfDoc(d.value);
    if (tDoc === null || vDoc === null) {
      skip(`${d.kind} ${declName} — type/value not representable in LF`);
      return;
    }
    // Flat single-line forms are still needed for embedding in emitDeclared
    // and in the dkind-ok constructor's value slot, which sit inside larger
    // strings.  Pretty-printable Docs feed emitTypeWf and the value-typed
    // obligation, where the wrapper computes hanging-indent.
    const T = flatStr(tDoc);
    const V = flatStr(vDoc);
    emit(`%% ${d.kind} ${declName}`);

    const tw = emitTypeWf(
      prover.typeWellFormed({ type: d.type, levelParams: d.levelParams, isThm: d.kind === "thm" }),
      mn,
      tDoc,
      d.kind === "thm",
    );
    const vt = emitObligation(
      prover.valueHasType({ value: d.value, type: d.type, levelParams: d.levelParams }),
      `${mn}/value-typed`,
      ofValueType(vDoc, tDoc),
    );

    const dkindCtor = d.kind === "def" ? "defn" : d.kind === "opaque" ? "opq" : "thm";
    const okCtor =
      d.kind === "def" ? "dkind-ok/defn" : d.kind === "opaque" ? "dkind-ok/opq" : "dkind-ok/thm";
    emitDeclared(mn, declName, tDoc, `(${dkindCtor} ${V})`, `(${okCtor} ${tw} ${vt})`);
  });
}

function generateAxiom(prover: Prover, d: Decl & { kind: "axiom" }): void {
  const declName = nameToString(d.name);
  const mn = mangle(d.name);
  withLevelParams(d.levelParams, () => {
    const tDoc = tryLfDoc(d.type);
    if (tDoc === null) {
      skip(`axiom ${declName} — type not representable in LF`);
      return;
    }
    const T = flatStr(tDoc);
    emit(`%% axiom ${declName}`);
    const tw = emitTypeWf(
      prover.typeWellFormed({ type: d.type, levelParams: d.levelParams }),
      mn,
      tDoc,
      false,
    );
    emitDeclared(mn, declName, tDoc, `ax`, `(dkind-ok/ax ${tw})`);
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

// Structural witness for `ends-in-sort-with-level T L`: T is a Π chain ending
// in `esort L`.  Both rules are determined by the syntactic shape of T:
// at each `eforall A B` introduce a fresh LF variable and recurse on B,
// emitting `(ends-in-sort-with-level/forall ([x] <rest>))`; at the result
// `esort L`, emit `ends-in-sort-with-level/sort` (with L inferred).
//
// Called by the ctor emission to provide the eisl premise to `dkind-ok/ctor`.
// No prover involvement — the witness is mechanical.
function buildEisl(t: Expr, used: string[] = []): Fmt {
  if (t.kind === "forallE") {
    const x = freshVar(used);
    const body = buildEisl(t.body, [x, ...used]);
    return app(atom("ends-in-sort-with-level/forall"), lam(x, body));
  }
  // At a non-forall expression — must be esort for ends-in-sort-with-level
  // to inhabit.  If it's not, Twelf will fail to type-check our witness;
  // either way the ctor declines.
  return atom("ends-in-sort-with-level/sort");
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
  for (const r of ind.recursors) {
    if (dupLevels(r.levelParams)) {
      return `recursor ${nameToString(r.name)} — duplicate universe parameter names`;
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
      const tDoc = tryLfDoc(c.type);
      if (tDoc === null) {
        skip(`ctor ${declName} — type not representable in LF`);
        return;
      }
      const T = flatStr(tDoc);
      const indLevels: Level[] = c.levelParams.map((name) => ({ kind: "param", name }));
      emit(`%% ctor ${declName} (of ${indName})`);
      const tw = emitTypeWf(
        prover.typeWellFormed({ type: c.type, levelParams: c.levelParams }),
        mn,
        tDoc,
        false,
      );
      const cp = emitCtorPositive(prover, c, indName, indLevels, mn, T);
      // §3.2: dkind-ok/ctor now requires three more witnesses — the parent
      // inductive's `declared`, an `ends-in-sort-with-level` derivation to
      // surface its sort, and a `field-universes-ok-skip-params` derivation
      // ensuring each field's sort is ≤ that sort (mleq).
      //
      // `eisl` is structural and we build it directly here (a fully-determined
      // walk of the inductive's Π chain to the result sort).  `fuo` needs
      // defeq + mleq subgoals for each field; that's prover work and lives
      // behind `prover.fieldUniverses`.  When the prover returns null (the
      // common case while the prover is incomplete), we emit a bare
      // declaration on the frozen `field-universes-ok-skip-params` family,
      // which %freeze rejects — so the ctor (and its env) declines.  That's
      // a loss of completeness, not of soundness.
      const indSpec = ind.types.find((t) => nameToString(t.name) === indName);
      if (indSpec === undefined) {
        skip(`ctor ${declName} — couldn't locate parent inductive ${indName}`);
        return;
      }
      const indMn = mangle(indSpec.name);
      const indUInd = inductiveResultUniverse(indSpec.type);
      if (indUInd === null) {
        skip(`ctor ${declName} — inductive ${indName} doesn't end in a concrete sort`);
        return;
      }
      // eisl: structural walk of the inductive's Π chain.  ends-in-sort-with-
      // level is closed, every node is determined by the syntactic shape.
      const eislFmt = buildEisl(indSpec.type);
      emit(
        `${mn}/eisl : ends-in-sort-with-level ${flatStr(lfExprDoc(indSpec.type, []))} ${lfLevel(indUInd)}`,
      );
      emit(`   = ${ppFmt(eislFmt, 5)}.`);
      emit(``);
      // fuo: bare HOLE on a frozen family until the prover can synthesize it.
      // Freeze rejects bare declarations, so the ctor's whole env declines.
      emit(`%%% HOLE: ${mn}/fuo — prover for field-universes-ok-skip-params not yet implemented`);
      emit(
        `${mn}/fuo : field-universes-ok-skip-params ${lidxLit(c.numParams)} ${T} ${lfLevel(indUInd)}.`,
      );
      emit(``);
      emitDeclared(
        mn,
        declName,
        tDoc,
        `ctor`,
        `(dkind-ok/ctor ${tw} ${cp} ${indMn}/decl ${mn}/eisl ${mn}/fuo)`,
      );
    });
  }
  // Recursors.
  for (const r of ind.recursors) {
    const declName = nameToString(r.name);
    const mn = mangle(r.name);
    withLevelParams(r.levelParams, () => {
      const tDoc = tryLfDoc(r.type);
      if (tDoc === null) {
        skip(`recursor ${declName} — type not representable in LF`);
        return;
      }
      const T = flatStr(tDoc);
      emit(`%% recursor ${declName}`);
      const tw = emitTypeWf(
        prover.typeWellFormed({ type: r.type, levelParams: r.levelParams }),
        mn,
        tDoc,
        false,
      );
      // A recursor is declared via `declared/ok-irec`, which requires the
      // `name N (is-rec-for IndN)` reservation that generateIndType emits for
      // its inductive.  Recover IndN by stripping the trailing ".rec" and find
      // the inductive that reserved it.  If there's no such inductive (the name
      // doesn't follow the <inductive>.rec convention), emit a HOLE — a bare
      // decl with no reservation witness, which %freeze rejects.
      const IndN = declName.endsWith(".rec") ? declName.slice(0, -4) : null;
      const indType =
        IndN !== null ? ind.types.find((t) => nameToString(t.name) === IndN) : undefined;
      const indMn = indType !== undefined ? mangle(indType.name) : null;
      // Match emitDeclared's break-after-head layout: short recursor types
      // stay flat; the killer N_rec / Eq_rec types wrap with `declared "..."`
      // alone on the prefix line and args at col 2.
      const declDoc = group(
        concat(text(`declared "${declName}"`), nest(2, concat(line, tDoc, line, text("irec")))),
      );
      const declStr = render(TYPE_WIDTH, declDoc);
      if (indMn !== null) {
        emit(`${mn}/decl : ${declStr}`);
        emit(`   = declared/ok-irec ${indMn}/rec-name (dkind-ok/irec ${tw}).`);
        emit(``);
      } else {
        emit(`%%% HOLE: recursor ${declName} — name does not follow <inductive>.rec convention`);
        emit(`${mn}/decl : ${declStr}.`);
        emit(``);
      }
    });
  }
}

function generateIndType(prover: Prover, t: IndType): void {
  const declName = nameToString(t.name);
  const mn = mangle(t.name);
  withLevelParams(t.levelParams, () => {
    const tDoc = tryLfDoc(t.type);
    if (tDoc === null) {
      skip(`inductive ${declName} — type not representable in LF`);
      return;
    }
    const T = flatStr(tDoc);
    emit(`%% inductive ${declName}`);
    const tw = emitTypeWf(
      prover.typeWellFormed({ type: t.type, levelParams: t.levelParams }),
      mn,
      tDoc,
      false,
    );
    const eis = emitObligation(
      prover.endsInSort({ type: t.type, levelParams: t.levelParams }),
      `${mn}/ends-in-sort`,
      concat(text("ends-in-sort "), tDoc),
    );
    // Reserve the canonical recursor slot: %unique name ensures no other
    // declaration can claim this string (e.g., a def with the recursor name).
    emit(`${mn}/rec-name : name "${declName}.rec" (is-rec-for "${declName}").`);
    emit(``);
    emitDeclared(mn, declName, tDoc, `indt`, `(dkind-ok/indt ${tw} ${eis})`);
  });
}

// =====================================================================
// Top-level
// =====================================================================

export function generateTwelf(prover: Prover, env: ParsedEnv): string {
  out.length = 0;
  natLiteralsSeen.clear();
  levelParamBindings.clear();
  levelParamIndices.clear();
  clearStringNeqFacts();

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
  // Prelude: the posited string-disequality facts that `no-self-ref` proofs
  // (strict positivity) refer to by `sneq/<i>` name.  These add to the open
  // `string-neq` family; final-checks.elf's `%query 0 * string-neq X X` rejects
  // any reflexive (a = b) claim, so emitting whatever the prover requested is
  // sound regardless of correctness.  A name with a quote/backslash/newline
  // would break the string literal, so reject it defensively (cannot happen
  // for well-formed Lean names, but the output must never be injectable).
  if (stringNeqFacts.length > 0) {
    stringNeqFacts.forEach(({ a, b }, i) => {
      for (const s of [a, b]) {
        if (/["\\\n]/.test(s)) {
          throw new Error(`string-neq fact rejected (possible injection): ${JSON.stringify(s)}`);
        }
      }
      prelude.push(`sneq/${i} : string-neq "${a}" "${b}".`);
    });
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
