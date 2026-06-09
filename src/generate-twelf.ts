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
  recordStringNeq,
  stringNeqFacts,
} from "./render.ts";
import type { Doc } from "./pp.ts";
import { concat, group, line, nest, render, text } from "./pp.ts";
import type {
  Decl,
  Expr,
  Fmt,
  IndCtor,
  IndRecursor,
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

// A de Bruijn level index as a unary `nat` literal: z, (s z), (s (s z)), ...
function lidxLit(i: number): string {
  let acc = "z";
  for (let k = 0; k < i; k++) acc = `(s ${acc})`;
  return acc;
}

// The canonical formal level list for an `n`-parameter declaration:
// `(lcons (lvar z) (lcons (lvar (s z)) ... lnil))`.  Used where a rule
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
// For `thm` the kernel forces U = lzero (the type must be a Prop), so we
// emit the literal.  Otherwise U is *synthesized* (the Sort that T
// inhabits — not in the NDJSON).  Previously we emitted U as its own
// `<mn>/type-wf-sort : lvl = <U-value>.` constant so the .render.elf could
// leave it as a HOLE on `lvl`.  Now `lvl` is closed by levels.elf (its
// dependent judgments are `%total`), so bare `<...> : lvl.` declarations
// are rejected even pre-freeze.  We inline U directly into the type
// expression — the level is pure computed data, never a real proof
// obligation, so losing the named indirection doesn't affect auditability.
function emitTypeWf(result: TypeWfResult, mn: string, T: Doc, isThm: boolean): string {
  // The obligation `of <T> (esort <U>)`: emit T as a Doc child so a big T
  // (the killer case: recursor types) breaks into a readable nested layout.
  // U is one token, kept inline.
  if (isThm) {
    const proof = result === null ? null : result.proof;
    return emitObligation(proof, `${mn}/type-wf`, ofSort(T, text("lzero")));
  }
  // Inline U into the obligation type.  For .full.elf U comes from the
  // synthesized result; for .render.elf result is null, so we emit `_`
  // and let Twelf treat the level as undetermined — the surrounding
  // declaration is a HOLE on the (frozen) `defeq` family anyway, so the
  // missing U doesn't matter.
  const uDoc =
    result === null || result.sort === null ? text("_") : fmtToDoc(result.sort);
  return emitObligation(
    result === null ? null : result.proof,
    `${mn}/type-wf`,
    ofSort(T, uDoc),
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
  dknWitness: string,
): void {
  // Defer to `emitInductiveFamilyDecl`, the generalized form. The non-
  // inductive-family path always uses `declared/ok ${mn}/name <dkn> ${okWitness}`.
  // The new `dkind-non-inductive K` premise (2026-06-03, see tcb.elf §"dkind
  // payloads") blocks declared/ok from sealing inductive-family kinds; the
  // caller supplies the matching witness atom (one of
  // `dkind-non-inductive/{defn,thm,opq,ax,quot}`).
  emitInductiveFamilyDecl(
    mn,
    declName,
    tDoc,
    kExpr,
    "declared/ok",
    `${mn}/name ${dknWitness} ${okWitness}`,
  );
}

// Generalized inductive-family declared/decl emission.  The non-inductive
// callers go through `emitDeclared` (which fixes the ok-rule to
// `declared/ok` and prepends `${mn}/name` to the witness list).  The
// inductive-family callers (indt/ctor/irec) call this directly so they can
// route through `declared/ok-indt` / `-ctor` / `-irec` and supply their
// specialized witness lists.
//
// Layout matches the rest of emitDefn/ofSort: a `group` with break-after-
// head, args at col 2.
function emitInductiveFamilyDecl(
  mn: string,
  declName: string,
  tDoc: Doc,
  kExpr: string,
  okRule: string,
  okWitnessArgs: string,
): void {
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
  emit(`   = ${okRule} ${okWitnessArgs}.`);
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
    case "quot": {
      // Quot's four constants are TCB-derived (see CLAUDE.md "Derive,
      // don't check" and tcb.elf §Quot).  The translator emits a
      // comment block documenting lean4export's claimed type, but
      // no Twelf declaration — `tcb.elf`'s `quot-name-Quot{,-mk,-lift,
      // -ind}` already reserve the names, and the `quot-known` family
      // provides what iota rules need.
      const tStr = (() => {
        try {
          return flatStr(lfExprDoc(d.type, []));
        } catch {
          return "(type not representable in LF)";
        }
      })();
      emit(`%% quot ${nameToString(d.name)} (${d.quotKind}) (TCB-derived; informational only)`);
      emit(`%%   type: ${tStr}`);
      emit(``);
      break;
    }
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
    const dknWitness =
      d.kind === "def"
        ? "dkind-non-inductive/defn"
        : d.kind === "opaque"
          ? "dkind-non-inductive/opq"
          : "dkind-non-inductive/thm";
    emitDeclared(
      mn,
      declName,
      tDoc,
      `(${dkindCtor} ${V})`,
      `(${okCtor} ${tw} ${vt})`,
      dknWitness,
    );
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
    emitDeclared(mn, declName, tDoc, `ax`, `(dkind-ok/ax ${tw})`, "dkind-non-inductive/ax");
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

// not-forall/<head> for a given non-forall expr.  Closed family — every
// non-forall expression has exactly one constructor.  Returns null if the
// expr is a bvar (not a top-level form a closed term should bottom out at)
// or a forallE (a logic error — caller should have stopped recursing).
function buildNotForall(t: Expr): Fmt | null {
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


// Build a `cnames` literal `(ccons "c_0" (ccons "c_1" ... cnil))` from a
// list of ctor name-strings (already in cidx order).
function ctorsToCnames(names: string[]): string {
  let acc = "cnil";
  for (let i = names.length - 1; i >= 0; i--) {
    acc = `(ccons "${names[i]}" ${acc})`;
  }
  return acc;
}

// Build `cmem C Ctors` witness for C at the i-th position (0-based) of
// Ctors.  cmem/here at i=0, (cmem/there^i cmem/here) otherwise.
function buildCmem(cidx: number): Fmt {
  let f: Fmt = atom("cmem/here");
  for (let k = 0; k < cidx; k++) f = app(atom("cmem/there"), f);
  return f;
}

// Build `cnames-distinct Ctors` for the list of ctor name-strings (in
// cidx order).  Each `cnames-distinct/cons` carries an `all-string-neq C
// Rest` whose leaves are `string-neq C D` posits — when the translator
// has no real proof, the posit is recorded via `recordStringNeq` so the
// global `%query 0 * string-neq X X` audit catches a lie.
function buildCnamesDistinct(names: string[]): Fmt {
  // `all-string-neq C Rest`: chain of (cons (string-neq C D_0) (cons ... nil))
  function allNeq(C: string, rest: string[]): Fmt {
    if (rest.length === 0) return atom("all-string-neq/nil");
    const D = rest[0]!;
    const tail = allNeq(C, rest.slice(1));
    const neq = atom(recordStringNeq(C, D));
    return app(atom("all-string-neq/cons"), neq, tail);
  }
  let acc: Fmt = atom("cnames-distinct/nil");
  // Walk from the back so the outermost ccons is at the front.  At each
  // step prepend names[k] and carry an all-string-neq against the suffix.
  for (let k = names.length - 1; k >= 0; k--) {
    const tail = names.slice(k + 1);
    const asn = allNeq(names[k]!, tail);
    acc = app(atom("cnames-distinct/cons"), acc, asn);
  }
  return acc;
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
  // Type formers.  Per §3.5, each inductive's reservation now carries its
  // full ctor list (in cidx order) and its NumParams.  We compute both from
  // `ind.ctors` (filtered to this type) so the reservation is grounded in
  // the env's own data and Twelf can match `name FooName (is-decl _ (indt
  // Ctors NParams))` lookups downstream.
  for (const t of ind.types) {
    const indName = nameToString(t.name);
    const ctorsForT = ind.ctors.filter((c) => nameToString(c.induct) === indName);
    // §3.3: bind MRec to the recorded `recs[].name` rather than a
    // synthesized `${indName}.rec`.  The NDJSON's `inductive` record
    // bundles `recs[]` inside the family; for non-mutual inductives
    // there's one recursor, used verbatim.  For mutual families we
    // fall back to the `<indName>.<...>` prefix.
    const rec =
      ind.types.length === 1
        ? ind.recursors[0]
        : ind.recursors.find((r) => nameToString(r.name).startsWith(`${indName}.`));
    // Canonicality decline: a non-canonical recursor name is not a
    // soundness gap (the TCB binds MRec to whatever name we recorded),
    // but it's also not a representable Lean kernel env — Lean's
    // canonical recursor is always `<ind>.rec`.  Treat as a translator-
    // side decline so the arena classifies the test correctly (bad
    // tests expecting reject pass via 🤷, good tests would fail).
    if (rec !== undefined && nameToString(rec.name) !== `${indName}.rec`) {
      skip(
        `inductive ${indName} — non-canonical recursor name "${nameToString(rec.name)}" (expected "${indName}.rec")`,
      );
      return;
    }
    generateIndType(prover, t, ctorsForT, rec);
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
      // §3.2 / §3.5: dkind-ok/ctor + declared/ok-ctor now require five
      // more witnesses than dkind-ok/ctor used to.  Three are structural
      // and we build them directly: eisl (the inductive's
      // ends-in-sort-with-level) and cmem (this ctor's position in the
      // inductive's reserved Ctors list).  Two are HOLEs on frozen
      // families (fuo for field-universes-ok-skip-params) until the
      // prover catches up — that drops the ctor's env to a decline but
      // never to wrong-accept.
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
      // Compute this ctor's cidx (its position among ctors of the same
      // inductive, in declaration order).
      const ctorsForInd = ind.ctors.filter((cc) => nameToString(cc.induct) === indName);
      const cidx = ctorsForInd.findIndex((cc) => nameToString(cc.name) === declName);
      if (cidx < 0) {
        skip(`ctor ${declName} — couldn't locate own cidx in parent ${indName}`);
        return;
      }
      // eisl: emitted once on the inductive (see generateIndType), shared
      // here as `${indMn}/eisl` rather than re-emitting per ctor.
      // cmem: this ctor's position in the inductive's reserved Ctors list.
      const ctorNames = ctorsForInd.map((cc) => nameToString(cc.name));
      const ctorsCnames = ctorsToCnames(ctorNames);
      const cmemFmt = buildCmem(cidx);
      emit(`${mn}/cmem : cmem "${declName}" ${ctorsCnames}`);
      emit(`   = ${ppFmt(cmemFmt, 5)}.`);
      emit(``);
      // fuo: prover walks the WHOLE ctor type with field-universes-ok
      // (no skip-params; see tcb.elf §field-universes-ok).  For each
      // leading Π synthesizes `defeq A A (esort UA)` plus the
      // impredicative `mleq (limax UA UInd) UInd 0`.  Returns null when
      // the synth heuristic gives up; we then emit a bare HOLE on the
      // frozen family, which %freeze rejects.  Loss of completeness,
      // never of soundness.
      const fuoFmt = prover.fieldUniverses({
        ctorType: c.type,
        nParams: 0,                // skip nothing — walk everything
        indUInd,
        levelParams: c.levelParams,
      });
      const fuoType = `field-universes-ok ${T} ${lfLevel(indUInd)}`;
      if (fuoFmt === null) {
        emit(`%%% HOLE: ${mn}/fuo`);
        emit(`${mn}/fuo : ${fuoType}.`);
      } else {
        emit(`${mn}/fuo : ${fuoType}`);
        emit(`   = ${ppFmt(fuoFmt, 5)}.`);
      }
      emit(``);
      // dkind payload: (ctor "<ind>" <cidx>).  Hand-roll the line rather
      // than going through emitDeclared because the dkind expression has
      // moving parts (indName, cidx).
      const cidxLidx = lidxLit(cidx);
      const dkindExpr = `(ctor "${indName}" ${cidxLidx})`;
      const okWitness = `(dkind-ok/ctor ${tw} ${cp})`;
      emitInductiveFamilyDecl(
        mn,
        declName,
        tDoc,
        dkindExpr,
        `declared/ok-ctor`,
        // The ok-ctor witness consumes (in order): name reservation, the
        // parent's name reservation, cmem, eisl, fuo, dkind-ok/ctor.
        `${mn}/name ${indMn}/name ${mn}/cmem ${indMn}/eisl ${mn}/fuo ${okWitness}`,
      );
    });
  }
  // Recursors are TCB-derived (see CLAUDE.md "Derive, don't check").  The
  // translator emits a comment block per recursor documenting the lean4-
  // export-supplied type and reduction rules — purely informational, no
  // Twelf declarations.  The TCB's `rec-derived` family constructs the
  // canonical recursor from the inductive's declaration; iota proofs in
  // `.full.elf` consume `rec-derived` via the untrusted prover.
  for (const r of ind.recursors) {
    emitRecursorComment(r);
  }
}

// Emit a Twelf-comment-block documenting a recursor's lean4export-supplied
// type and reduction rules.  Format is a mangled Twelf/Lean hybrid: each
// rule's RHS is shown in LF syntax; the LHS is sugared for readability.
// Not parsed by Twelf — purely for human readers.
function emitRecursorComment(r: IndRecursor): void {
  const declName = nameToString(r.name);
  withLevelParams(r.levelParams, () => {
    const tStr = (() => {
      try {
        return flatStr(lfExprDoc(r.type, []));
      } catch {
        return "(type not representable in LF)";
      }
    })();
    emit(`%% recursor ${declName} (TCB-derived; informational only)`);
    const lps = r.levelParams.map((p) => nameToString(p)).join(" ");
    if (lps.length > 0) emit(`%%   level params: ${lps}`);
    emit(`%%   type:   ${tStr}`);
    if (r.rules.length > 0) {
      emit(`%%   rules:`);
      for (const rule of r.rules) {
        const ctorName = nameToString(rule.ctor);
        const rhsStr = (() => {
          try {
            return flatStr(lfExprDoc(rule.rhs, []));
          } catch {
            return "(rhs not representable in LF)";
          }
        })();
        emit(`%%     ${declName} … ${ctorName} … = ${rhsStr}   (${rule.nfields} fields)`);
      }
    }
    if (r.k) emit(`%%   K-like reduction: yes`);
    emit(``);
  });
}

function generateIndType(
  prover: Prover,
  t: IndType,
  ctorsForT: readonly IndCtor[],
  rec: IndRecursor | undefined,
): void {
  const declName = nameToString(t.name);
  const mn = mangle(t.name);
  withLevelParams(t.levelParams, () => {
    const tDoc = tryLfDoc(t.type);
    if (tDoc === null) {
      skip(`inductive ${declName} — type not representable in LF`);
      return;
    }
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
    // §3.3: reserve the recorded recursor name, not a synthesized one.
    // The NDJSON's `inductive` record bundles its recursors by
    // containment, so the inductive↔recursor binding is already
    // explicit at the source level; flattening it to a `<ind>.rec`
    // convention would manufacture an artificial soundness gap.  If
    // the env doesn't carry a recursor (atypical but possible), fall
    // back to the canonical name.  `%unique name` still catches a
    // junk `def` colliding with the *actual* reserved name.
    const recName = rec ? nameToString(rec.name) : `${declName}.rec`;
    emit(`${mn}/rec-name : name "${recName}" (is-rec-for "${declName}").`);
    emit(``);
    // §3.1 / §3.5: emit the inductive's `ends-in-sort-with-level` witness
    // *once* on the inductive (it's a property of the inductive's type
    // alone), and reference it from both ctors (`declared/ok-ctor`) and
    // recursors (`dkind-ok/irec`).  Pre-§3.1 this was emitted per-ctor,
    // duplicating the same fact across every ctor; reciprocally,
    // recursors had no way to reach it.  Centralizing here serves both
    // call sites and avoids redundancy.
    const indUInd = inductiveResultUniverse(t.type);
    if (indUInd !== null) {
      const eislFmt = buildEisl(t.type);
      emit(`${mn}/eisl : ends-in-sort-with-level ${flatStr(tDoc)} ${lfLevel(indUInd)}`);
      emit(`   = ${ppFmt(eislFmt, 5)}.`);
      emit(``);
    }
    // §3.5: emit the cnames-distinct witness
    // that `declared/ok-indt` requires.  Both are structural / posit-and-
    // audited (the cnames-distinct leaves record `string-neq` posits that
    // the global `%query 0 * string-neq X X` audit catches if reflexive).
    //
    // The `indt`'s NParams payload is the inductive's `numParams`, carried
    // unchecked (declared/ok-indt no longer pins it — field-universes-ok
    // checks all leading binders uniformly, so there is no skip count to
    // over-claim against).
    const ctorNames = ctorsForT.map((c) => nameToString(c.name));
    const ctorsCnames = ctorsToCnames(ctorNames);
    const nparamsLidx = lidxLit(t.numParams);
    // cnames-distinct: pairwise-distinct ctor name list (closes the
    // duplicate-ctor iota gap via the string-neq posit + global %query
    // audit pattern).
    const cndFmt = buildCnamesDistinct(ctorNames);
    emit(`${mn}/cnd : cnames-distinct ${ctorsCnames}`);
    emit(`   = ${ppFmt(cndFmt, 5)}.`);
    emit(``);
    // dkind payload: (indt <Ctors> <NParams>).  NParams is the inductive's
    // numParams as supplied by the env — kept in the payload for
    // informational use (e.g. by tooling); not load-bearing in any TCB
    // soundness check after the no-skip-params refactor.
    const dkindExpr = `(indt ${ctorsCnames} ${nparamsLidx})`;
    emitInductiveFamilyDecl(
      mn,
      declName,
      tDoc,
      dkindExpr,
      `declared/ok-indt`,
      `${mn}/name ${mn}/rec-name ${mn}/cnd (dkind-ok/indt ${tw} ${eis})`,
    );
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
