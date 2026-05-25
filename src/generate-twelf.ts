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
//   .full.elf   = this generator with the RealProver
//
// Because both files come from THIS generator, `.render.elf` structurally
// contains every fact `.full.elf` does — that is the adequacy property.
// The Prover (prover.ts) is untrusted; auditing shared.ts + parse.ts + this
// file suffices.

import { NullProver, RealProver } from "./prover.ts";
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
      // Deferred (plugin-refactor step 1): quot members carry a type on this
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
      prover.typeWellFormed({ type: d.type, levelParams: d.levelParams }),
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

function generateInductive(prover: Prover, ind: Decl & { kind: "inductive" }): void {
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
      const cp = emitObligation(
        prover.ctorPositive({
          ctorType: c.type,
          indName: c.induct,
          indLevels,
          levelParams: c.levelParams,
        }),
        `${mn}/positivity`,
        `ctor-positive "${indName}" ${formalLvls(c.levelParams.length)} ${T}`,
      );
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
  const prover = which === "null" ? NullProver : RealProver;
  const raw = await readAllStdin();
  const env = transformNamesFromJSON(JSON.parse(raw)) as ParsedEnv;
  process.stdout.write(generateTwelf(prover, env));
}

main().catch((err: unknown) => {
  // eslint-disable-next-line no-console
  console.error(err);
  process.exit(1);
});
