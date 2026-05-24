#!/usr/bin/env -S node --experimental-strip-types
// generate-twelf.ts — the single, trusted Twelf generator.
//
// Reads a ParsedEnv JSON on stdin, emits a Twelf signature on stdout.
// Parameterized by a Prover (see shared.ts): for every proof obligation
// the generator raises, it asks the prover for an `Fmt` proof.
//   - prover returns Fmt  → `<const> : <type> = <proof>.`   (discharged)
//   - prover returns null → `%%% HOLE` + `<const> : <type>.` (declared by
//                            fiat; rejected by %freeze in the full load)
//   - prover returns
//     "fail-on-purpose"   → `%solve - : fail-on-purpose.`   (reject the env)
//
//   .render.elf = this generator with the NullProver (every obligation a HOLE)
//   .full.elf   = this generator with the RealProver
//
// Because both files come from THIS generator, `.render.elf` structurally
// contains every fact `.full.elf` does — that is the adequacy property.
// The Prover (prover.ts) is untrusted; auditing shared.ts + parse.ts + this
// file suffices.

import { NullProver, RealProver } from "./prover.ts";
import { levelParamBindings, lfExpr, mangle, nameToLfLevelVar, natLiteralsSeen } from "./render.ts";
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
import { lam, nameToString, transformNamesFromJSON } from "./shared.ts";

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

function withLevelParams<T>(params: Name[], fn: (lfNames: string[]) => T): T {
  const lfNames: string[] = [];
  for (const p of params) {
    const v = nameToLfLevelVar(p);
    levelParamBindings.set(nameToString(p), v);
    lfNames.push(v);
  }
  try {
    return fn(lfNames);
  } finally {
    for (const p of params) levelParamBindings.delete(nameToString(p));
  }
}

function lvlBinders(lfNames: string[]): string {
  return lfNames.map((n) => `{${n} : lvl} `).join("");
}

// `(lcons u1 (lcons u2 lnil))`, or `lnil` for the monomorphic case.
function lvlsExpr(lfNames: string[]): string {
  return lfNames.reduceRight((acc, n) => `(lcons ${n} ${acc})`, "lnil");
}

// How to reference an obligation constant inside a witness: bare when
// monomorphic, applied to the level args otherwise.
function obRef(constName: string, lfNames: string[]): string {
  return lfNames.length === 0 ? constName : `(${constName} ${lfNames.join(" ")})`;
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

// Render a single proof obligation and return a reference to use in the
// enclosing dkind-ok witness.  `null` → a HOLE (a bare decl rejected by
// %freeze); an `Fmt` → a definition.  A prover that wants to reject the
// environment supplies the `failOnPurpose` Fmt as its proof; it flows
// through like any term and Twelf rejects the ill-typed definition (no
// special-casing).  For a polymorphic obligation the type is `{u..} J` and
// the proof body is wrapped in the matching `[u..]` level-lambdas.
function emitObligation(
  result: Fmt | null,
  constName: string,
  lfNames: string[],
  judgmentType: string,
): string {
  const type = `${lvlBinders(lfNames)}${judgmentType}`;
  const body = result === null ? null : lfNames.reduceRight<Fmt>((b, n) => lam(n, b), result);
  emitDefn(constName, type, body);
  return obRef(constName, lfNames);
}

// Emit the type-wf obligation `defeq T T (esort U)`.
//
// For `thm` the kernel forces U = lzero (the type must be a Prop), so we emit
// the literal and no universe obligation.  Otherwise U is *synthesized* (the
// Sort that T inhabits — not in the NDJSON), so we emit it as its own
// obligation on `lvl`: `lvl` is freezable and independent of `declared`, so
// (a) the type-wf witness stays ground (no implicit-var reconstruction, no
// `%mode declared` violation) and (b) the universe HOLE is itself detectable.
function emitTypeWf(
  result: TypeWfResult,
  mn: string,
  lfNames: string[],
  T: string,
  isThm: boolean,
): string {
  if (isThm) {
    const proof = result === null ? null : result.proof;
    return emitObligation(proof, `${mn}/type-wf`, lfNames, `defeq ${T} ${T} (esort lzero)`);
  }
  const sortRef = emitObligation(
    result === null ? null : result.sort,
    `${mn}/type-wf-sort`,
    lfNames,
    `lvl`,
  );
  return emitObligation(
    result === null ? null : result.proof,
    `${mn}/type-wf`,
    lfNames,
    `defeq ${T} ${T} (esort ${sortRef})`,
  );
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
  withLevelParams(d.levelParams, (lfNames) => {
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
      lfNames,
      T,
      d.kind === "thm",
    );
    const vt = emitObligation(
      prover.valueHasType({ value: d.value, type: d.type, levelParams: d.levelParams }),
      `${mn}/value-typed`,
      lfNames,
      `defeq ${V} ${V} ${T}`,
    );

    const dkindCtor = d.kind === "def" ? "defn" : d.kind === "opaque" ? "opq" : "thm";
    const okCtor =
      d.kind === "def" ? "dkind-ok/defn" : d.kind === "opaque" ? "dkind-ok/opq" : "dkind-ok/thm";
    emit(`${mn}/decl : ${lvlBinders(lfNames)}declared "${declName}" ${lvlsExpr(lfNames)}`);
    emit(`   ${T}`);
    emit(`   (${dkindCtor} ${V})`);
    emit(`   (${okCtor} ${tw} ${vt}).`);
    emit(``);
  });
}

function generateAxiom(prover: Prover, d: Decl & { kind: "axiom" }): void {
  const declName = nameToString(d.name);
  const mn = mangle(d.name);
  withLevelParams(d.levelParams, (lfNames) => {
    const T = tryLf(d.type);
    if (T === null) {
      skip(`axiom ${declName} — type not representable in LF`);
      return;
    }
    emit(`%% axiom ${declName}`);
    const tw = emitTypeWf(
      prover.typeWellFormed({ type: d.type, levelParams: d.levelParams }),
      mn,
      lfNames,
      T,
      false,
    );
    emit(`${mn}/decl : ${lvlBinders(lfNames)}declared "${declName}" ${lvlsExpr(lfNames)}`);
    emit(`   ${T}`);
    emit(`   ax`);
    emit(`   (dkind-ok/ax ${tw}).`);
    emit(``);
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
    withLevelParams(c.levelParams, (lfNames) => {
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
        lfNames,
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
        lfNames,
        `ctor-positive "${indName}" ${lvlsExpr(lfNames)} ${T}`,
      );
      emit(`${mn}/decl : ${lvlBinders(lfNames)}declared "${declName}" ${lvlsExpr(lfNames)}`);
      emit(`   ${T}`);
      emit(`   ctor`);
      emit(`   (dkind-ok/ctor ${tw} ${cp}).`);
      emit(``);
    });
  }
  // Recursors.
  for (const r of ind.recursors) {
    const declName = nameToString(r.name);
    const mn = mangle(r.name);
    withLevelParams(r.levelParams, (lfNames) => {
      const T = tryLf(r.type);
      if (T === null) {
        skip(`recursor ${declName} — type not representable in LF`);
        return;
      }
      emit(`%% recursor ${declName}`);
      const tw = emitTypeWf(
        prover.typeWellFormed({ type: r.type, levelParams: r.levelParams }),
        mn,
        lfNames,
        T,
        false,
      );
      emit(`${mn}/decl : ${lvlBinders(lfNames)}declared "${declName}" ${lvlsExpr(lfNames)}`);
      emit(`   ${T}`);
      emit(`   irec`);
      emit(`   (dkind-ok/irec ${tw}).`);
      emit(``);
    });
  }
}

function generateIndType(prover: Prover, t: IndType): void {
  const declName = nameToString(t.name);
  const mn = mangle(t.name);
  withLevelParams(t.levelParams, (lfNames) => {
    const T = tryLf(t.type);
    if (T === null) {
      skip(`inductive ${declName} — type not representable in LF`);
      return;
    }
    emit(`%% inductive ${declName}`);
    const tw = emitTypeWf(
      prover.typeWellFormed({ type: t.type, levelParams: t.levelParams }),
      mn,
      lfNames,
      T,
      false,
    );
    const eis = emitObligation(
      prover.endsInSort({ type: t.type, levelParams: t.levelParams }),
      `${mn}/ends-in-sort`,
      lfNames,
      `ends-in-sort ${T}`,
    );
    emit(`${mn}/decl : ${lvlBinders(lfNames)}declared "${declName}" ${lvlsExpr(lfNames)}`);
    emit(`   ${T}`);
    emit(`   indt`);
    emit(`   (dkind-ok/indt ${tw} ${eis}).`);
    emit(``);
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
