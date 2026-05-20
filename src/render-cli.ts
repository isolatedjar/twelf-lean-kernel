#!/usr/bin/env -S node --experimental-strip-types
// render-cli.ts — render-only entry point.
//
// Reads a ParsedEnv JSON on stdin (from parse.ts), emits a Twelf file
// that binds the rendered shape of each Lean declaration as a named
// `expr` (or, for level-polymorphic decls, as `{u : lvl} expr`).
//
// This is the "moral Twelf" view: every Lean declaration is rendered
// faithfully by the pure-rendering layer in render.ts, with NO proof
// construction.  Auditing the encoding's faithfulness is a matter of
// reading just this output (and render.ts), without the noise of
// proof attempts that lean2lf.ts emits in the .full.elf version.
//
// Output is Twelf-loadable after the TCB: the constants here have
// type `expr` (or universally quantified over level params), so
// Twelf will at least validate that the rendered expressions are
// syntactically well-formed (binders correctly scoped, levels valid,
// names well-formed).  It does NOT attempt to prove the dkind-ok
// obligations — that's lean2lf.ts's job.

import type {
  Name,
  Level,
  Expr,
  Decl,
  ParsedEnv,
} from "./shared.ts";
import { nameToString, transformNamesFromJSON } from "./shared.ts";
import {
  mangle,
  lfExpr,
  nameToLfLevelVar,
  levelParamBindings,
  natLiteralsSeen,
} from "./render.ts";

// =====================================================================
// Output buffer
// =====================================================================

const out: string[] = [];

function emit(s: string): void {
  out.push(s);
}

// =====================================================================
// Level-param scope helper
// =====================================================================

function withLevelParams<T>(params: Name[], fn: () => T): T {
  for (const p of params) {
    levelParamBindings.set(nameToString(p), nameToLfLevelVar(p));
  }
  try {
    return fn();
  } finally {
    for (const p of params) {
      levelParamBindings.delete(nameToString(p));
    }
  }
}

function lvlPrefixes(params: Name[]): { binders: string; lams: string } {
  if (params.length === 0) return { binders: "", lams: "" };
  const binders = params.map((p) => `{${nameToLfLevelVar(p)} : lvl} `).join("");
  const lams = params.map((p) => `[${nameToLfLevelVar(p)}] `).join("");
  return { binders, lams };
}

// =====================================================================
// Rendering wrapper with error recovery
// =====================================================================

function tryRender(e: Expr): { ok: true; text: string } | { ok: false; err: string } {
  try {
    return { ok: true, text: lfExpr(e, []) };
  } catch (err: any) {
    return { ok: false, err: err.message };
  }
}

function emitBinding(name: string, levelParams: Name[], body: string): void {
  const { binders, lams } = lvlPrefixes(levelParams);
  emit(`${name} : ${binders}expr =`);
  emit(`   ${lams}${body}.`);
}

function emitRenderError(label: string, err: string): void {
  emit(`%% RENDER-ERROR ${label}: ${err}`);
}

// =====================================================================
// Per-declaration emission
// =====================================================================

function emitDecl(d: Decl): void {
  switch (d.kind) {
    case "def":
    case "thm":
    case "opaque": {
      const mn = mangle(d.name);
      emit(`%% ${d.kind} ${nameToString(d.name)}`);
      withLevelParams(d.levelParams, () => {
        const t = tryRender(d.type);
        if (t.ok) emitBinding(`${mn}/render-type`, d.levelParams, t.text);
        else emitRenderError(`${mn}/render-type`, t.err);
        const v = tryRender(d.value);
        if (v.ok) emitBinding(`${mn}/render-value`, d.levelParams, v.text);
        else emitRenderError(`${mn}/render-value`, v.err);
      });
      emit(``);
      break;
    }
    case "axiom": {
      const mn = mangle(d.name);
      emit(`%% axiom ${nameToString(d.name)}`);
      withLevelParams(d.levelParams, () => {
        const t = tryRender(d.type);
        if (t.ok) emitBinding(`${mn}/render-type`, d.levelParams, t.text);
        else emitRenderError(`${mn}/render-type`, t.err);
      });
      emit(``);
      break;
    }
    case "quot":
      emit(`%% quot — kernel-derived; no body to render`);
      emit(``);
      break;
    case "inductive": {
      for (const t of d.types) {
        const mn = mangle(t.name);
        emit(`%% inductive ${nameToString(t.name)} (numParams=${t.numParams}, numIndices=${t.numIndices})`);
        withLevelParams(t.levelParams, () => {
          const tr = tryRender(t.type);
          if (tr.ok) emitBinding(`${mn}/render-type`, t.levelParams, tr.text);
          else emitRenderError(`${mn}/render-type`, tr.err);
        });
        emit(``);
      }
      for (const c of d.ctors) {
        const mn = mangle(c.name);
        emit(`%% ctor ${nameToString(c.name)} (induct=${nameToString(c.induct)}, numFields=${c.numFields})`);
        withLevelParams(c.levelParams, () => {
          const tr = tryRender(c.type);
          if (tr.ok) emitBinding(`${mn}/render-type`, c.levelParams, tr.text);
          else emitRenderError(`${mn}/render-type`, tr.err);
        });
        emit(``);
      }
      for (const r of d.recursors) {
        const mn = mangle(r.name);
        emit(
          `%% recursor ${nameToString(r.name)} (numMotives=${r.numMotives}, numMinors=${r.numMinors}, k=${r.k})`,
        );
        withLevelParams(r.levelParams, () => {
          const tr = tryRender(r.type);
          if (tr.ok) emitBinding(`${mn}/render-type`, r.levelParams, tr.text);
          else emitRenderError(`${mn}/render-type`, tr.err);
          for (let i = 0; i < r.rules.length; i++) {
            const rule = r.rules[i]!;
            emit(`%%   rec-rule for ${nameToString(rule.ctor)} (nfields=${rule.nfields})`);
            const rr = tryRender(rule.rhs);
            if (rr.ok) emitBinding(`${mn}/render-rule${i}-rhs`, r.levelParams, rr.text);
            else emitRenderError(`${mn}/render-rule${i}-rhs`, rr.err);
          }
        });
        emit(``);
      }
      break;
    }
  }
}

// =====================================================================
// Main
// =====================================================================

async function readAllStdin(): Promise<string> {
  const chunks: Buffer[] = [];
  for await (const chunk of process.stdin) {
    chunks.push(chunk as Buffer);
  }
  return Buffer.concat(chunks).toString("utf8");
}

async function main(): Promise<void> {
  const raw = await readAllStdin();
  const parsed = transformNamesFromJSON(JSON.parse(raw)) as ParsedEnv;

  for (const decl of parsed.decls) {
    try {
      emitDecl(decl);
    } catch (e: any) {
      emit(`%% RENDER-ERROR decl ${(decl as any).kind}: ${e.message}`);
      emit(``);
    }
  }

  // Prepend %solve declarations for every nat literal encountered
  // by lfExpr.  Same plumbing as lean2lf.ts uses.
  const prelude: string[] = [];
  if (natLiteralsSeen.size > 0) {
    for (const n of natLiteralsSeen) {
      prelude.push(`%solve nonneg_${n} : ${n} >= 0.`);
    }
    prelude.push(``);
  }

  process.stdout.write([...prelude, ...out].join("\n") + "\n");
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
