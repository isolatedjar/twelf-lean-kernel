#!/usr/bin/env -S node --experimental-strip-types
// pp.test.ts — smoke tests for the pretty-printer engine.  Runs directly with
// `node --experimental-strip-types`; exits 1 on any failure with a focused
// diff.  Not wired through vitest yet; the rest of the project's npm test is
// still a no-op.

import type { Doc } from "./pp.ts";
import { concat, group, line, nest, nil, render, sepBy, text } from "./pp.ts";

let fails = 0;

function check(name: string, actual: string, expected: string): void {
  if (actual === expected) {
    process.stdout.write(`  OK ${name}\n`);
    return;
  }
  fails++;
  process.stdout.write(`  FAIL ${name}\n`);
  process.stdout.write(`    expected:\n${indent("|   ", expected)}\n`);
  process.stdout.write(`    actual:\n${indent("|   ", actual)}\n`);
}

function indent(p: string, s: string): string {
  return s.split("\n").map((l) => p + l).join("\n");
}

// ----- Atoms -----------------------------------------------------------

check("plain text", render(80, text("hello")), "hello");

check(
  "concat of texts",
  render(80, concat(text("("), text("fn"), text(")"))),
  "(fn)",
);

// ----- Lines and groups ------------------------------------------------

const fnArgs = group(
  concat(
    text("(fn"),
    nest(2, concat(line, text("arg1"), line, text("arg2"))),
    text(")"),
  ),
);

check(
  "group fits on one line at width 80",
  render(80, fnArgs),
  "(fn arg1 arg2)",
);

check(
  "group breaks at narrow width with proper nest indent",
  render(10, fnArgs),
  "(fn\n  arg1\n  arg2)",
);

// ----- Nested groups: outer breaks, inner stays flat when it fits ------

const outer = group(
  concat(
    text("("),
    text("outer"),
    nest(2, concat(
      line,
      group(concat(text("(inner"), nest(2, concat(line, text("x"), line, text("y"))), text(")"))),
      line,
      group(concat(text("(inner2"), nest(2, concat(line, text("a"), line, text("b"))), text(")"))),
    )),
    text(")"),
  ),
);

check(
  "everything fits → flat",
  render(80, outer),
  "(outer (inner x y) (inner2 a b))",
);

// At a width where the outer can't fit but each inner can.
check(
  "outer breaks, both inners stay flat",
  render(20, outer),
  "(outer\n  (inner x y)\n  (inner2 a b))",
);

// ----- Inherited flat: inner groups forced flat by outer ---------------

// Force a layout where the WHOLE thing fits flat — the inner group's line
// must become a space too (inherited flat), not respect its own width.
const inheritedFlat = group(concat(text("a"), line, group(concat(text("b"), line, text("c")))));
check("inherited flat collapses inner lines", render(80, inheritedFlat), "a b c");

// ----- sepBy helper ----------------------------------------------------

check(
  "sepBy with line between items",
  render(80, group(sepBy(line, [text("x"), text("y"), text("z")]))),
  "x y z",
);

check(
  "sepBy with line, broken",
  render(3, group(sepBy(line, [text("xx"), text("yy"), text("zz")]))),
  "xx\nyy\nzz",
);

check("sepBy empty", render(80, sepBy(line, [])), "");

// ----- Domain-shaped example: LF-like s-expression ---------------------

// Mimic what fmtToDoc/exprToDoc will produce: head followed by indented args.
type SArg = string | Doc;
function sexp(head: string, ...args: SArg[]): Doc {
  const argDocs: Doc[] = args.map((a) => (typeof a === "string" ? text(a) : a));
  const argsDoc: Doc =
    argDocs.length === 0
      ? nil
      : concat(...argDocs.flatMap((d): Doc[] => [line, d]));
  return group(concat(text("("), text(head), nest(2, argsDoc), text(")")));
}

const recursorTypeShape = sexp(
  "eforall",
  sexp("eforall", sexp("econst", "\"Bool\"", "lnil"), sexp("[x]", sexp("esort", sexp("lvar", "liz")))),
  sexp(
    "[x]",
    sexp(
      "eforall",
      sexp("eapp", "x", sexp("econst", "\"Bool.false\"", "lnil")),
      sexp("[y]", sexp("eforall", sexp("eapp", "x", sexp("econst", "\"Bool.true\"", "lnil")), sexp("[z]", "..."))),
    ),
  ),
);

const oneLine = render(1000, recursorTypeShape);
const formatted = render(80, recursorTypeShape);
process.stdout.write(`  (info) recursor-shape one-line: ${oneLine.length} chars\n`);
process.stdout.write(`  (info) recursor-shape width-80:\n`);
process.stdout.write(indent("    ", formatted) + "\n");

// Just assert that breaking actually happened at width 80 (one-line should
// exceed it, so we expect newlines in the formatted output).
if (oneLine.length > 80 && !formatted.includes("\n")) {
  fails++;
  process.stdout.write("  FAIL recursor-shape should have broken at width 80\n");
} else {
  process.stdout.write("  OK recursor-shape broke at width 80\n");
}

process.stdout.write(`\n${fails === 0 ? "PASS" : `FAIL (${fails})`} pp.test.ts\n`);
process.exit(fails === 0 ? 0 : 1);
