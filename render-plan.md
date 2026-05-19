# Plan: a "moral Twelf" render pass

## What this is

Project: a Twelf-based kernel checker for Lean. The translator
(`translator/lean2lf.ts`) takes Lean's NDJSON export and emits a Twelf LF
signature; the result is checked against a small TCB (`tcb.elf`,
`derived.elf`, `final-checks.elf`) to certify each declaration. Pipeline
today:

```
.ndjson  →  parse.ts   →  resolved JSON IR  →  lean2lf.ts  →  .elf  →  twelf  →  ✅ / ❌ / 🤷
```

`parse.ts` was split off from `lean2lf.ts` to make the NDJSON → IR step
auditable as its own thing. This document proposes the analogous next split,
on the other side of the IR: a render pass whose output is auditable as "the
Twelf equivalent of the NDJSON file."

## The problem we're solving

Right now `lean2lf.ts` does two things at once:

1. **Render** each Expr/Decl into Twelf LF syntax (`econst`, `eforall`, …,
   `dkind-ok/...`).
2. **Construct proofs** for every kernel-level judgment the TCB requires
   (`defeq`, `ends-in-sort`, `ctor-positive`, etc.).

When (2) fails — translator isn't clever enough, missing defeq rule, missing
lvl-eq rule, or a synth bridge can't be built — the **entire declaration** is
dropped and a `%% SKIP:` marker is emitted. The test gets classified 🤷
(incomplete). The harness now reports this honestly (Good 50 ✅ / 26 ⚠️ / 10
❌, Bad 20 ✅ / 19 ⚠️ / 1 💥) but it doesn't distinguish _why_ a test is 🤷:

- Sometimes we **can't even represent** what's in the NDJSON (no `eproj`
  constructor in the LF expr datatype; no `enatlit` for `Nat.succ`-style
  literals).
- Sometimes we **can represent it fine** but couldn't construct the proof
  obligation Twelf needs (defeq gap, missing universe-arithmetic rule, etc.).

The first kind is a hard wall. The second kind is a TODO list — but right now
it's an invisible TODO list, hidden behind "the translator gave up."

## Goal of the render pass

Produce, for every input NDJSON, a file that:

- Renders **every** declaration: no syntactic form is ever dropped.
- Looks like Twelf (uses `econst`, `eforall`, `defeq`, `dkind-ok/indt`, …) so
  a human reading it sees a recognizable LF signature.
- **Doesn't need to compile as valid Twelf.** Where we'd normally need a proof
  we don't have, it emits a clearly-marked hole.
- Is human-auditable: a person familiar with both Lean and the LF encoding
  should be able to read it and convince themselves "yes, this is a fair
  encoding of what was in the NDJSON, modulo these listed holes."

The output is the "moral Twelf" version of the NDJSON. Holes are syntactic
markers in the rendered file; whether downstream Twelf actually accepts the
file is a separate, later question.

## Architecture

Add one more pass to the pipeline:

```
.ndjson  →  parse.ts  →  JSON IR  →  render.ts  →  moral-LF .elf  →  twelf  →  …
                                          ↑
                                  THIS IS THE NEW PASS
```

- `render.ts` is **total** over the JSON IR. It never throws.
- It emits Twelf-shaped output with explicit hole annotations where the
  existing `lean2lf.ts` would have thrown or emitted `%% SKIP:`.
- The audit story: read `render.ts` (short, mechanical) and read its output
  (one file per NDJSON test); satisfy yourself the rendering is faithful.

`lean2lf.ts` either gets refactored to _be_ `render.ts` plus a layered proof
pass, or stays as the "best-effort with real proofs" path and `render.ts`
becomes a parallel auditable lens. The first option (refactor) is probably
better long-term; the second (parallel) is safer to land incrementally.

## Hole conventions

Output is roughly Twelf, but holes are markers rather than valid Twelf terms.
Two flavors:

### Term-position hole

Used inside an expression we can render but where some sub-piece is unknown:

```
%% HOLE/defeq: couldn't bridge inferred type Nat to declared type Nat.succ Nat.zero
[u, v] (defeq/forall (defeq/sort-refl-at u) ?HOLE_defeq?)
```

The `?HOLE_<judgment>?` marker stands in for the missing proof. Twelf would
reject the file; that's fine — the hole tells a human (or a later filler pass)
exactly what proof obligation is unmet.

### Declaration-position hole

Used when we can't render or construct the entire declaration body:

```
%% HOLE/ctor-positive: field strict-pos under-capture (see safelist)
Foo_mk/positivity : ctor-positive "Foo" lnil <T_lf> = ?HOLE_ctor-positive?.
```

### Per-judgment hole categories

Each hole names _which_ judgment is unmet. Initial list, drawn from the
current 🤷 sources:

| Hole tag                     | Meaning                                                       | Current 🤷 sources           |
| ---------------------------- | ------------------------------------------------------------- | ---------------------------- |
| `HOLE/defeq`                 | Two terms morally definitionally equal, no proof constructed  | 070, 095-101, 110, 112       |
| `HOLE/ends-in-sort`          | Inductive type signature should end in a sort, can't prove it | (already handled via %solve) |
| `HOLE/ctor-positive`         | Constructor should be strictly positive, can't prove it       | 047, 050, 105 (safelist)     |
| `HOLE/lvl-eq`                | Universe equality, no rule                                    | scattered                    |
| `HOLE/numparams-ok`          | numParams ≤ #leading Π, no LF judgment yet                    | 042                          |
| `HOLE/canonical-ctor-result` | ctor result's param-args / index-args must be canonical       | 043, 044, 046                |
| `HOLE/universe-le`           | field universe ≤ inductive universe − 1                       | 054                          |
| `HOLE/proj-typed`            | `eproj` typing, no rule                                       | 078-088, 104                 |

Each is a TODO line item: either a TCB extension (judgment added) or a
translator improvement (proof can now be constructed).

## Concrete changes

### 1. `shared.ts` — extend the Expr IR (representation)

Current `Expr` already has `proj`, `natLit`, `strLit` cases (added during the
parse split). They just throw in `lfExpr`. No type changes needed.

### 2. `tcb.elf` — extend the LF Expr datatype (representation)

Add unproductive constructors so we can _render_ proj / natLit / strLit:

```
eproj    : name -> peano -> expr -> expr.
enatlit  : enat  -> expr.
estrlit  : estr  -> expr.

%% Minimal nat/str datatypes (no arithmetic, no reduction).  Their job
%% is only to make the expr family closed under what NDJSON ships.
peano   : type.
peano/z : peano.
peano/s : peano -> peano.

enat    : type.
enat/z  : enat.
enat/s  : enat -> enat.

estr    : type.
estr/empty : estr.
estr/cons  : char -> estr -> estr.   %% or some opaque opaqification
```

No typing rules. The semantics is opaque — that's the point. Any defeq
involving `eproj`/`enatlit`/`estrlit` will need either a hole or a future TCB
extension.

This unblocks ~12 tests (proj-family and natLit-family) from
representation-blocked to proof-blocked.

### 3. `render.ts` — total rendering pass

Mirror the structure of `lean2lf.ts`'s `emitValDecl` / `emitInductive` /
`emitAxiom`, but every emission is `Render = string`. Replace every `throw`
with a `?HOLE_<x>?` marker emission and a preceding `%% HOLE/<x>: <reason>`
comment line.

Sketch of the function shape:

```typescript
function renderExpr(e: Expr): string {
  switch (e.kind) {
    case "bvar":
      return `(bvar ${peano(e.deBruijn)})`;
    case "sort":
      return `(esort ${renderLevel(e.level)})`;
    case "const":
      return `(econst ${stringLit(e.name)} ${renderLvls(e.us)})`;
    case "app":
      return `(eapp ${renderExpr(e.fn)} ${renderExpr(e.arg)})`;
    case "forallE":
      return `(eforall ${renderExpr(e.type)} ([${fresh()}] ${renderExpr(e.body)}))`;
    case "lam":
      return `(elam ${renderExpr(e.type)} ([${fresh()}] ${renderExpr(e.body)}))`;
    case "letE": /* either desugar (current) or render letE syntactically */
    case "proj":
      return `(eproj ${stringLit(e.typeName)} ${peano(e.idx)} ${renderExpr(e.struct)})`;
    case "natLit":
      return `(enatlit ${enatFromString(e.value)})`;
    case "strLit":
      return `(estrlit ${estrFromString(e.value)})`;
  }
}
```

Note: `bvar` rendering is wrong above as-is (`bvar` isn't a TCB constructor —
it's used in HOAS). The actual rendering needs to track the binder context to
translate bvars to HOAS variables. `lean2lf.ts` already does this via the
`boundVars: string[]` parameter to `lfExpr`; preserve that pattern.

For declarations: emit the structural pieces verbatim, drop in hole markers
where `lean2lf.ts` would have thrown. E.g., for
`<mn>/type-wf : defeq T T (sort u) = <proof>.` where `<proof>` couldn't be
constructed:

```
%% HOLE/defeq: type-well-formedness for <name>: couldn't unify ... with ...
<mn>/type-wf : defeq <T_lf> <T_lf> <sort_lf> = ?HOLE_defeq?.
```

### 4. Harness — count holes, separate verification level

`check-tests.sh` currently has six counters (good ✅/⚠️/❌, bad ✅/⚠️/💥). Add
a "with-holes" axis:

```
Good (expected accept) N:   ✅ N1 fully    🩹 N2 with-holes    ❌ N3 rejected
Bad  (expected reject) M:   ✅ N4 rejected 🩹 N5 with-holes    💥 N6 accepted
```

Counting: `grep -c "^%% HOLE/" <file>`. A test is 🩹 iff it has at least one
hole _and_ Twelf doesn't outright reject it for non-hole reasons.

Verdict semantics:

- **Good ✅ fully**: Twelf accepts, zero holes. Genuine kernel-level pass.
- **Good 🩹 with-holes**: Twelf accepts but we papered over judgments. Honest
  "we don't know yet" — could become ✅ once holes are filled, or could become
  ❌.
- **Good ❌ rejected**: Twelf rejects via structural check (`applies-self`,
  `%unique`, arity mismatch). Genuine bug or a known structural disagreement
  with Lean.
- **Bad ✅ rejected**: Twelf rejects despite our holes; the brokenness is
  caught by a judgment we _did_ encode.
- **Bad 🩹 with-holes**: Twelf accepts but only because of holes. Honest
  "might still be caught when holes are filled" — each one is a
  regression-risk to monitor.
- **Bad 💥 accepted**: Twelf accepts a bad test with no holes. Soundness bug.

The bad 🩹 column is the most important new signal. Currently, when a bad test
fails to be Twelf-rejected through a SKIP, we count it 🤷 and lose track.
Under the new scheme each becomes a tracked hole list with a concrete TODO.

### 5. Migration ordering

Each step lands independently and the corpus stays green throughout.

1. **TCB extension only.** Add
   `eproj`/`enatlit`/`estrlit`/`peano`/`enat`/`estr` to `tcb.elf`. No
   translator changes. Verify corpus unchanged.

2. **Make `lfExpr` total.** Replace `throw new Error("X not yet supported")`
   with emission of the new constructors. Now `proj`/`natLit`/`strLit` tests
   reach the synth phase instead of bailing at rendering. Some 🤷 tests may
   move to ❌ (Twelf rejects the un-reducible terms) or to 🩹 (synth emits
   holes); track each transition.

3. **Hole-aware synth.** Wrap each `synth(...)` and proof-constructor call in
   a `tryProve` adapter that returns `{ proof } | { hole, reason }`. On
   `hole`, emit `%% HOLE/<judgment>: <reason>` and `?HOLE_<judgment>?` as the
   proof body. Remove `%% SKIP:` emissions except for genuine representation
   gaps that even the new constructors don't cover.

4. **Optional: extract `render.ts`.** Move the pure rendering helpers
   (`lfExpr`, `lfLevel`, `lfLvls`, declaration assembly) into a separate file.
   `lean2lf.ts` imports them and adds the proof-construction layer on top.
   This is the architectural payoff: rendering becomes auditable in isolation.

5. **Update `check-tests.sh`** with the 🩹 column. Categorize the corpus.

6. **Triage the hole list.** For each test in 🩹, decide: TCB extension,
   translator improvement, or known safelist case.

## What stays out of scope

- **Strict-positivity field-position safelist (047, 050, 105).** This isn't
  fixed by the render pass — it's a TCB-level soundness gap in
  `ctor-positive/intro`. The render pass _will_ mark these with
  `%% HOLE/ctor-positive` rather than silently producing a spurious proof;
  that's a small improvement. The real fix is the `fully-captures` judgment
  described in `completeness.md`.

- **Filling holes.** Each hole becomes a concrete TODO, but actually _filling_
  them (extending the TCB with new judgments, teaching the translator new
  defeq rules) is the work-after-this-work. The render pass just makes that
  work tractable by surfacing the list.

- **Twelf compilation of the moral-LF output.** The output doesn't need to be
  valid Twelf. If a downstream pipeline wants real Twelf, it can strip the
  holes (each is a single line) or replace them with `hole/<judgment>` axioms
  (an even smaller TCB extension — see "Optional later" below).

## Optional later: make hole-output Twelf-loadable

If, after a few iterations of hole-filling, we want the residual-holes output
to be loadable into Twelf for soundness-modulo-holes checking, add an axiom
per judgment:

```
%%% In a separate "holes.elf" file — never loaded for real verification.
hole/defeq         : {A:expr} {B:expr} {T:expr} defeq A B T.
hole/ends-in-sort  : {T:expr} ends-in-sort T.
hole/ctor-positive : {N:name} {LS:lvls} {T:expr} ctor-positive N LS T.
hole/lvl-eq        : {U:lvl} {V:lvl} lvl-eq U V.
```

Then `?HOLE_defeq?` becomes `(hole/defeq _ _ _)` and the file compiles.
Loading `holes.elf` makes the TCB inconsistent, so this would be a
development-mode aid, not a production verification path. The check-tests
harness would refuse to count anything as ✅ if `holes.elf` was loaded.

## Files involved

In `/home/claude/twelf-lean/`:

- `tcb.elf` — the trusted base, ~700 lines
- `derived.elf` — small layer of derived lemmas
- `final-checks.elf` — global %mode/%worlds/%unique on `declared` (new this
  session)
- `translator/shared.ts` — IR types (Name, Level, Expr, Decl, Inductive, …)
- `translator/parse.ts` — NDJSON → JSON IR
- `translator/lean2lf.ts` — JSON IR → LF (current entry point, ~2000 lines)
- `regen.sh` — runs parse | lean2lf for all NDJSON inputs
- `run-gen.sh` — local harness (calls Twelf, counts results)

Test inputs in `/home/claude/arena/tutorial/{good,bad}/*.ndjson` (126 files
total). Each has an `*.info.json` with a description line.

Canonical artifacts synced to `/mnt/user-data/outputs/`: `tcb.elf.txt`,
`shared.ts`, `parse.ts`, `lean2lf.ts`, `regen.sh`, `check-tests.sh`,
`completeness.md`, `final-checks.elf.txt`.

## Current state to pick up from

Last full run (before this plan):

```
Good (expected accept) 86:   ✅ 50   ⚠️ 26   ❌ 10
Bad  (expected reject) 40:   ✅ 20   ⚠️ 19   💥 1
```

Migration progress already made (documented in `completeness.md`):

- `%unique declared` catches duplicates (5 tests migrated).
- `%solve` on `ends-in-sort` for monomorphic types (2 tests).
- Conditional `%solve` on `ctor-positive` for head-mismatch (1 test).
- Level-substituted `%solve` for polymorphic head-mismatch (1 test).
- Dup-aware synth-failure suppression (1 test).

Recent infrastructure splits:

- `final-checks.elf` extracted (global directives).
- `parse.ts` extracted (NDJSON → JSON IR, with `_n`-tagged Name compaction).
- `lean2lf.ts` slimmed to consume `ParsedEnv` JSON.

Recent bug fix:

- `check-tests.sh` was silently mis-reporting tests as "accept" when its inner
  `cd "$LF_DIR"` failed under `set -euo pipefail`. Fixed: validates `$LF_DIR`
  / `sources.cfg` / `final-checks.elf` at startup, uses a tempfile-based
  output capture, flags empty-output cases instead of pretending they're
  accepts.

## First concrete steps for the next agent

If picking this up cold, do these in order:

1. **Verify current state.** Run `/home/claude/twelf-lean/run-gen.sh`. Expect
   `Good 50/26/10, Bad 20/19/1`. If not, something has drifted since this
   writeup.

2. **Add the extended Expr constructors to `tcb.elf`.** Just the type
   declarations, no rules. Re-run; expect no change.

3. **Make `lfExpr` total in `lean2lf.ts`.** Replace the four
   `throw new Error("X not yet supported")` cases (search for the string) with
   emissions of `eproj` / `enatlit` / `estrlit` / `eletE` (or desugar letE;
   current code already desugars in parse.ts, so that case is dead). Re-run;
   some 🤷 tests should move. Categorize the diff.

4. **Introduce `tryProve` adapter and per-judgment hole emissions.** This is
   the bulk of the work. Identify every `try { ... synth(...) ... } catch`
   block in `lean2lf.ts`; convert each to emit a hole instead of `%% SKIP:`.

5. **Update the harness.** Add the 🩹 column.

6. **Snapshot and review.** The output is the audit artifact. Read several
   moral-LF files (start with `030_boolType.elf` for a clean case, then
   `093_aNatLit.elf` for a freshly-unblocked case, then `047_indNeg.elf` for a
   safelist case) and check that they look like fair Twelf-shaped renderings
   of their NDJSON inputs.

The whole project's value is in step 6 — being able to read the output and
audit it. Steps 1-5 are mechanics that get us there.

## Risks

- **Hole pollution.** If most tests get many holes, the audit becomes hard to
  skim. Mitigation: per-judgment categorization, summary at top of each file
  listing `%% holes: 3 defeq, 1 ctor-positive`.

- **Categorization drift.** Each hole tag's exact meaning needs to be stable
  for triage to work. Mitigation: keep the tag definitions in a single comment
  block at the top of `render.ts` (or wherever holes are emitted).

- **The auditable-rendering claim is only as strong as the renderer's
  simplicity.** If `render.ts` grows complex, the audit loses its force.
  Mitigation: keep proof construction _out_ of the rendering path entirely.
  Holes are first-class output; they're not failure modes, they're the design.

- **Some current 🤷s might turn out to mask actual bugs.** When the corpus
  shifts and e.g. some good test was relying on a SKIP to _avoid_ triggering a
  real Twelf rejection, removing the SKIP exposes the rejection. Mitigation:
  track every 🤷 → ❌ transition as a separate to-look-at line item.
