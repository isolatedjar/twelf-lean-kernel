# twelf-lean-kernel

A Twelf-based kernel checker for Lean 4 environments. Encodes Lean's
definitional equality into LF and checks it with Twelf.

## What it does

Lean 4 exports environment declarations as NDJSON (one JSON object per
declaration). This project translates that NDJSON into Twelf LF and asks Twelf
to verify each declaration type-checks against the TCB (`lf/tcb.elf`).

Pipeline:

```
.ndjson  →  src/parse.ts  →  JSON IR  →  src/generate-twelf.ts  →  .elf  →  twelf-server  →  ✅ / ❌
                                              (prover plugin: src/prover.ts + src/synth.ts)
```

Test cases live under `tests/` (NDJSON) and `lf/tests/` (generated `.elf`).

## Architecture (trust boundary)

`generate-twelf.ts` is the single, **trusted** generator. It walks a
`ParsedEnv` and, for each proof obligation, asks a **`Prover`** (see the
`Prover` interface in `shared.ts`) to discharge it. The prover returns a
structured `Fmt` proof term, which the generator pretty-prints (`ppFmt`
validates every atom/binder, so an untrusted prover cannot smuggle a
declaration terminator). A prover method returns one of:

- `Fmt` → `<const> : <obligation> = <proof>.` (discharged)
- `null` → `%%% HOLE` + `<const> : <obligation>.` (bare decl, rejected by
  `%freeze`)
- `failOnPurpose` (the undeclared atom `fail-on-purpose`) → Twelf ABORTs → the
  env is **rejected on purpose** (used when the prover can _prove_ an
  obligation false, not merely fail to prove it true)

Two provers, both run by the same generator:

- **`NullProver`** discharges nothing → produces `.render.elf` (every
  obligation a HOLE). This is the "moral Twelf" view.
- **`makeRealProver(env)`** (in `prover.ts`, backed by `synth.ts`) → produces
  `.full.elf`.

Because both files come from the same generator, `.render.elf` structurally
contains every fact `.full.elf` does (the adequacy property). **Auditing
`shared.ts` + `parse.ts` + `generate-twelf.ts` suffices** (plus the three
trusted `.elf`: `tcb.elf`, `freeze.elf`, `final-checks.elf`); `prover.ts` /
`synth.ts` are untrusted — a prover bug can only lose completeness (a wrongful
HOLE/reject), never accept an ill-typed term.

### Posited facts audited globally (the `%unique` / `string-neq` pattern)

Two soundness checks follow the same shape: the environment is allowed to
*posit* facts onto an **open** type family, and a global directive in
`final-checks.elf` rejects the whole load if any posited fact is inconsistent.

- **Name → meaning functional dependency.** The env adds `<decl>/name` facts to
  the open `name` family; `%unique name` rejects a string given two meanings.
- **String disequality (strict positivity).** LF can't *derive* that two
  strings differ, so the env *posits* `string-neq "a" "b"` facts on the open
  `string-neq` family to discharge the `no-self-ref` leaves of a constructor's
  positivity proof. `%query 0 * string-neq X X.` ABORTs the load if any posited
  pair is reflexive (`a = a`). So a translator may claim whatever
  disequalities it likes; a lie sinks the development. This makes
  `ctor-positive` sound **inside the TCB**, independent of the generator's
  `T_HOAS` computation (see the `string-neq` / `no-self-ref` comments in
  `tcb.elf`, and the regression in `lf/soundness/`).

## Running tests

```bash
# Regenerate all .elf files from NDJSON
./scripts/gen-tests.sh

# Check all tests with Twelf
./scripts/check-tests.sh /home/user/twelf-src/bin/twelf-server

# Run the hand-written soundness regressions (adversarial .elf that the TCB
# must reject on its own — see lf/soundness/)
./scripts/check-soundness.sh /home/user/twelf-src/bin/twelf-server

# TypeScript type-check
npx tsc --noEmit
```

## Twelf binary (limited-thaw build)

Twelf server binary: `/home/user/twelf-src/bin/twelf-server`.

It must be built from the **`limited-thaw`** branch of
[`robsimmons/twelf`](https://github.com/robsimmons/twelf/tree/limited-thaw), not
stock Twelf. The harness detects unfilled obligations by loading the environment
against a **frozen** TCB: a HOLE is a bare declaration on a frozen family, which
Twelf's freezing check rejects. This only works if `%thaw name` (in
`lf/freeze.elf`, needed so each environment can add its own `<decl>/name`
reservations) thaws *only* `name` and not its transitive dependents. Stock Twelf
thaws transitively — re-opening `defeq` — so it would wrongly accept unfilled
`defeq` obligations; `limited-thaw` is a one-line fix to
`src/subordinate/subordinate.fun`. Rebuild with:

```bash
./scripts/build-twelf.sh            # requires MLton; → /home/user/twelf-src/bin/twelf-server
```

Because the frozen load is now authoritative, the `%%% HOLE` marker in generated
`.elf` files is purely informational — `check-tests.sh` no longer simulates
freeze rejection from it.

## Regenerating the tutorial NDJSON test cases

The NDJSON files under `tests/tutorial/` are generated from the Lean 4 source
in `lean/tutorial/` (a copy of the tutorial project from
[lean-kernel-arena](https://github.com/leanprover/lean-kernel-arena/tree/master/tutorial)).
They are checked in so the TypeScript pipeline can run without Lean.

To regenerate them (requires `elan`/`lake` on PATH):

```bash
./scripts/regen-tutorial-ndjson.sh
```

After regenerating NDJSON, re-run `./scripts/gen-tests.sh` to update the
`.elf` files.

## Key files

| File                               | Role                                                                |
| ---------------------------------- | ------------------------------------------------------------------- |
| `lf/tcb.elf`                       | Trusted base — LF encoding of Lean's type theory                    |
| `lf/derived.elf`                   | Derived lemmas built on top of the TCB                              |
| `lf/shared.elf`                    | Shared definitions used across test files                           |
| `lf/final-checks.elf`              | Final verification declarations (`%unique name`, `string-neq` audit)|
| `lf/soundness/`                    | Hand-written adversarial `.elf` the TCB must reject (regressions)   |
| `lf/sources.cfg`                   | Twelf sources file (loads TCB in order)                             |
| `src/parse.ts`                     | NDJSON → JSON IR parser (trusted)                                   |
| `src/shared.ts`                    | IR types + the `Prover` interface + `Fmt` (trusted)                 |
| `src/generate-twelf.ts`            | JSON IR → Twelf LF generator (trusted); inductive pre-flight checks |
| `src/render.ts`                    | Pure IR → LF text rendering (`lfExpr`, mangling)                    |
| `src/prover.ts`                    | `NullProver` + `makeRealProver` (untrusted)                         |
| `src/synth.ts`                     | Type synthesizer / defeq prover / positivity builders (untrusted)   |
| `scripts/gen-tests.sh`             | Generate `lf/tests/*.elf` from `tests/*.ndjson`                     |
| `scripts/check-tests.sh`           | Run Twelf on each `.elf` and report results                         |
| `scripts/check-soundness.sh`       | Load each `lf/soundness/*.elf` through the chain; assert it ABORTs  |
| `scripts/regen-tutorial-ndjson.sh` | Regenerate `tests/tutorial/**/*.ndjson` from Lean source            |
| `lean/tutorial/`                   | Lean 4 source for the tutorial test suite                           |

## Test status

Tests are in `tests/` and categorized:

- `good/` — declarations that should be accepted
- `bad/` — declarations that should be rejected

Run `check-tests.sh` for the current pass/fail/skip breakdown.

### Verdict taxonomy

Each test gets one raw outcome (precedence order), reported by
`check-tests.sh`:

| Outcome | Meaning                                                                                |
| ------- | -------------------------------------------------------------------------------------- |
| 🤷      | generator declined to represent the env (`.full.elf` has `%%% SKIP`)                   |
| 🔴      | `.render.elf` rejected by Twelf even without freeze (rendering is broken)              |
| ✅      | `.full.elf` accepted by the full pipeline (freeze + final-checks)                      |
| 🩹      | `.full.elf` rejected _with_ freeze but accepted _without_ (only unfilled HOLEs failed) |
| ❌      | `.full.elf` rejected even without freeze (a genuine error on a concrete term)          |

Mapping to a pass/fail verdict depends on what the test expects:

- **good (expect accept):** ✅ → pass · 🩹 → incomplete · 🤷/🔴/❌ → fail
- **bad (expect reject):** 🤷/🔴/❌ → pass(reject) · 🩹 → incomplete · ✅ → 💥
  **soundness failure**

🤷 (and 🔴) count as a reject from the Kernel Arena's perspective, so they are
a _pass_ for bad tests and a _fail_ for good tests — we'd like to represent
every valid Lean signature, but some inputs (unparseable NDJSON, malformed de
Bruijn indices, invariants we can only check translator-side) genuinely can't
be posed to Twelf. A 🩹 means we declined to _evaluate_ the development (the
HOLE isn't filled), distinct from Twelf verifying it bad (❌).

## Plans and design docs

- `completeness-plan.md` — the live roadmap: a tick-box accounting of how much
  of Mario Carneiro's declarative `IsDefEq` spec the TCB encodes, plus
  salvaged design notes for the highest-value remaining work (level-equality
  decision procedure, name-reservation soundness check, `lean.mm1` borrows).
  Start here for "what's left to do."
