# twelf-lean-kernel

A Twelf-based kernel checker for Lean 4 environments. Encodes Lean's definitional equality into LF and checks it with Twelf.

## What it does

Lean 4 exports environment declarations as NDJSON (one JSON object per declaration). This project translates that NDJSON into Twelf LF and asks Twelf to verify each declaration type-checks against the TCB (`lf/tcb.elf`).

Pipeline:
```
.ndjson  →  src/parse.ts  →  JSON IR  →  src/lean2lf.ts  →  .elf  →  twelf-server  →  ✅ / ❌
```

Test cases live under `tests/` (NDJSON) and `lf/tests/` (generated `.elf`).

## Running tests

```bash
# Regenerate all .elf files from NDJSON
./scripts/gen-tests.sh

# Check all tests with Twelf
./scripts/check-tests.sh /home/user/twelf-src/bin/twelf-server

# TypeScript type-check
npx tsc --noEmit
```

Twelf server binary: `/home/user/twelf-src/bin/twelf-server`

## Key files

| File | Role |
|------|------|
| `lf/tcb.elf` | Trusted base — LF encoding of Lean's type theory |
| `lf/derived.elf` | Derived lemmas built on top of the TCB |
| `lf/shared.elf` | Shared definitions used across test files |
| `lf/final-checks.elf` | Final verification declarations |
| `lf/sources.cfg` | Twelf sources file (loads TCB in order) |
| `src/parse.ts` | NDJSON → JSON IR parser |
| `src/lean2lf.ts` | JSON IR → Twelf LF translator |
| `scripts/gen-tests.sh` | Generate `lf/tests/*.elf` from `tests/*.ndjson` |
| `scripts/check-tests.sh` | Run Twelf on each `.elf` and report results |

## Test status

Tests are in `tests/` and categorized:
- `good/` — declarations that should be accepted
- `bad/` — declarations that should be rejected

Run `check-tests.sh` for the current pass/fail/skip breakdown.

## Plans and design docs

- `render-plan-revised-by-rob.md` — current active plan (render pass + hole emission)
- `completeness-plan.md` — longer-term roadmap for filling proof gaps
- `render-plan.md` — earlier draft (superseded by the -by-rob version)
- `lf/archive/first-version.elf` — historical earlier encoding (explicit levels; superseded by tcb.elf's implicit-level approach)
