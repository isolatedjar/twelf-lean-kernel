#!/usr/bin/env bash
# scripts/build-arena-ndjson.sh
#
# (Re)build the lean-kernel-arena test NDJSONs that this project checks.
#
# We do NOT keep a copy of the tests in this repo.  The arena is the single
# source of truth and is assumed to live in a sibling directory at
# ../lean-kernel-arena (override with $ARENA or the first positional arg).
# This script just drives the arena's own `lka.py build-test`, which writes
# its output under $ARENA/_build/tests/.  `scripts/gen-tests.sh` then reads
# those NDJSONs directly to produce lf/tests/*.elf.
#
# We build the arena's non-heavy set via its `--skip-ci` flag, which skips the
# tests tagged `skip-on-ci: true` in their YAML (mathlib, std, cslib, mlir,
# cedar, init) — the ones that require cloning/compiling large external Lean
# projects.  Everything else (the tutorial suite plus the singleton tests) is
# built.
#
# Requires: elan + lake (the per-test lean-toolchain pins the Lean version) and
# `uv` (to run lka.py with its Python deps).
#
# Usage:
#   ./scripts/build-arena-ndjson.sh                 # build the whole non-heavy set
#   ./scripts/build-arena-ndjson.sh tutorial        # rebuild one definition (name/glob)
#   ARENA=/path/to/lean-kernel-arena ./scripts/build-arena-ndjson.sh

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ARENA="${ARENA:-$REPO_ROOT/../lean-kernel-arena}"

# The first positional arg, if given, is a test name/glob passed straight
# through to `lka.py build-test` (the arena path comes from $ARENA, not argv).
TEST_FILTER=()
if [[ $# -gt 0 ]]; then
    TEST_FILTER=("$1")
fi

if [[ ! -f "$ARENA/lka.py" ]]; then
    echo "error: arena not found at '$ARENA' (no lka.py there)." >&2
    echo "       Set \$ARENA or place the arena at ../lean-kernel-arena." >&2
    exit 2
fi

ARENA="$(cd "$ARENA" && pwd)"
echo "Building arena test NDJSONs in: $ARENA"
echo "  (skipping skip-on-ci tests: mathlib, std, cslib, mlir, cedar, init)"

( cd "$ARENA" && uv run lka.py build-test --skip-ci "${TEST_FILTER[@]}" )

echo ""
echo "Done. NDJSONs are under $ARENA/_build/tests/"
echo "Next: ./scripts/gen-tests.sh   (regenerates lf/tests/*.elf from them)"
