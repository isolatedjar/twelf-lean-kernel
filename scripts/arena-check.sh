#!/usr/bin/env bash
# scripts/arena-check.sh — per-test wrapper for the Lean Kernel Arena.
#
# Usage:  arena-check.sh <ndjson-path>
# Reads the test NDJSON, runs the full twelf-lean-kernel pipeline on it, and
# exits per the arena's convention:
#
#   0  accept   — Twelf accepts .full.elf under tcb + freeze + derived + final-checks
#   1  reject   — .full.elf rejected even WITHOUT freeze (concrete error in the
#                 term, or the generator emitted `fail-on-purpose`)
#   2  decline  — generator skipped (%%% SKIP), parse/generate failed, or the
#                 .full.elf has unfilled HOLEs (rejected with freeze, accepted
#                 without)
#   3  error    — twelf-server produced no output / wrapper-internal failure
#
# Environment:
#   TWELF   path to the twelf-server binary (default: $REPO_ROOT/.twelf/bin/twelf-server).
#           The arena's checker `build:` populates this when it builds Twelf.
#
# Why the two loads?  An "accept-with-freeze" answer is sufficient for exit 0:
# every obligation was discharged AND verified.  Otherwise we re-load without
# freeze: if THAT accepts, the only thing the frozen load was complaining about
# was unfilled holes (decline), versus a genuine refutation of a posed term
# (reject).  This is precisely the classification done by scripts/check-tests.sh
# in its richer 5-outcome taxonomy — flattened here to the arena's 3 codes per
# the design note in arena-submission-plan.md.

set -euo pipefail

if [[ $# -ne 1 ]]; then
    echo "Usage: $0 <ndjson-path>" >&2
    exit 3
fi
NDJSON="$1"
if [[ ! -f "$NDJSON" ]]; then
    echo "error: not a file: $NDJSON" >&2
    exit 3
fi

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LF_DIR="$REPO_ROOT/lf"
PARSE="$REPO_ROOT/src/parse.ts"
GENERATE="$REPO_ROOT/src/generate-twelf.ts"
TWELF="${TWELF:-$REPO_ROOT/.twelf/bin/twelf-server}"

if [[ ! -x "$TWELF" ]]; then
    echo "error: twelf-server not executable at \$TWELF=$TWELF" >&2
    exit 3
fi

# Sanity: the trusted base must be where we expect — otherwise we'd silently
# load whatever Twelf finds via its search path.
for f in nat.elf levels.elf tcb.elf freeze.elf derived.elf final-checks.elf; do
    if [[ ! -f "$LF_DIR/$f" ]]; then
        echo "error: missing $LF_DIR/$f" >&2
        exit 3
    fi
done

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
JSON="$tmp/env.json"
FULL="$tmp/env.full.elf"

# Stage 1: parse + generate.  Any failure here is "we can't pose the question"
# → decline.  Mirrors the SKIP path in scripts/gen-tests.sh.
if ! "$PARSE" < "$NDJSON" > "$JSON" 2>/dev/null; then
    exit 2
fi
if ! "$GENERATE" --prover real < "$JSON" > "$FULL" 2>/dev/null; then
    exit 2
fi
# Generator's own self-skip marker (env outside what the translator handles).
# The marker can appear on any line (the generator emits axiom/inductive
# preamble before deciding to skip a later declaration), so scan the whole
# file — matching scripts/check-tests.sh's `grep -qa "^%%% SKIP"`.  Checking
# only `head -1` here silently misclassified such declines as accepts.
if grep -q "^%%% SKIP" "$FULL"; then
    exit 2
fi

# Stage 2: frozen load.  Twelf-server takes commands on stdin; cd into $LF_DIR
# so the relative loadFile paths (tcb.elf, freeze.elf, derived.elf,
# final-checks.elf) resolve; pass $FULL absolutely.  An ABORT line in the
# transcript marks any load failure.
run_twelf() {
    local script="$1"
    local out
    out="$(cd "$LF_DIR" && printf '%s\n' "$script" | "$TWELF" 2>&1)"
    if [[ -z "$out" ]]; then
        echo "error: twelf-server produced no output" >&2
        exit 3
    fi
    printf '%s' "$out"
}

frozen_script="loadFile nat.elf
loadFile levels.elf
loadFile tcb.elf
set unsafe true
loadFile freeze.elf
set unsafe false
loadFile derived.elf
loadFile $FULL
loadFile final-checks.elf
OS.exit"

frozen_out="$(run_twelf "$frozen_script")"
if ! grep -q ABORT <<< "$frozen_out"; then
    exit 0   # accept
fi

# Stage 3: unfrozen load — disambiguate holes (decline) vs concrete error
# (reject).  Same chain minus freeze.  An accept here means the only thing
# the frozen load was rejecting were unfilled HOLEs.
unfrozen_script="loadFile nat.elf
loadFile levels.elf
loadFile tcb.elf
loadFile derived.elf
loadFile $FULL
loadFile final-checks.elf
OS.exit"

unfrozen_out="$(run_twelf "$unfrozen_script")"
if grep -q ABORT <<< "$unfrozen_out"; then
    exit 1   # reject — concrete error or fail-on-purpose
fi
exit 2       # decline — only unfilled HOLEs
