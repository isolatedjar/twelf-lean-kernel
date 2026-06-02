#!/usr/bin/env bash
# scripts/gen-tests.sh
#
# Regenerate lf/tests/*.elf from the lean-kernel-arena test NDJSONs.
#
# We keep no copy of the tests in this repo: the arena is the source of truth
# and is assumed to live at ../lean-kernel-arena (override with $ARENA).  Run
# ./scripts/build-arena-ndjson.sh first to populate $ARENA/_build/tests/; this
# script reads those NDJSONs directly.
#
# A test is any *.ndjson under $ARENA/_build/tests/ that has a sibling
# <name>.stats.json carrying an `outcome` field.  That requirement is what
# distinguishes a finished test output from the arena's `work/` intermediates,
# and it gives us the accept/reject verdict and description uniformly for both
# the tutorial subtests and the singleton tests.  NDJSONs larger than 10 MB are
# skipped (mirroring the arena's own tarball policy).
#
# Usage:
#   ./scripts/gen-tests.sh            # regenerate everything
#   ./scripts/gen-tests.sh 001 003    # regenerate only these tutorial test numbers
#
# Each output file gets:
#   %%% Expected outcome: accept | reject
#   %%% <description from .stats.json>
#   ... translator output ...

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PARSE_NDJSON="$REPO_ROOT/src/parse.ts"
GENERATE="$REPO_ROOT/src/generate-twelf.ts"
OUT_DIR="$REPO_ROOT/lf/tests"
ARENA="${ARENA:-$REPO_ROOT/../lean-kernel-arena}"
SRC="$ARENA/_build/tests"

MAX_BYTES=$((10 * 1024 * 1024))   # arena tarball policy: skip NDJSONs > 10 MB

if [[ ! -d "$SRC" ]]; then
    echo "error: no arena test build at '$SRC'." >&2
    echo "       Run ./scripts/build-arena-ndjson.sh first (and check \$ARENA)." >&2
    exit 2
fi

mkdir -p "$OUT_DIR"

# On a full run (no test-number filter), wipe the output dir so it ends up an
# exact mirror of the current arena test set — otherwise stale `.elf` from tests
# the arena has since renamed or removed would linger and be checked.  A
# filtered run (args given) only touches the matching tests, so leave the rest.
if [[ $# -eq 0 ]]; then
    rm -f "$OUT_DIR"/*.full.elf "$OUT_DIR"/*.render.elf "$OUT_DIR"/*.json
fi

# If test-number args given, build a regex like ^(001|003)_
if [[ $# -gt 0 ]]; then
    pattern="^($(IFS='|'; echo "$*"))_"
else
    pattern="."
fi

# Read one field from a JSON file (prints empty string if absent/null).
json_field() {
    local file="$1" field="$2"
    node -e "const v=JSON.parse(require('fs').readFileSync('$file','utf8'))['$field']; if (v!=null) process.stdout.write(String(v));"
}

n_ok=0
n_skip=0

# Write a SKIP stub when a test can't be represented (parse or generate failed,
# or it was filtered out by size).  check-tests.sh classifies a `.full.elf`
# whose body starts with `%%% SKIP` as 🤷, so the test still shows up in the
# report rather than silently vanishing — and one broken input never aborts the
# whole run.
write_skip() {
    local out_full="$1" out_render="$2" outcome="$3" description="$4" reason="$5" base="$6"
    {
        echo "%%% Expected outcome: $outcome"
        [[ -n "$description" ]] && printf '%s\n' "$description" | sed 's/^/%%% /'
        echo "%%% SKIP: $reason"
    } > "$out_full"
    {
        echo "%%% Render-only view of: $base (skipped)"
        echo "%%% SKIP: $reason"
    } > "$out_render"
}

gen_one() {
    local ndjson="$1"
    local stats="${ndjson%.ndjson}.stats.json"

    # Only finished test outputs have a stats file with an `outcome`; this also
    # filters out stray NDJSONs that aren't arena tests.  Use `return 0` so a
    # non-test file is skipped silently without tripping `set -e`.
    [[ -f "$stats" ]] || return 0
    local outcome
    outcome="$(json_field "$stats" outcome)"
    [[ -n "$outcome" ]] || return 0

    local base
    base="$(basename "$ndjson" .ndjson)"

    # Apply tutorial test-number filter when args were given.
    if [[ "$pattern" != "." ]] && ! echo "$base" | grep -qE "$pattern"; then
        return
    fi

    local description
    description="$(json_field "$stats" description)"

    local out_json="$OUT_DIR/${base}.json"
    local out_full="$OUT_DIR/${base}.full.elf"
    local out_render="$OUT_DIR/${base}.render.elf"

    # Mirror the arena tarball's 10 MB cap.
    local bytes
    bytes="$(wc -c < "$ndjson")"
    if (( bytes > MAX_BYTES )); then
        write_skip "$out_full" "$out_render" "$outcome" "$description" \
            "input is ${bytes} bytes (> 10 MB cap)" "$base"
        printf "  %-45s  -> SKIP (%d bytes > 10 MB)\n" "$base" "$bytes"
        (( n_skip++ )) || true
        return
    fi

    # Parse NDJSON → JSON IR.  A failure here (e.g. a parser crash on some
    # input) must not abort the whole run.
    if ! "$PARSE_NDJSON" < "$ndjson" > "$out_json" 2>/dev/null; then
        write_skip "$out_full" "$out_render" "$outcome" "$description" \
            "parse.ts failed on this input" "$base"
        printf "  %-45s  -> SKIP (parse.ts failed)\n" "$base"
        (( n_skip++ )) || true
        return
    fi

    # Both files come from the SAME generator (generate-twelf.ts), differing
    # only in the Prover plugged in:
    #   .full.elf   — RealProver (discharges what it can; HOLEs otherwise)
    #   .render.elf — NullProver (every obligation a HOLE)
    local full_body render_body
    if ! full_body="$("$GENERATE" --prover real < "$out_json" 2>/dev/null)" \
       || ! render_body="$("$GENERATE" --prover null < "$out_json" 2>/dev/null)"; then
        write_skip "$out_full" "$out_render" "$outcome" "$description" \
            "generate-twelf.ts failed on this input" "$base"
        printf "  %-45s  -> SKIP (generate-twelf.ts failed)\n" "$base"
        (( n_skip++ )) || true
        return
    fi

    {
        echo "%%% Expected outcome: $outcome"
        [[ -n "$description" ]] && printf '%s\n' "$description" | sed 's/^/%%% /'
        printf '%s\n' "$full_body"
    } > "$out_full"

    {
        echo "%%% Render-only view of: $base"
        [[ -n "$description" ]] && printf '%s\n' "$description" | sed 's/^/%%% /'
        printf '%s\n' "$render_body"
    } > "$out_render"

    printf "  %-45s  -> %s, %s\n" "$base" "$(basename "$out_full")" "$(basename "$out_render")"
    (( n_ok++ )) || true
}

echo "Generating tests from $SRC ..."
while IFS= read -r -d '' ndjson; do
    gen_one "$ndjson"
done < <(find "$SRC" -type f -name '*.ndjson' -not -path '*/work/*' -print0 | sort -z)

echo "Done. Output in $OUT_DIR/  ($n_ok generated, $n_skip skipped)"
