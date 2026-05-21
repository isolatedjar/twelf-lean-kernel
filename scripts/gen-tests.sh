#!/usr/bin/env bash
# scripts/gen-tests.sh
#
# Regenerate lf/tests/*.elf from tests/tutorial/{good,bad}/*.ndjson.
#
# Usage:
#   ./scripts/gen-tests.sh            # regenerate everything
#   ./scripts/gen-tests.sh 001 003    # regenerate only these test numbers
#
# Each output file gets:
#   %%% Expected outcome: accept | reject
#   %%% <description from .info.json>
#   ... translator output ...

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PARSE_NDJSON="$REPO_ROOT/src/parse.ts"
LEAN_TO_LF="$REPO_ROOT/src/lean2lf.ts"
RENDER_CLI="$REPO_ROOT/src/render-cli.ts"
OUT_DIR="$REPO_ROOT/lf/tests"
GOOD_DIR="$REPO_ROOT/tests/tutorial/good"
BAD_DIR="$REPO_ROOT/tests/tutorial/bad"

mkdir -p "$OUT_DIR"

# One-time cleanup: remove any leftover single-name `.elf` files from
# before the .full.elf / .render.elf split.  Keep new-style outputs.
if [[ $# -eq 0 ]]; then
    for old in "$OUT_DIR"/*.elf; do
        [[ -f "$old" ]] || continue
        name="$(basename "$old")"
        case "$name" in
            *.full.elf|*.render.elf) ;;
            *) rm -f "$old" ;;
        esac
    done
fi

# If test-number args given, build a regex like ^(001|003)_
if [[ $# -gt 0 ]]; then
    pattern="^($(IFS='|'; echo "$*"))_"
else
    pattern="."
fi

gen_one() {
    local ndjson="$1"
    local outcome="$2"      # "accept" or "reject"

    local base
    base="$(basename "$ndjson" .ndjson)"

    # Apply number filter when args were given.
    if [[ $# -gt 2 ]]; then
        if ! echo "$base" | grep -qE "$pattern"; then
            return
        fi
    fi

    local info
    info="${ndjson%.ndjson}.info.json"
    local description=""
    if [[ -f "$info" ]]; then
        description="$(node -e "process.stdout.write(JSON.parse(require('fs').readFileSync('$info','utf8')).description)")"
    fi

    local out_json="$OUT_DIR/${base}.json"
    local out_full="$OUT_DIR/${base}.full.elf"
    local out_render="$OUT_DIR/${base}.render.elf"

    {
        "$PARSE_NDJSON" < "$ndjson"
    } > "$out_json"

    # Full pipeline: rendering + proof construction.  This is what
    # check-tests.sh runs through Twelf.
    {
        echo "%%% Expected outcome: $outcome"
        [[ -n "$description" ]] && printf '%s\n' "$description" | sed 's/^/%%% /'
        "$LEAN_TO_LF" < "$out_json"
    } > "$out_full"

    # Render-only view: pure encoding artifact for human audit.  Binds
    # each Lean declaration's rendered shape as a Twelf constant, with
    # no proof obligations.
    {
        echo "%%% Render-only view of: $base"
        [[ -n "$description" ]] && printf '%s\n' "$description" | sed 's/^/%%% /'
        "$RENDER_CLI" < "$out_json"
    } > "$out_render"

    printf "  %-45s  -> %s, %s\n" "$base" "$(basename "$out_full")" "$(basename "$out_render")"
}

echo "Generating good tests..."
for f in "$GOOD_DIR"/*.ndjson; do
    [[ -f "$f" ]] || continue
    gen_one "$f" "accept" "$@"
done

echo "Generating bad tests..."
for f in "$BAD_DIR"/*.ndjson; do
    [[ -f "$f" ]] || continue
    gen_one "$f" "reject" "$@"
done

echo "Done. Output in $OUT_DIR/"