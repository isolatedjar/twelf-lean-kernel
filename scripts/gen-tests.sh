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
TRANSLATOR="$REPO_ROOT/src/lean2lf.ts"
OUT_DIR="$REPO_ROOT/lf/tests"
GOOD_DIR="$REPO_ROOT/tests/tutorial/good"
BAD_DIR="$REPO_ROOT/tests/tutorial/bad"

mkdir -p "$OUT_DIR"

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

    local out="$OUT_DIR/${base}.elf"

    {
        echo "%%% Expected outcome: $outcome"
        [[ -n "$description" ]] && echo "%%% $description"
        "$TRANSLATOR" < "$ndjson"
    } > "$out"

    printf "  %-45s  -> %s\n" "$base" "$(basename "$out")"
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