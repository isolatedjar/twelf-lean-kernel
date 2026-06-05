#!/usr/bin/env bash
# scripts/check-soundness.sh
#
# Run the hand-written soundness regressions in lf/soundness/*.elf.
#
# Unlike scripts/check-tests.sh (which drives the NDJSON → generator → Twelf
# pipeline), these files are ADVERSARIAL developments written by hand: each
# models an attack a buggy or malicious translator could attempt, and must be
# REJECTED by the trusted base alone.  Loading one through the full chain
#
#   tcb.elf -> freeze.elf -> derived.elf -> <attack>.elf -> final-checks.elf
#
# must ABORT (Twelf prints "%% ABORT %%").  If any attack loads clean, that is
# a soundness failure and the script exits non-zero.
#
# Usage:
#   ./scripts/check-soundness.sh [/path/to/twelf-server]

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LF_DIR="$REPO_ROOT/lf"
SND_DIR="$LF_DIR/soundness"
TWELF="${1:-/home/user/twelf-src/bin/twelf-server}"

if [[ ! -x "$TWELF" ]]; then
    echo "twelf-server not found/executable: $TWELF" >&2
    exit 2
fi

run_full_chain() {
    # Load the full trusted chain plus the attack file, capture all output.
    printf 'loadFile nat.elf\nloadFile levels.elf\nloadFile tcb.elf\nset unsafe true\nloadFile freeze.elf\nset unsafe false\nloadFile derived.elf\nloadFile %s\nloadFile final-checks.elf\nOS.exit\n' "$1" \
        | (cd "$LF_DIR" && "$TWELF" 2>&1)
}

fail=0
count=0
echo ""
for f in "$SND_DIR"/*.elf; do
    [[ -f "$f" ]] || continue
    (( count++ )) || true
    name="$(basename "$f")"
    out="$(run_full_chain "$f")"
    if grep -q "%% ABORT %%" <<<"$out"; then
        printf "  %-45s  ✅ rejected (ABORT)\n" "$name"
    else
        printf "  %-45s  💥 ACCEPTED — SOUNDNESS FAILURE\n" "$name"
        echo "    ---- twelf output ----"
        sed 's/^/    /' <<<"$out" | tail -20
        fail=1
    fi
done

echo ""
if [[ "$count" -eq 0 ]]; then
    echo "  (no soundness regressions found in $SND_DIR)"
elif [[ "$fail" -eq 0 ]]; then
    echo "  All $count soundness regression(s) correctly rejected."
else
    echo "  SOUNDNESS REGRESSION FAILED."
fi
echo ""
exit "$fail"
