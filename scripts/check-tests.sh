#!/usr/bin/env bash
# scripts/check-tests.sh
#
# Run all lf/tests/*.elf through Twelf and report results.
#
# Usage:
#   ./scripts/check-tests.sh <twelf-binary>
#   ./scripts/check-tests.sh <twelf-binary> lf/tests/001_*.elf   # subset
#
# Output columns:
#   <name>   expected <✅|❌>   got <✅|❌|🤷>   <verdict>
#
# Verdict key:
#   ✅  correct (got matches expected, no skips)
#   ⚠️   incomplete (translator emitted ≥1 %% SKIP:)
#   ❌  failed a good test (expected accept, got reject)
#   💥  passed a bad test  (expected reject, got accept) — most dangerous

set -euo pipefail

# ---------------------------------------------------------------------------
# Args
# ---------------------------------------------------------------------------

TWELF="${1:-}"
if [[ -z "$TWELF" ]]; then
    echo "Usage: $0 <twelf-binary> [test-files...]" >&2
    exit 1
fi
if [[ ! -x "$TWELF" ]]; then
    echo "Error: not executable: $TWELF" >&2
    exit 1
fi
# Resolve to absolute so we don't lose it when we cd into $LF_DIR.
TWELF="$(cd "$(dirname "$TWELF")" && pwd)/$(basename "$TWELF")"
shift  # remaining args, if any, are specific test files

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LF_DIR="$REPO_ROOT/lf"
TESTS_DIR="$LF_DIR/tests"

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

# Run one .elf file through Twelf.  Prints: accept | reject | incomplete
check_one() {
    local file="$1"

    # Incomplete if translator marked any skipped declarations.
    if grep -q "^%% SKIP:" "$file" 2>/dev/null; then
        echo "incomplete"
        return
    fi

    local abs_file
    abs_file="$(cd "$(dirname "$file")" && pwd)/$(basename "$file")"

    local output
    output=$(
        cd "$LF_DIR"
        echo "Config.read sources.cfg
Config.load
loadFile $abs_file
OS.exit" | "$TWELF" 2>&1
    )

    if echo "$output" | grep -q "ABORT"; then
        echo "reject"
    else
        echo "accept"
    fi
}

# ---------------------------------------------------------------------------
# Collect test files
# ---------------------------------------------------------------------------

if [[ $# -gt 0 ]]; then
    test_files=("$@")
else
    test_files=("$TESTS_DIR"/*.elf)
fi

# ---------------------------------------------------------------------------
# Run and collect results
# ---------------------------------------------------------------------------

# Width of the longest basename (for alignment).
max_len=0
for f in "${test_files[@]}"; do
    len=${#f}
    base="$(basename "$f")"
    len=${#base}
    (( len > max_len )) && max_len=$len
done
# Cap so lines don't blow out on wide names.
(( max_len > 50 )) && max_len=50

n_correct=0
n_incomplete=0
n_fail_good=0
n_pass_bad=0
n_no_header=0

echo ""

for file in "${test_files[@]}"; do
    [[ -f "$file" ]] || continue

    base="$(basename "$file")"

    # Read expected outcome from header.
    expected_raw="$(grep -i "^%%% Expected outcome:" "$file" | head -1 | \
                    sed 's/^.*: *//' | tr -d ' \r' | tr '[:upper:]' '[:lower:]')"

    if [[ -z "$expected_raw" ]]; then
        printf "  %-*s  (no expected outcome header — skipped)\n" "$max_len" "$base"
        (( n_no_header++ )) || true
        continue
    fi

    # expected emoji
    case "$expected_raw" in
        accept) exp_emoji="✅" ;;
        reject) exp_emoji="❌" ;;
        *)      exp_emoji="?" ;;
    esac

    # Run the check.
    got="$(check_one "$file")"

    # got emoji
    case "$got" in
        accept)     got_emoji="✅" ;;
        reject)     got_emoji="❌" ;;
        incomplete) got_emoji="🤷" ;;
        *)          got_emoji="?" ;;
    esac

    # Verdict.
    if [[ "$got" == "incomplete" ]]; then
        verdict="⚠️ "
        (( n_incomplete++ )) || true
    elif [[ "$expected_raw" == "$got" ]]; then
        verdict="✅"
        (( n_correct++ )) || true
    elif [[ "$expected_raw" == "reject" && "$got" == "accept" ]]; then
        verdict="💥"
        (( n_pass_bad++ )) || true
    else
        verdict="❌"
        (( n_fail_good++ )) || true
    fi

    printf "  %-*s  expected %s  got %s  %s\n" \
        "$max_len" "$base" "$exp_emoji" "$got_emoji" "$verdict"
done

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------

total=$(( n_correct + n_incomplete + n_fail_good + n_pass_bad ))

echo ""
echo "  ────────────────────────────────────────"
printf "  %d tests\n" "$total"
[[ $n_correct    -gt 0 ]] && printf "  ✅  correct:          %d\n" "$n_correct"
[[ $n_incomplete -gt 0 ]] && printf "  ⚠️   incomplete:        %d\n" "$n_incomplete"
[[ $n_fail_good  -gt 0 ]] && printf "  ❌  failed good test:  %d\n" "$n_fail_good"
[[ $n_pass_bad   -gt 0 ]] && printf "  💥  passed bad test:   %d\n" "$n_pass_bad"
[[ $n_no_header  -gt 0 ]] && printf "  ?   no header:         %d\n" "$n_no_header"
echo ""

# Exit non-zero if anything is wrong (💥 or ❌).
if [[ $(( n_fail_good + n_pass_bad )) -gt 0 ]]; then
    exit 1
fi