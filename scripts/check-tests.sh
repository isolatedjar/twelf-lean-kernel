#!/usr/bin/env bash
# scripts/check-tests.sh
#
# Run all lf/tests/*.elf through Twelf and report results.
#
# Usage:
#   ./scripts/check-tests.sh <twelf-binary>
#   ./scripts/check-tests.sh <twelf-binary> lf/tests/001_*.full.elf   # subset
#
# Only *.full.elf files are checked.  *.render.elf files are a separate
# pure-encoding artifact (no proofs) and are not Twelf-verified here.
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

# Loud startup checks.  The previous version silently mis-reported
# tests as "accept" when `cd "$LF_DIR"` failed inside the subshell:
# `set -e` exited the inner shell, output came back empty, and
# `grep -q ABORT` found nothing — making genuine rejections look
# like soundness failures.  We now refuse to run if the layout
# isn't right.
if [[ ! -d "$LF_DIR" ]]; then
    echo "Error: LF_DIR=$LF_DIR does not exist." >&2
    echo "  This script expects <repo-root>/lf/{sources.cfg,final-checks.elf,tests/...}." >&2
    exit 1
fi
if [[ ! -f "$LF_DIR/sources.cfg" ]]; then
    echo "Error: $LF_DIR/sources.cfg is missing." >&2
    exit 1
fi
if [[ ! -f "$LF_DIR/final-checks.elf" ]]; then
    echo "Error: $LF_DIR/final-checks.elf is missing." >&2
    echo "  Note: if you grabbed it from /mnt/user-data/outputs it may be" >&2
    echo "  named final-checks.elf.txt — rename to final-checks.elf." >&2
    exit 1
fi

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

# Run one .elf file through Twelf.  Prints: accept | reject | incomplete
# Loud-fail on infrastructure errors (Twelf binary missing, no output, etc.)
# rather than silently returning a wrong verdict.
check_one() {
    local file="$1"

    # Incomplete if translator marked any skipped declarations.
    if grep -q "^%% SKIP:" "$file" 2>/dev/null; then
        echo "incomplete"
        return 0
    fi

    local abs_file
    abs_file="$(cd "$(dirname "$file")" && pwd)/$(basename "$file")"

    # Capture Twelf output via tempfile.  Disable `set -e` for the
    # block so we can detect failures explicitly rather than silently
    # aborting the subshell.
    local tmpfile
    tmpfile=$(mktemp)
    set +e
    (
        cd "$LF_DIR" || exit 64
        echo "Config.read sources.cfg
Config.load
loadFile $abs_file
loadFile final-checks.elf
OS.exit" | "$TWELF"
    ) > "$tmpfile" 2>&1
    local rc=$?
    set -e

    if [[ $rc -eq 64 ]]; then
        echo "ERROR: cd to LF_DIR=$LF_DIR failed" >&2
        rm -f "$tmpfile"
        exit 1
    fi
    if [[ ! -s "$tmpfile" ]]; then
        echo "ERROR: Twelf produced no output for $file (exit=$rc)" >&2
        rm -f "$tmpfile"
        exit 1
    fi

    if grep -q "ABORT" "$tmpfile"; then
        rm -f "$tmpfile"
        echo "reject"
    else
        rm -f "$tmpfile"
        echo "accept"
    fi
}

# ---------------------------------------------------------------------------
# Collect test files
# ---------------------------------------------------------------------------

if [[ $# -gt 0 ]]; then
    test_files=("$@")
else
    test_files=("$TESTS_DIR"/*.full.elf)
fi

# ---------------------------------------------------------------------------
# Run and collect results
# ---------------------------------------------------------------------------

# Width of the longest basename (for alignment).
max_len=0
for f in "${test_files[@]}"; do
    len=${#f}
    base="$(basename "$f" .full.elf)"
    len=${#base}
    (( len > max_len )) && max_len=$len
done
# Cap so lines don't blow out on wide names.
(( max_len > 50 )) && max_len=50

n_good_pass=0
n_good_incomp=0
n_good_fail=0
n_bad_pass=0
n_bad_incomp=0
n_bad_fail=0
n_no_header=0

echo ""

for file in "${test_files[@]}"; do
    [[ -f "$file" ]] || continue

    base="$(basename "$file" .full.elf)"

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

    # Verdict.  Track good/bad cases separately so that "should reject"
    # tests in INCOMPLETE state are visibly distinct from genuine Twelf
    # rejections.
    if [[ "$expected_raw" == "accept" ]]; then
        case "$got" in
            accept)     verdict="✅"; (( n_good_pass++ ))  || true ;;
            incomplete) verdict="⚠️ "; (( n_good_incomp++ )) || true ;;
            *)          verdict="❌"; (( n_good_fail++ ))  || true ;;
        esac
    elif [[ "$expected_raw" == "reject" ]]; then
        case "$got" in
            reject)     verdict="✅"; (( n_bad_pass++ ))   || true ;;
            incomplete) verdict="⚠️ "; (( n_bad_incomp++ )) || true ;;
            *)          verdict="💥"; (( n_bad_fail++ ))   || true ;;
        esac
    fi

    printf "  %-*s  expected %s  got %s  %s\n" \
        "$max_len" "$base" "$exp_emoji" "$got_emoji" "$verdict"
done

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------

n_good=$(( n_good_pass + n_good_incomp + n_good_fail ))
n_bad=$((  n_bad_pass  + n_bad_incomp  + n_bad_fail  ))
total=$(( n_good + n_bad ))

echo ""
echo "  ────────────────────────────────────────"
printf "  %d tests\n" "$total"
echo ""
printf "  Good tests (expected accept) — %d total:\n" "$n_good"
printf "    ✅  pass:        %d\n" "$n_good_pass"
printf "    ⚠️   incomplete:  %d\n" "$n_good_incomp"
printf "    ❌  failed:      %d\n" "$n_good_fail"
echo ""
printf "  Bad tests (expected reject) — %d total:\n" "$n_bad"
printf "    ✅  reject:      %d\n" "$n_bad_pass"
printf "    ⚠️   incomplete:  %d  (translator declined — not Twelf-verified)\n" "$n_bad_incomp"
printf "    💥  accept:      %d\n" "$n_bad_fail"
[[ $n_no_header -gt 0 ]] && printf "  ?   no header:         %d\n" "$n_no_header"
echo ""

# Exit non-zero if anything wrong (good ❌ or bad 💥).
if [[ $(( n_good_fail + n_bad_fail )) -gt 0 ]]; then
    exit 1
fi