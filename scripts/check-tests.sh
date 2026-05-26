#!/usr/bin/env bash
# scripts/check-tests.sh
#
# Classify each generated test under the plugin-refactor taxonomy by
# loading its .render.elf / .full.elf through Twelf with and without the
# %freeze step.
#
# Usage:
#   ./scripts/check-tests.sh <twelf-binary>
#   ./scripts/check-tests.sh <twelf-binary> 030 056      # subset by number
#
# Outcomes (per test), in precedence order:
#   🤷  generator declined to represent the env  (.full.elf has %%% SKIP)
#   🔴  .render.elf rejected by Twelf without freeze (rendering is broken)
#   ✅  .full.elf accepted by the full pipeline (freeze + final-checks)
#   🩹  .full.elf rejected with freeze but accepted without freeze
#       (the only failures are unfilled HOLEs)
#   ❌  .full.elf rejected even without freeze (a genuine error)
#
# Verdict per expected outcome:
#   good (expect accept):  ✅→pass   🩹→incomplete   🤷/🔴/❌→fail
#   bad  (expect reject):  ✅→💥      🩹→incomplete   🤷/🔴/❌→pass(reject)

set -euo pipefail

TWELF="${1:-}"
if [[ -z "$TWELF" ]]; then
    echo "Usage: $0 <twelf-binary> [test-numbers...]" >&2
    exit 1
fi
if [[ ! -x "$TWELF" ]]; then
    echo "Error: not executable: $TWELF" >&2
    exit 1
fi
TWELF="$(cd "$(dirname "$TWELF")" && pwd)/$(basename "$TWELF")"
shift

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LF_DIR="$REPO_ROOT/lf"
TESTS_DIR="$LF_DIR/tests"

for f in tcb.elf freeze.elf derived.elf final-checks.elf; do
    if [[ ! -f "$LF_DIR/$f" ]]; then
        echo "Error: $LF_DIR/$f is missing." >&2
        exit 1
    fi
done

# ---------------------------------------------------------------------------
# Twelf load helpers.  Each prints "accept" or "reject".
# ---------------------------------------------------------------------------

# Run a Twelf session from a heredoc-style command string; "reject" if the
# output contains ABORT, else "accept".
run_twelf() {
    local script="$1"
    local tmp
    tmp=$(mktemp)
    set +e
    ( cd "$LF_DIR" && printf '%s\n' "$script" | "$TWELF" ) > "$tmp" 2>&1
    set -e
    if [[ ! -s "$tmp" ]]; then
        echo "ERROR: Twelf produced no output" >&2
        rm -f "$tmp"
        exit 1
    fi
    if grep -q "ABORT" "$tmp"; then echo "reject"; else echo "accept"; fi
    rm -f "$tmp"
}

# .render.elf without freeze or final-checks.
load_render_nofreeze() {
    run_twelf "loadFile tcb.elf
loadFile derived.elf
loadFile $1
OS.exit"
}

# .full.elf through the full pipeline (freeze + final-checks).
load_full_freeze() {
    run_twelf "loadFile tcb.elf
set unsafe true
loadFile freeze.elf
set unsafe false
loadFile derived.elf
loadFile $1
loadFile final-checks.elf
OS.exit"
}

# .full.elf with the freeze step skipped (final-checks still loaded).
load_full_nofreeze() {
    run_twelf "loadFile tcb.elf
loadFile derived.elf
loadFile $1
loadFile final-checks.elf
OS.exit"
}

# Classify one test → one of: shrug | red | accept | holes | fail
classify() {
    local full="$1" render="$2"
    if grep -q "^%%% SKIP" "$full" 2>/dev/null; then echo "shrug"; return; fi
    [[ "$(load_render_nofreeze "$render")" == "reject" ]] && { echo "red"; return; }
    # %freeze-based HOLE detection is currently unsound: %thaw name transitively
    # thaws defeq (defeq/const and defeq/delta take a `declared` premise, which
    # depends on `name`), so the frozen load wrongly accepts type-wf/value-typed
    # obligations left as HOLEs. Until Twelf's thaw semantics are patched to thaw
    # only the `name` class, simulate the freeze rejection here: a file with an
    # unfilled HOLE is treated as if the frozen load rejected it. NOTE: this is a
    # cooperative stand-in, not a soundness guarantee — an adversarial generator
    # could emit a proof without the marker. It only unblocks the honest pipeline.
    if ! grep -q "^%%% HOLE" "$full" 2>/dev/null; then
        [[ "$(load_full_freeze "$full")" == "accept" ]] && { echo "accept"; return; }
    fi
    [[ "$(load_full_nofreeze "$full")" == "accept" ]] && { echo "holes"; return; }
    echo "fail"
}

# ---------------------------------------------------------------------------
# Collect test bases (those with a .full.elf).
# ---------------------------------------------------------------------------

if [[ $# -gt 0 ]]; then
    pattern="^($(IFS='|'; echo "$*"))_"
else
    pattern="."
fi

bases=()
for f in "$TESTS_DIR"/*.full.elf; do
    [[ -f "$f" ]] || continue
    b="$(basename "$f" .full.elf)"
    echo "$b" | grep -qE "$pattern" && bases+=("$b")
done

max_len=0
for b in "${bases[@]}"; do (( ${#b} > max_len )) && max_len=${#b}; done
(( max_len > 50 )) && max_len=50

# good = expected accept; bad = expected reject
g_pass=0 g_holes=0 g_fail=0
b_reject=0 b_holes=0 b_accept=0
n_no_header=0

echo ""
for b in "${bases[@]}"; do
    full="$TESTS_DIR/$b.full.elf"
    render="$TESTS_DIR/$b.render.elf"

    expected="$(grep -i "^%%% Expected outcome:" "$full" | head -1 | \
                sed 's/^.*: *//' | tr -d ' \r' | tr '[:upper:]' '[:lower:]')"
    if [[ -z "$expected" ]]; then
        printf "  %-*s  (no expected-outcome header)\n" "$max_len" "$b"
        (( n_no_header++ )) || true
        continue
    fi

    outcome="$(classify "$full" "$render")"
    case "$outcome" in
        shrug)  emoji="🤷" ;;
        red)    emoji="🔴" ;;
        accept) emoji="✅" ;;
        holes)  emoji="🩹" ;;
        fail)   emoji="❌" ;;
    esac

    if [[ "$expected" == "accept" ]]; then
        case "$outcome" in
            accept) verdict="✅"; (( g_pass++ ))  || true ;;
            holes)  verdict="🩹"; (( g_holes++ )) || true ;;
            *)      verdict="❌"; (( g_fail++ ))  || true ;;
        esac
    else
        case "$outcome" in
            accept) verdict="💥"; (( b_accept++ )) || true ;;
            holes)  verdict="🩹"; (( b_holes++ ))  || true ;;
            *)      verdict="✅"; (( b_reject++ )) || true ;;
        esac
    fi

    printf "  %-*s  expect %-6s  %s  %s\n" "$max_len" "$b" "$expected" "$emoji" "$verdict"
done

n_good=$(( g_pass + g_holes + g_fail ))
n_bad=$(( b_reject + b_holes + b_accept ))

echo ""
echo "  ────────────────────────────────────────"
printf "  %d tests\n\n" "$(( n_good + n_bad ))"
printf "  Good tests (expected accept) — %d total:\n" "$n_good"
printf "    ✅  pass:        %d\n" "$g_pass"
printf "    🩹  with-holes:  %d\n" "$g_holes"
printf "    ❌  failed:      %d  (🤷 / 🔴 / genuine reject)\n" "$g_fail"
echo ""
printf "  Bad tests (expected reject) — %d total:\n" "$n_bad"
printf "    ✅  reject:      %d  (🤷 / 🔴 / genuine reject)\n" "$b_reject"
printf "    🩹  with-holes:  %d\n" "$b_holes"
printf "    💥  accept:      %d  (soundness failure)\n" "$b_accept"
[[ $n_no_header -gt 0 ]] && printf "  ?   no header:    %d\n" "$n_no_header"
echo ""

# Non-zero exit on a genuine good-test failure or a soundness failure.
if [[ $(( g_fail + b_accept )) -gt 0 ]]; then exit 1; fi
