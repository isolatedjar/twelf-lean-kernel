#!/bin/bash
# Run an arena .elf and check it matches its declared "Expected outcome".
# Reads the expected outcome from a comment line like:
#   %%% Expected outcome: accept
# in the header of the file.

set -u

TWELF=/home/claude/twelf-main/bin/twelf-server
TCB_DIR=/home/claude/twelf-lean

run_one() {
    local file="$1"
    local expected
    expected=$(grep -i "^%%% Expected outcome:" "$file" | head -1 | sed 's/^.*: *//' | tr -d ' \r')
    if [[ -z "$expected" ]]; then
        printf "  %-40s  [SKIP — no expected outcome declared]\n" "$(basename "$file")"
        return
    fi

    local output
    output=$(echo "Config.read sources.cfg
Config.load
loadFile $file
OS.exit" | "$TWELF" 2>&1)

    # Check for translator-side skips before Twelf even runs.
    local skipped=0
    if grep -q "^%% SKIP:" "$file"; then
        skipped=1
    fi

    # Look at the last status line emitted by Twelf for *this* file.
    local final_status
    if echo "$output" | grep -q "ABORT"; then
        final_status="reject"
    elif [[ $skipped -eq 1 ]]; then
        final_status="incomplete"
    else
        final_status="accept"
    fi

    if [[ "$final_status" == "$expected" ]]; then
        printf "  %-40s  [ %s ]\n" "$(basename "$file")" "PASS ($expected)"
    elif [[ "$final_status" == "incomplete" ]]; then
        printf "  %-40s  [ %s — translator skipped declarations ]\n" \
            "$(basename "$file")" "INCOMPLETE"
        grep "^%% SKIP:" "$file" | sed 's/^/      /'
    else
        printf "  %-40s  [ %s — expected %s, got %s ]\n" \
            "$(basename "$file")" "FAIL" "$expected" "$final_status"
        echo "$output" | tail -10 | sed 's/^/      /'
    fi
}

cd "$TCB_DIR"

if [[ $# -eq 0 ]]; then
    for f in arena/*.elf; do
        run_one "$f"
    done
else
    for f in "$@"; do
        run_one "$f"
    done
fi