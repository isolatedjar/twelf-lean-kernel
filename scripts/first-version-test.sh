#!/usr/bin/env bash
#
# Trust-tracking harness for the v2 translator.
#
# For each .ndjson in the given directory, run translator + Twelf, parse
# the TRUST_SUMMARY block from the translator output, classify the case
# as one of:
#
#   verified         — Twelf OK; 0 axioms added; 0 translation errors.
#                      The of/defeq obligations for every Lean decl in
#                      the file are discharged by Twelf-checkable
#                      derivations.  No new trust.
#
#   partial          — Twelf OK; at least one axiom added, but no
#                      translation errors.  The file loads and at
#                      least one of-claim rests on an axiom rather
#                      than a derivation.
#
#   twelf_fail       — Twelf rejected the file (any %% ABORT) and the
#                      translator emitted a clean TRUST_SUMMARY with
#                      zero translation errors.  The Twelf-level
#                      rejection is the meaningful signal.
#
#   trans_fail       — Translator emitted at least one translation
#                      error during processing (recoverable error in
#                      a declaration).  The TRUST_SUMMARY was still
#                      reached, but downstream Twelf behaviour is not
#                      meaningful — the input was not fully
#                      translatable.  Checked BEFORE twelf_fail so a
#                      Twelf abort downstream of a translation error
#                      is attributed to the translation error.
#
#   translator_fail  — Translator never emitted a TRUST_SUMMARY block,
#                      indicating it crashed mid-stream.  No file-level
#                      verification was attempted.
#
# Mode is inferred from the basename of the directory:
#   .../good  → "verified" is the goal; "partial" is a soft pass.
#   .../bad   → "verified" is a SOUNDNESS BUG; everything else is fine.
#
# Usage:
#   ./run-tut4-trust.sh <dir-of-ndjsons>
#
# Required environment (set these before invocation; see README at the
# bottom of the file for typical paths):
#   PKG     directory containing lean2lf-v2.ts
#   SIG     path to lean-core-v2.elf
#   TWELF   path to twelf-server binary
#   MLTON   directory containing mlton binary (added to PATH)
#   LIBGMP  optional: directory containing libgmp.so.10 (for MLton)
#
# Output directory: $OUTDIR (default /tmp/arena-trust); per-case .elf
# and .log files are written there.

set -u

PKG=${PKG:-/home/claude/work/lean2lf-pkg}
SIG=${SIG:-/home/claude/work/lean-core-v2.elf}
TWELF=${TWELF:-/home/claude/work/twelf-main/bin/twelf-server}
MLTON=${MLTON:-/home/claude/work/mlton-20241230-1.amd64-linux.ubuntu-24.04_static/bin}
LIBGMP=${LIBGMP:-}
OUTDIR=${OUTDIR:-/tmp/arena-trust}

if [ $# -ne 1 ]; then
  echo "usage: $0 <dir-of-ndjsons>" >&2
  exit 2
fi
DIR="$1"
if [ ! -d "$DIR" ]; then
  echo "$0: not a directory: $DIR" >&2
  exit 2
fi

# Mode inference: directory's last path component.
MODE=$(basename "$DIR")

export PATH=$MLTON:$PATH
if [ -n "$LIBGMP" ]; then
  export LD_LIBRARY_PATH=$LIBGMP:${LD_LIBRARY_PATH:-}
fi

mkdir -p "$OUTDIR"

# Tallies.
v_count=0    # verified
p_count=0    # partial
tnf_count=0  # trans_fail
tf_count=0   # twelf_fail
xf_count=0   # translator_fail
soundness_bugs=()

# Header.
printf "%-32s %5s %5s %5s  %-16s  %s\n" \
  "name" "decls" "axiom" "terr" "classification" "first-error"
printf "%-32s %5s %5s %5s  %-16s  %s\n" \
  "----" "-----" "-----" "----" "--------------" "-----------"

shopt -s nullglob
for f in "$DIR"/*.ndjson; do
  name=$(basename "$f" .ndjson)
  elf="$OUTDIR/$name.elf"
  log="$OUTDIR/$name.log"

  # 1. Run translator.
  node --experimental-strip-types "$PKG/lean2lf-v2.ts" < "$f" > "$elf" 2>/dev/null

  # 2. Parse the trust summary.
  summary_present=$(grep -c '^% TRUST_SUMMARY' "$elf" 2>/dev/null); summary_present=${summary_present:-0}
  axioms=$(awk '/^% TRUST_FIELD axioms_added:/ { print $4 }' "$elf" | head -1)
  axioms=${axioms:-0}
  terrors=$(awk '/^% TRUST_FIELD translation_errors:/ { print $4 }' "$elf" | head -1)
  terrors=${terrors:-0}
  decls=$(grep -cE '^decl/n_' "$elf" 2>/dev/null); decls=${decls:-0}

  # 3. Run Twelf.
  { echo "loadFile $SIG"; echo "loadFile $elf"; echo "quit"; } \
    | "$TWELF" > "$log" 2>&1

  twelf_aborted=0
  reason=""
  if grep -q '%% ABORT' "$log"; then
    twelf_aborted=1
    errline=$(grep -n 'Error:' "$log" | head -1 | cut -d: -f1)
    if [ -n "$errline" ]; then
      reason=$(sed -n "$((errline+1))p" "$log")
    else
      reason="(unknown error)"
    fi
  fi

  # 4. Classify.
  #
  # Ordering matters: trans_fail wins over twelf_fail, since a Twelf
  # abort downstream of a translation error is attributed to the
  # translation error.  A file with both is reported as trans_fail.
  if [ "$summary_present" -eq 0 ]; then
    classification="translator_fail"
    xf_count=$((xf_count+1))
  elif [ "$terrors" -gt 0 ]; then
    classification="trans_fail"
    tnf_count=$((tnf_count+1))
  elif [ "$twelf_aborted" -eq 1 ]; then
    classification="twelf_fail"
    tf_count=$((tf_count+1))
  elif [ "$axioms" -gt 0 ]; then
    classification="partial"
    p_count=$((p_count+1))
  else
    classification="verified"
    v_count=$((v_count+1))
    if [ "$MODE" = "bad" ]; then
      soundness_bugs+=("$name")
    fi
  fi

  printf "%-32s %5d %5d %5d  %-16s  %s\n" \
    "$name" "$decls" "$axioms" "$terrors" "$classification" "$reason"
done

# Totals.
total=$((v_count + p_count + tnf_count + tf_count + xf_count))
echo
echo "=== Summary ($MODE, $total cases) ==="
printf "  verified         %4d   ( Twelf OK, no new axioms, no translator errors )\n"  "$v_count"
printf "  partial          %4d   ( Twelf OK, but some axioms added )\n"                  "$p_count"
printf "  trans_fail       %4d   ( translator emitted at least one translation error )\n" "$tnf_count"
printf "  twelf_fail       %4d   ( Twelf rejected the file )\n"                          "$tf_count"
printf "  translator_fail  %4d   ( translator crashed; no TRUST_SUMMARY emitted )\n"     "$xf_count"

# Mode-specific reporting.
if [ "$MODE" = "bad" ]; then
  echo
  if [ "${#soundness_bugs[@]}" -gt 0 ]; then
    echo "*** SOUNDNESS VIOLATIONS (${#soundness_bugs[@]}): bad tests that were fully verified"
    echo "*** Each of these is a Lean term that does NOT typecheck, but our pipeline"
    echo "*** accepted as fully verified without flagging an axiom or error.  This is a bug."
    for b in "${soundness_bugs[@]}"; do
      echo "    - $b"
    done
    exit 1
  else
    echo "Soundness check PASSED: no bad test was fully verified."
    echo "Every bad test was honestly rejected (twelf_fail, trans_fail, or translator_fail)"
    echo "or honestly partial (axiomatized)."
  fi
fi