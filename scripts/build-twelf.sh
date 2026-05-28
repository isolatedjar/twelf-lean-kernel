#!/usr/bin/env bash
# scripts/build-twelf.sh — (re)build the Twelf server binary this project needs.
#
# The harness (check-tests.sh) detects unfilled proof obligations by loading the
# environment against a frozen TCB: a HOLE is a bare declaration on a frozen
# family, which the freezing check rejects.  This requires `%thaw name` to thaw
# ONLY the `name` family (so environments can add `<decl>/name` reservations)
# and NOT its transitive dependents — otherwise `defeq` is re-thawed and unfilled
# `defeq` obligations are wrongly accepted.  Stock Twelf thaws transitively; the
# one-line fix lives on robsimmons/twelf `limited-thaw`
# (src/subordinate/subordinate.fun).  See README and CLAUDE.md.
#
# Requires MLton on PATH (build via `make mlton`).
# Usage:  ./scripts/build-twelf.sh [twelf-src-dir]   (default: /home/user/twelf-src)

set -euo pipefail

SRC="${1:-/home/user/twelf-src}"
FORK="https://github.com/robsimmons/twelf"
BRANCH="limited-thaw"

command -v mlton >/dev/null || { echo "error: mlton not found on PATH" >&2; exit 1; }

if [[ ! -d "$SRC/.git" ]]; then
    echo "Cloning $FORK into $SRC ..."
    git clone "$FORK" "$SRC"
fi

cd "$SRC"
git remote get-url robsimmons >/dev/null 2>&1 || git remote add robsimmons "$FORK"
git fetch robsimmons "$BRANCH"
# Preserve any existing binary as a fallback oracle.
[[ -f bin/twelf-server ]] && cp -f bin/twelf-server bin/twelf-server.stock
git checkout -B "$BRANCH" "robsimmons/$BRANCH"

make mlton

echo ""
echo "Built: $SRC/bin/twelf-server"
printf 'OS.exit\n' | "$SRC/bin/twelf-server" | head -1
