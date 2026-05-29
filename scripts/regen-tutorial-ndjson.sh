#!/usr/bin/env bash
# scripts/regen-tutorial-ndjson.sh
#
# Regenerate tests/tutorial/{good,bad}/*.ndjson from the Lean source
# in lean/tutorial/.  The .stats.json files are not touched.
#
# Requires: elan + lake (install from https://github.com/leanprover/elan).
# The lean-toolchain file in lean/tutorial/ pins the exact Lean version.
#
# Usage:
#   ./scripts/regen-tutorial-ndjson.sh

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_DIR="$REPO_ROOT/lean/tutorial"
OUT_DIR="$REPO_ROOT/tests/tutorial"

# Remove stale NDJSON and info files (but leave .stats.json alone).
rm -f "$OUT_DIR"/good/*.ndjson "$OUT_DIR"/good/*.info.json
rm -f "$OUT_DIR"/bad/*.ndjson  "$OUT_DIR"/bad/*.info.json

# Force re-elaboration of Tutorial.lean: lake skips modules whose .olean
# is fresh, so we delete just that one cache entry rather than all deps.
# The build path moved under `lib/lean/` in newer Lake, so clear the matching
# artifacts wherever they live rather than assuming the legacy flat path.
find "$LEAN_DIR/.lake/build" \
     \( -name 'Tutorial.olean' -o -name 'Tutorial.trace' -o -name 'Tutorial.ilean' \) \
     -delete 2>/dev/null || true

cd "$LEAN_DIR"
OUT="$OUT_DIR" lake build Tutorial
