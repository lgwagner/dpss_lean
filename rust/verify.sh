#!/usr/bin/env bash
# Verify the Rust half. Expects the pinned toolchain from scripts/setup_verus.sh.
set -euo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLS="${VERUS_TOOLS_DIR:-$HOME/tools}"
export PATH="$HOME/.cargo/bin:$TOOLS/bin:$PATH"
exec "$TOOLS/verus/verus" --crate-type=lib "$REPO/rust/src/lib.rs" "$@"
