#!/usr/bin/env bash
# Differential test: run the *verified* stepper and check its output against
# traces Lean has already proved.
#
# Verus proves the executable step equals the generated specification, and the
# generator produces that specification from Dpss/IntModel.lean. This closes the
# last link: that the specification is the algorithm. It is the check that would
# catch the one kind of bug this project has actually had -- a wrong definition
# supporting a flawless proof.
set -euo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLS="${VERUS_TOOLS_DIR:-$HOME/tools}"
export PATH="$HOME/.cargo/bin:$TOOLS/bin:$PATH"
BIN="$(mktemp -d)/dpss"
"$TOOLS/verus/verus" --compile "$REPO/rust/src/main.rs" -o "$BIN" >/dev/null
"$BIN" > "$BIN.out"
if diff -u "$REPO/rust/traces.expected" "$BIN.out"; then
  echo "traces agree with Lean"
else
  echo "::error::the verified stepper no longer reproduces the Lean traces"
  exit 1
fi
