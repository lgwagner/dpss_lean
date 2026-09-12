#!/usr/bin/env bash
# Run the verified binary and check its output against the recorded traces.
#
# THE TWO KINDS OF BLOCK IN traces.expected ARE NOT EQUALLY STRONG.
#
# `cfgS` and `spread` are a genuine DIFFERENTIAL test. Lean proves those runs
# step by step (Dpss/IntModel.lean, cfgSI_run_1 .. cfgSI_run_4, by `decide`),
# Verus proves the executable step equals the generated specification, and the
# generator produces that specification from the same Lean file. That closes the
# last link -- that the specification is the algorithm -- and it is the check
# that would catch the one kind of bug this project has actually had: a wrong
# definition supporting a flawless proof.
#
# The `fence`, `separation` and `stale link` blocks are only a REGRESSION test.
# They were recorded from this binary, not derived from Lean, because the Lean
# safety objects (Fence.Traj and friends) are structures over real-valued
# functions and are not executable. So they guard against the Rust changing
# behaviour; they do NOT check the Rust against the Lean. Raising them to the
# first standard is scoped in PLAN.md.
set -euo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLS="${VERUS_TOOLS_DIR:-$HOME/tools}"
export PATH="$HOME/.cargo/bin:$TOOLS/bin:$PATH"
BIN="$(mktemp -d)/dpss"
"$TOOLS/verus/verus" --compile "$REPO/rust/src/main.rs" -o "$BIN" >/dev/null
"$BIN" > "$BIN.out"
if diff -u "$REPO/rust/traces.expected" "$BIN.out"; then
  echo "traces match (cfgS/spread checked against Lean; safety blocks regression-only)"
else
  echo "::error::the verified binary no longer reproduces the recorded traces"
  exit 1
fi
