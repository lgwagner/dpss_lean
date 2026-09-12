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
# The `fence`, `separation`, `stale link` and `link` blocks are still only a
# REGRESSION test as far as the NUMBERS go: the columns were recorded from this
# binary, not derived from Lean. So they guard against the Rust changing
# behaviour; they do NOT check the Rust against the Lean. That is S6c and is
# scoped in PLAN.md.
#
# Their `contract:` lines are a different and stronger thing (S6b). `leg_ok`,
# `obs_ok`, `traj_ok`, `pair_leg_ok` and `link_ok` are SPECIFICATIONS -- they
# never execute, so no test can exercise them, and a wrong one would make every
# theorem about them true of the wrong system. Each `contract:` line is the
# result of running an executable function that Verus has proved returns exactly
# that specification's truth value (`traj_step_ok_ex` and friends), so a trace
# that says `holds at all N samples` has had the specification itself evaluated
# on it, sample by sample.
set -euo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLS="${VERUS_TOOLS_DIR:-$HOME/tools}"
export PATH="$HOME/.cargo/bin:$TOOLS/bin:$PATH"
BIN="$(mktemp -d)/dpss"
"$TOOLS/verus/verus" --compile "$REPO/rust/src/main.rs" -o "$BIN" >/dev/null
"$BIN" > "$BIN.out"
if diff -u "$REPO/rust/traces.expected" "$BIN.out"; then
  echo "traces match (cfgS/spread checked against Lean; safety blocks regression-only,"
  echo "              with the spec predicates themselves evaluated on each sample)"
else
  echo "::error::the verified binary no longer reproduces the recorded traces"
  exit 1
fi
