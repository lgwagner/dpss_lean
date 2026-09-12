#!/usr/bin/env bash
# Run the verified binary and check its output against the recorded traces.
#
# EVERY BLOCK IS CHECKED AGAINST LEAN, BY THE SAME MECHANISM. `EmitTraces.lean`
# prints all ten blocks from Lean definitions and `scripts/check_traces.py`
# diffs them against the recorded file; this script diffs the verified binary
# against that same file, so the binary and Lean meet on it.
#
# Until S7 the two team blocks -- `cfgS` and `spread` -- were the exception.
# They rested on a proof chain (Verus proves the executable step equals the
# generated specification, and the generator produces that specification from
# Lean) plus a hand-maintained match between the recorded rows and
# `cfgSI_run_1` .. `_4`. The chain is strong where it reaches, but it does not
# reach `advance`, `step`, `run` or `timeToNextEvent`: the generator refuses all
# four, so they are hand-written on the Rust side, and these two blocks are the
# only thing that exercises them. Nothing in CI would have noticed the recorded
# rows drifting from Lean. Now `IntConfig.run` prints them and they are diffed
# like everything else -- and the `decide`-proved theorems remain, so those rows
# are attested twice over.
#
# The safety blocks -- `fence`, `separation`, `stale link`, `link` and the
# contract violation -- were already checked this way. The Lean side is not a
# transcription of this harness: `Dpss/FenceTrace.lean` proves the trajectory
# obeys the whole vehicle contract for any well-formed vehicle and any margin
# (`Sim.trajOk`), proves the sufficient-margin blocks clear of the fence by the
# fence theorem itself (`Sim.low_nonneg`), and `decide`-proves every row.
#
# The `contract:` lines are the one thing Lean does not attest, because they are
# a fact about the Rust: each is an executable function that Verus proved returns
# exactly the truth value of a SPECIFICATION -- `leg_ok`, `obs_ok`, `traj_ok`,
# `pair_leg_ok`, `link_ok` -- evaluated on the trace. Specifications never
# execute, so nothing else can exercise them, and a wrong one would make every
# theorem about them true of the wrong system. The last block is the negative
# control: a reversal that loses ground, which that check rejects and which
# `FenceTrace.bad_not_trajOk` also refutes.
set -euo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLS="${VERUS_TOOLS_DIR:-$HOME/tools}"
export PATH="$HOME/.cargo/bin:$TOOLS/bin:$HOME/.elan/bin:$PATH"
BIN="$(mktemp -d)/dpss"
"$TOOLS/verus/verus" --compile "$REPO/rust/src/main.rs" -o "$BIN" >/dev/null
"$BIN" > "$BIN.out"
if ! diff -u "$REPO/rust/traces.expected" "$BIN.out"; then
  echo "::error::the verified binary no longer reproduces the recorded traces"
  exit 1
fi
echo "the binary reproduces the recorded traces"

# The other side of the differential test needs a Lean toolchain, which the
# Verus CI job deliberately does not have -- it pins Verus, Rust and Z3 and
# nothing else. So run it when `lake` is here (which is every local run), and
# leave it to the Lean job otherwise, where it is a step of its own.
if command -v lake >/dev/null 2>&1; then
  python3 "$REPO/scripts/check_traces.py"
  echo "traces agree with Lean"
else
  echo "note: no lake on PATH, so the Lean side was not checked here."
  echo "      scripts/check_traces.py does it, and Lean CI runs it."
fi
