#!/usr/bin/env bash
# Run the verified binary and check its output against the recorded traces.
#
# EVERY BLOCK IS NOW CHECKED AGAINST LEAN. What that means differs a little
# between them, and the differences are worth knowing.
#
# `cfgS` and `spread`: Lean proves those runs step by step (Dpss/IntModel.lean,
# cfgSI_run_1 .. cfgSI_run_4, by `decide`), Verus proves the executable step
# equals the generated specification, and the generator produces that
# specification from the same Lean file. That closes the last link -- that the
# specification is the algorithm.
#
# The safety blocks -- `fence`, `separation`, `stale link`, `link` and the
# contract violation -- are checked by `scripts/check_traces.py`, which runs
# `EmitTraces.lean` and compares its output to the recorded file. The Lean side
# is not a transcription of this harness: `Dpss/FenceTrace.lean` proves the
# trajectory obeys the whole vehicle contract for any well-formed vehicle and
# any margin (`Sim.trajOk`), proves the sufficient-margin blocks clear of the
# fence by the fence theorem itself (`Sim.low_nonneg`), and `decide`-proves every
# row. This script checks the binary against the same file, so the two meet.
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
