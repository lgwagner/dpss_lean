#!/usr/bin/env python3
"""Check the safety blocks of `rust/traces.expected` against **Lean**.

`rust/traces.sh` checks the verified binary against `rust/traces.expected`.
That makes the file a regression test: it says the Rust has not changed. This
script closes the other side, so that the six safety blocks are a *differential*
test in the sense the `cfgS` and `spread` blocks already were — the recorded
numbers are what Lean says they are.

The Lean side is `EmitTraces.lean`, which prints the blocks from the definitions
of `Dpss/FenceTrace.lean`. Those are not a transcription of the harness:
`Sim.trajOk` proves the trajectory obeys the whole vehicle contract for any
well-formed vehicle and any margin, `Sim.low_nonneg` proves the sufficient-margin
blocks clear of the fence by the fence theorem, and every row is a
`decide`-proved theorem.

What is deliberately **not** compared: the `contract:` lines. Those report the
Rust's own executable specifications (S6b) evaluated on the trace, so they are a
fact about the Rust and Lean has nothing to say about them. They are dropped
before the comparison.

Usage: python3 scripts/check_traces.py
"""
import os
import pathlib
import subprocess
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent
EXPECTED = REPO / "rust" / "traces.expected"
EMITTER = REPO / "EmitTraces.lean"
FIRST_SAFETY_BLOCK = "--- fence (dmax=10, turn=3, eps=2, margin=15) ---"


def lean_side() -> list[str]:
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    r = subprocess.run(["lake", "env", "lean", "--run", str(EMITTER)],
                       cwd=REPO, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        print(r.stdout + r.stderr, file=sys.stderr)
        sys.exit("::error::the Lean emitter did not run")
    return r.stdout.splitlines()


def recorded_side() -> list[str]:
    lines = EXPECTED.read_text(encoding="utf-8").splitlines()
    if FIRST_SAFETY_BLOCK not in lines:
        sys.exit(f"::error::{EXPECTED} has no safety blocks")
    lines = lines[lines.index(FIRST_SAFETY_BLOCK):]
    return [l for l in lines if not l.startswith("contract:")]


def main() -> None:
    lean, recorded = lean_side(), recorded_side()
    if lean == recorded:
        print(f"safety traces agree with Lean ({len(lean)} lines, "
              f"{sum(1 for l in lean if l.startswith('---'))} blocks; "
              f"`contract:` lines are the Rust's own and are not compared)")
        return
    print("::error::the recorded safety traces disagree with Lean")
    for i, (a, b) in enumerate(zip(lean, recorded)):
        if a != b:
            print(f"  line {i}:\n    Lean:     {a}\n    recorded: {b}")
    if len(lean) != len(recorded):
        print(f"  Lean emitted {len(lean)} lines, the file has {len(recorded)}")
    sys.exit(1)


if __name__ == "__main__":
    main()
