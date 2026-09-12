#!/usr/bin/env python3
"""Check **every** block of `rust/traces.expected` against **Lean**.

`rust/traces.sh` checks the verified binary against `rust/traces.expected`.
That alone makes the file a regression test: it says the Rust has not changed.
This script closes the other side, so the file is a *differential* test — the
recorded numbers are what Lean says they are, and the two checks meet on it.

The Lean side is `EmitTraces.lean`, which prints every block from Lean
definitions that are not transcriptions of the harness:

* the team blocks (`cfgS`, `spread`) run `IntConfig.run` of `Dpss/IntModel.lean`,
  and every row is additionally pinned by a `decide`-proved theorem there
  (`cfgSI_run_1` .. `_4`, `spreadI_run_1` .. `_3`);
* the safety blocks come from `Dpss/FenceTrace.lean`, where `Sim.trajOk` proves
  the trajectory obeys the whole vehicle contract for any well-formed vehicle and
  any margin, `Sim.low_nonneg` proves the sufficient-margin blocks clear of the
  fence by the fence theorem, and every row is a `decide`-proved theorem.

The team blocks were the last gap. They are the only thing that exercises
`advance`, `step`, `run` and `timeToNextEvent` end to end — the four definitions
`scripts/lean_to_verus.py` refuses to translate, so they are hand-written on the
Rust side and nothing else checks them against Lean. Until S7 they were compared
against the checked-in file only, never against Lean.

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
FIRST_BLOCK = "--- cfgS  (n=3, K=1) ---"


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
    """The whole recorded file, less the `contract:` lines.

    Nothing is sliced off the front any more. The file must start at the first
    block, so that a block silently prepended to it cannot escape comparison.
    """
    lines = EXPECTED.read_text(encoding="utf-8").splitlines()
    if not lines or lines[0] != FIRST_BLOCK:
        sys.exit(f"::error::{EXPECTED} does not start with {FIRST_BLOCK!r}")
    return [l for l in lines if not l.startswith("contract:")]


def main() -> None:
    lean, recorded = lean_side(), recorded_side()
    if lean == recorded:
        print(f"every recorded trace agrees with Lean ({len(lean)} lines, "
              f"{sum(1 for l in lean if l.startswith('---'))} blocks; "
              f"`contract:` lines are the Rust's own and are not compared)")
        return
    print("::error::the recorded traces disagree with Lean")
    for i, (a, b) in enumerate(zip(lean, recorded)):
        if a != b:
            print(f"  line {i}:\n    Lean:     {a}\n    recorded: {b}")
    if len(lean) != len(recorded):
        print(f"  Lean emitted {len(lean)} lines, the file has {len(recorded)}")
    sys.exit(1)


if __name__ == "__main__":
    main()
