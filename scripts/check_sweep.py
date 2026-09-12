#!/usr/bin/env python3
"""Check `rust/sweep.expected` against **Lean**.

The companion of `scripts/check_traces.py`, for the generated half. Where
`rust/traces.expected` is ten hand-chosen configurations, this is every valid
configuration of five small teams: for each `(n, K)`, every position vector in
`[0, 2Kn]^n` and every heading vector, filtered to those satisfying the standing
conditions and `ApartOnBoundaries`, run for a fixed number of steps.

`rust/traces.sh` checks the same file against the verified binary, so the two
meet on it — the same two-job arrangement the traces already use, and the reason
neither CI job needs both toolchains.

## What the sweep adds over the traces

`advance`, `step`, `run` and `timeToNextEvent` are hand-written on the Rust side
because `scripts/lean_to_verus.py` refuses to translate them, so the traces are
load-bearing exactly there — and they were two configurations. A transcription
error surviving this has to be invisible on *every* valid configuration of every
team up to four drones.

The enumeration is duplicated on the two sides rather than handed over from one,
so each decides membership with its own implementation of the standing
conditions. A disagreement about which configurations are valid changes the
line count, and shows up before any trajectory is compared.

Each line carries the final state and a rolling digest of every intermediate
one, so a divergence repaired by the last step still shows.

Usage: python3 scripts/check_sweep.py
"""
import os
import pathlib
import subprocess
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent
EXPECTED = REPO / "rust" / "sweep.expected"


def lean_side() -> list[str]:
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    r = subprocess.run(["lake", "exe", "emit_sweep"],
                       cwd=REPO, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        print(r.stdout[-4000:] + r.stderr[-4000:], file=sys.stderr)
        sys.exit("::error::the Lean sweep did not run")
    return r.stdout.splitlines()


def main() -> None:
    lean = lean_side()
    recorded = EXPECTED.read_text(encoding="utf-8").splitlines()
    if lean == recorded:
        blocks = [l for l in lean if l.startswith("---")]
        print(f"the sweep agrees with Lean ({len(lean) - len(blocks)} configurations, "
              f"{len(blocks)} groups)")
        return
    print("::error::the recorded sweep disagrees with Lean")
    shown = 0
    for i, (a, b) in enumerate(zip(lean, recorded)):
        if a != b:
            print(f"  line {i}:\n    Lean:     {a}\n    recorded: {b}")
            shown += 1
            if shown == 10:
                print("  (further differences not shown)")
                break
    if len(lean) != len(recorded):
        print(f"  Lean emitted {len(lean)} lines, the file has {len(recorded)}")
        print("  a length difference means the two sides disagree about which "
              "configurations are valid, not about a trajectory")
    sys.exit(1)


if __name__ == "__main__":
    main()
