# DPSS Algorithm A, in Rust, verified with Verus

The executable half of `dpss_lean`. The Lean development proves Theorem 2.1 —
`n` patrol drones synchronize by time `2 − 1/n` — about a real-valued model; this
crate is a program that implements that model, with Verus proving that the
executable step computes exactly the specified step and preserves the standing
invariants.

> **Branch.** This lives on `rust-verus`. `main` carries the finished Lean work
> package and is deliberately untouched.

## Status

```
verification results:: 80 verified, 0 errors
traces agree with Lean
```

| | |
|---|---|
| **Verus proves** | `view_of(*final(e)) == spec_step(view_of(*old(e)))`; both standing conditions preserved, and along a whole run; no arithmetic overflow |
| **Lean proves** | `2 − 1/n`, sharp, for every resolution of the nondeterminism; and that the integer model refines the real one |
| **Trusted** | the generator, the Verus toolchain and Z3 |

## How it fits together

```
Dpss/*.lean               real-valued model; convergesBy
      │
      │  Dpss/IntModel.lean          embed_step, intRun_converges
      ▼
scripts/lean_to_verus.py  syntactic translator, fail-loud
      ▼
rust/src/spec/model.rs    GENERATED -- 24 spec fns, do not edit
rust/src/inv.rs           the standing conditions, hand-written
rust/src/exec.rs          the executable step and run
      ▼
rust/traces.sh            the verified binary, against Lean-proved traces
```

**Integers, and why nothing is lost.** Verus has no real numbers. Positions and
times here are integers scaled by `S = 2·K·n`: the segment boundaries land on the
even integers `2·K·i`, and because a gap only ever changes by `sep_rate · dt` with
`sep_rate ∈ {−2, 0, 2}`, **gap parity is invariant** — so `meet_time = gap/2` is
always exact. The integer runs are a sublattice of the real runs, not an
approximation. `Dpss/IntModel.lean` proves it.

**The clock is ghost.** Positions are bounded by the perimeter, so they fit in
`i64`. A run's clock is not bounded, so the ensemble does not store it: the step
computes `dt`, and absolute time is carried in ghost state as an unbounded `int`.

## Running it

```bash
./scripts/setup_verus.sh      # installs the pinned toolchain into ~/tools
./rust/verify.sh              # expect "80 verified, 0 errors"
./rust/traces.sh              # expect "traces agree with Lean"
python3 scripts/lean_to_verus.py --check   # the spec has not drifted
python3 scripts/no_proof_holes.py          # no assume/admit/external_body
```

Versions are pinned in `toolchain-versions.txt` and bumped deliberately: Verus
releases roll weekly, and **Z3 is not bundled** with the release — its required
version lives in Verus's `tools/common/consts.rs`, not in `INSTALL.md`.

## What is here

| | |
|---|---|
| `PLAN.md` | the build plan and its running status |
| `REFINEMENT.md` | what a verified per-drone **controller** would additionally require — scoped, not built |
| `src/spec/model.rs` | generated from `Dpss/IntModel.lean`; do not edit |
| `src/inv.rs` | the standing conditions, and the parts the generator refuses |
| `src/schedule.rs` | the scheduler's two guarantees |
| `src/geometry.rs` | the scaled geometry, which is nonlinear |
| `src/step_lemmas.rs`, `src/coherence.rs`, `src/reachable.rs` | invariant preservation |
| `src/exec.rs` | the executable ensemble, and the key equivalence |
