# DPSS Algorithm A, in Rust, verified with Verus

The executable half of `dpss_lean`. The Lean development proves Theorem 2.1 —
`n` patrol drones synchronize by time `2 − 1/n` — about a real-valued model; this
crate is a program that implements that model, with Verus proving that the
executable step computes exactly the specified step and preserves the standing
invariants.

> **Branch.** E1 — the team model, everything above `src/fence.rs` in the table
> below — was built on `rust-verus`, where it verifies at `100 verified, 0
> errors`. You are on `safety`, which adds the drone-level modules
> `src/fence.rs`, `src/separation.rs` and `src/comms.rs`. `main` carries the
> finished Lean work package and is deliberately untouched.

## Status

```
verification results:: 121 verified, 0 errors
traces match (cfgS/spread checked against Lean; safety blocks regression-only,
              with the spec predicates themselves evaluated on each sample)
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
rust/src/spec/*_model.rs  GENERATED from Dpss/FenceInt.lean and
                          Dpss/SeparationInt.lean -- 14 more
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
./rust/verify.sh              # expect "121 verified, 0 errors"
./rust/traces.sh              # expect "traces match ..."
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
| `src/spec/fence_model.rs` | generated from `Dpss/FenceInt.lean`; the safety predicates |
| `src/spec/separation_model.rs` | generated from `Dpss/SeparationInt.lean`; the pair and the link |
| `src/vehicle.rs` | the airframe numbers; a type, so hand-written like `Dir` |
| `src/inv.rs` | the standing conditions, and the parts the generator refuses |
| `src/schedule.rs` | the scheduler's two guarantees |
| `src/geometry.rs` | the scaled geometry, which is nonlinear |
| `src/step_lemmas.rs`, `src/coherence.rs`, `src/reachable.rs` | invariant preservation |
| `src/exec.rs` | the executable ensemble, and the key equivalence |
| `src/fence.rs` | S2 — the margined fence, and the `_ex` mirrors of its specifications |
| `src/separation.rs` | S3 — margined separation, as the fence on the excess gap |
| `src/comms.rs` | S5 — staleness priced as sensing error, and the link predicates |

**The safety specifications are generated (S6d).** `leg_ok`, `obs_ok`, `safe`,
`fence_dir`, `pair_leg_ok` and the rest come out of Lean through
`scripts/lean_to_verus.py`, so nobody types them twice. Two clauses of `link_ok`
are **refused** and hand-written instead: they subtract sample indices, which is
ℕ subtraction in Lean and `int` subtraction here, and a translator that mapped
one to the other would be unsound in general. The generated headers say so.

**The `_ex` functions are S6b.** A `spec fn` never executes, so no test can
exercise one, and a wrong specification supporting a flawless proof is the
failure mode this project has actually had. Each `_ex` function carries an
`ensures` clause saying it returns exactly the corresponding specification's
truth value, so the `contract:` lines in `traces.expected` are the
specifications themselves evaluated on the trace. The last block of the trace
output is the negative control: a drone whose reversal loses ground, which the
same check rejects at the sample where it happens.
