# Changelog

What changed, when, and what it cost. Newest first.

Each entry is the account you would want after a `git pull`: what landed, the
few things worth knowing that are not obvious from the diff, and — the part
that matters most in a project like this — **what was not finished, and why**.

The long forms live elsewhere: `STATUS.md` for what is proved, `PLAN.md` for
what is next, `INSIGHTS.md` for what the work taught, `GUIDE.md` for how to
follow the convergence proof.

---

## 2026-09-12 — S3: margined separation, both halves  *(branch `safety`)*

The safety track's third item, and the last one that turned out to be a change
of coordinates rather than new work.

### The model half — `Dpss/Standoff.lean`

S0 left the scheduler open and the standoff convergence bound as a prediction.
Both are closed. `toPoint` gains an inverse, so the standoff and point models
are two coordinate systems on one thing; the standoff step is *defined* as the
point step read in standoff coordinates, which makes the commuting square
trivial and puts the content in the theorems saying the pullback has the form an
engineer would have written:

  sStep_pos            drones still move at unit speed in standoff coordinates
  sTimeToNextEvent_eq  the duration is the min over drones of deadlines written
                       in standoff terms
  sInvariant_toPoint   the standing conditions correspond
  sConvergesBy         Theorem 2.1 under standoff

    every drone is inside its own respaced segment from
    (2 − 1/n)·(1 − (n−1)·d) onwards

*smaller* than `2 − 1/n`, because a team holding a standoff has less ground
between the walls to cover. The standoff is paid for in **coverage**, not in
time.

### The controller half — `Dpss/Separation.lean`, `rust/src/separation.rs`

At a wall a drone must never arrive; between drones the pair is *supposed* to
close, so the guarantee is `d ≤ gap` with equality permitted. Writing `g − d` for
the excess separation, every vehicle quantity doubles — both drones move, both
turn, both are sensed — and nothing else changes. So `PairTraj.le_low` is
`Fence.Traj.low_nonneg` read through `PairTraj.toFence`, with no second
induction, and `pair_margin_sharp` transfers backwards through `Traj.toPair`,
making the doubled margin sharp for free.

`91 verified, 0 errors`, and two more traces driven by the verified controller:
margin `30 = 2·(10+3+2)` clears a standoff of 5 at `low = 6`; margin `26`, short
by `2·eps`, breaches at `low = 2`.

### What this session did **not** finish

* **S1 is next and is the first genuinely hard item on this track.** S0, S2 and
  S3 were all changes of coordinates or instantiations of one another. S1 is
  not: it touches the *timing* arguments rather than the invariants. The
  standing correction remains — a lower bound `v_min > 0` is required, not
  optional.
* **`Dmax` is still a hypothesis** (S4), and there is still no comms model (S5).
* **Nothing on this branch is a Track B result.** `sConvergesBy` is Theorem 2.1
  transported, not a new convergence theorem; Algorithm B and the phase-1 bound
  are untouched, and the latter is an open research problem.

733 theorems, `sorry`-free; `91 verified, 0 errors`; traces agree with Lean.
`INSIGHTS.md` §22.

---

## 2026-09-12 — Track A: the fence, and the standoff verdict  *(branch `safety`)*

The mathematics was finished and neither half was a thing you could fly. This
session starts Track A: making the results apply to a vehicle, **safety first**.
Convergence under cooperation is Track B, and is recorded rather than scheduled.

`main` is untagged no longer: **`v1.0-lean-baseline`** marks the Lean
formalization with extensions, so the baseline can be found without reading past
the engineering.

### S2 — the margined fence, in both halves

One drone, one wall, a sampled controller. Three idealizations of the team model
removed at once — point mass at unit speed, instantaneous reversal, perfect
sensing — each replaced by a number an airframe analysis measures.

```lean
theorem Traj.low_nonneg (hM : V.Dmax + V.turn + V.eps ≤ M)
    (h0 : T.Safe 0) (k : ℕ) : 0 ≤ T.low k
```

`low k` is the lowest position of a whole leg, so this covers **every instant**
— proved by a discrete induction with no continuous-time machinery in it. Both
fences; the right one by an explicit reflection (`TrajR.mirror`), because B7 is
on record as the item whose "by symmetry" cost 737 lines.

`Fence.margin_sharp` proves the margin exactly tight: for *every* smaller `M`
there is a conforming trajectory that crosses. Unconditional — no restriction on
which of the three terms is deficient and no window of `M`, which took one
trajectory family rather than three counterexamples.

`rust/src/fence.rs` is the same theorem in Verus — `87 verified, 0 errors`, with
the trajectory as `spec_fn(nat)` so `safe_at` is the same induction, not a
horizon-limited version of it. Two new traces drive the **verified** controller
under a worst-case adversary and breach exactly when the margin is short.

### S0 — the standoff shear holds, exactly

`adj_ordered` is `0 ≤ gap`: the separation invariant with `d = 0`. Raising it to
`d ≤ gap` reads like a contradiction of the algorithm, since in DPSS a meet *is*
a loss of separation. S3 was sized "S if a shear works, else L", with a day set
aside to find out which.

`Dpss/Standoff.lean`: the shear `yᵢ = xᵢ − i·d` turns separation into ordering,
`toPoint_advance` says the dynamics commute, and the event predicates pull back
one for one. The catch is real and benign — the segments do not shear, they
respace, each narrowing by `1 − (n−1)d` with a buffer of exactly `d` that two
neighbours cover precisely when the standoff is two half-footprints.

**S3 is a change of constants.** The predicted bound is
`(2 − 1/n)·(1 − (n−1)d)` — *better* than the point bound.

### What this session did **not** finish

* **The scheduler-level correspondence.** S0 proved the correspondence for
  positions, motion and the event *predicates*. `timeToNextEvent`, `newDir` and
  `step` are left to S3 and are **not claimed**. Until they are done the
  standoff convergence bound above is a prediction, not a theorem.
* **S1, bounded speed in the team model.** Not started. A survey of the
  development produced one correction to the plan worth recording before anyone
  picks it up: a lower bound `v_min > 0` is **required, not optional** —
  `Dpss/EventuallyTurns.lean` is false without it, and with it go Lemma 3.5 and
  Theorem 2.1. Bounding speed only from above is not enough.
* **`Dmax` is still a hypothesis.** Deriving it from a vehicle model is S4.
  Keeping it a hypothesis is exactly what made S2 cheap, and the honest
  statement is that the guarantee is conditional on a number someone else
  measures — with the theorem saying precisely which number.

703 theorems, `sorry`-free; `87 verified, 0 errors`; traces agree with Lean.
`INSIGHTS.md` §20 and §21.

---

## 2026-09-12 — E1: DPSS in Rust, verified with Verus  *(branch `rust-verus`)*

An executable implementation of Algorithm A, with Verus proving it computes exactly
the specification the Lean development proves theorems about. `80 verified,
0 errors`; the verified binary reproduces two traces Lean has already proved.

`main` is untouched. The work is on `rust-verus`; `rust/PLAN.md` is the build plan
and its running status, `rust/README.md` explains the branch.

### The constraint that shaped it

**Verus has no real numbers** — `int`/`nat` in specs, fixed-width integers in
executable code, no rationals, no verified floats. So the specification had to be
restated over the integers.

**That restatement loses nothing.** Scale by `S = 2·K·n`: the segment boundaries
land on the even integers, and because a gap only ever changes by `sep_rate · dt`
with `sep_rate ∈ {−2, 0, 2}`, **gap parity is invariant** — so `meet_time = gap/2`
is always exact. The integer runs are a sublattice of the real runs, not an
approximation of them. `Dpss/IntModel.lean` proves it (`embed_step`,
`intRun_converges`), which is what lets the Rust inherit the `2 − 1/n` bound
without reproving it.

Doing that step in Lean is also what keeps the generator honest: the one
semantically interesting part of the port is proved, so
`scripts/lean_to_verus.py` only has to change notation.

### What is proved where

| | |
|---|---|
| **Verus** | the executable step equals the generated spec step; both standing conditions preserved, and along a whole run; no arithmetic overflow |
| **Lean** | `2 − 1/n`, sharp, for every resolution; and that the integer model refines the real one |
| **Trusted** | the generator, the Verus toolchain, Z3 |

`converges_by` is *written down* as a Verus `spec fn` so the property exists in the
crate's own language, but is neither proved nor `assume`d there — an `assume` would
be a silent trust hole and nothing depends on it.

### Three things that were not expected

**Z3 is better at the exhaustive branch analyses than Lean is.**
`apart_on_boundaries` preservation costs ~90 lines across three hand-written
lemmas in `Dpss/Reachable.lean`; in Verus it went through with no case split
written at all. An if-chain over decidable conditions is what an SMT solver is for.
The opposite held for the real-valued reasoning, where Mathlib was indispensable —
which is the argument for this split of labour rather than either tool alone.

**The invariant proofs are a sharper filter than the differential tests.** The plan
expected the traces to catch a mistranslation. Corrupting the generated
`escort_dir_left` to aim at the wrong boundary — and corrupting the executable code
to match, so the equivalence would still verify — was caught one layer earlier, by
escort coherence failing. I could not construct a corruption that passes every
proof and still changes a trace, which matches what `Dpss/Priority.lean` found
about the model: the tie-breaks that look like choices are unreachable.

**Z3 is not bundled with the Verus release**, and the version it requires is not in
`INSTALL.md` — it is `EXPECTED_Z3_VERSION` in `tools/common/consts.rs` at the
pinned commit. Verus also releases weekly, so all three versions are pinned in
`rust/toolchain-versions.txt` and bumped deliberately.

### What is not done

The per-drone controller — what you would actually fly. `rust/REFINEMENT.md`
scopes it: every event in the model is already local and every quantity a drone
needs is already local, but `time_to_next_event` is a minimum over all drones, and
the theorem that local reaction realizes the global event sequence does not exist
in any form. The Rust side of that would be the easy half.

---

## 2026-09-12 (later) — the work package, closed

The two items the Theorem 2.1 entry below left open are done. **Every item in
the work package is complete.** 594 theorems, all `sorry`-free.

### What landed

| | |
|---|---|
| **C3′** Sharpness at every `n` | `bound_sharp_general` — no `B < 2 − 1/n` is correct, for any `n ≥ 2` |
| **C1′** Nondeterminism as a relation | `convergesBy_of_isRun` — Theorem 2.1 for every trajectory of `StepRel` |

### Both were re-sized, and then shrank again

The entry below re-sized C1′ from `M` to `L` and kept C3′ at `M`, in each case
budgeting for the construction the paper describes. Both estimates were wrong,
and wrong the same way.

**C3′** was sized for the paper's `n`-drone cascade — `2(n−1)` phases, each a
configuration given by a formula in the phase index. None of it was needed. The
theorem does not ask where every drone is at every moment; it asks that one
drone be outside its interval at one late instant. On a ladder every gap stays
`d` while all drones head right, so a drone that turned left would have to be
co-located with its right-hand neighbour — impossible unless it has none. That
pins the first turn, and Lemma 3.1 does the rest. No configuration in the
cascade is ever written down.

**C1′** was sized for re-proving the development over an arbitrary trajectory,
reaching all 31 files. Re-reading the paper made that unnecessary: the passage
that flags the ambiguity ends *"Neither of these issues bears on the results
reported below, since our upper bound only concerns phase 2, where these issues
do not arise."* That is a claim about reachable states, and it is provable. The
two escort headings differ exactly when the meeting point lies strictly inside
the middle drone's interval — word for word the paper's own description of the
open case — and that configuration cannot arise. So the relation collapses to
the function, and every theorem in the development is already a theorem about
every resolution.

`ExamplesThree.triple` guards against the obvious failure mode: it exhibits a
configuration where the open clause genuinely admits two headings, so the
uniqueness theorem is not a theorem about our own definition.

### What is left

Nothing from the work package. `PLAN.md` now carries a backlog instead: **E1**,
a Rust implementation of Algorithm A verified against this specification in
Verus, with the discretization problem named up front.

---

## 2026-09-12 — Theorem 2.1

**The `2 − 1/n` bound is proved.** The work package is complete except for two
items that were re-sized rather than finished; see below.

Eight commits, `20c9295`…`be1079a`. 565 theorems, all `sorry`-free, CI-enforced.
A reader's guide to the result is `GUIDE.md`, also published at
<https://claude.ai/code/artifact/a1d8ba23-5932-4596-8f43-92bea56c3ad2>.

### What landed

| | |
|---|---|
| **B5** Lemma 3.7 | `leftSyncAt_next`, on a new real-time layer (`Dpss/RealTime.lean`) |
| **B6** Theorem 2.1 | `convergesBy` — every `n`, constant exactly `2 − 1/n`, plus the stronger real-time form `sync_at_of_time` |
| **C3** Sharpness | `bound_sharp` — no `B < 2 − 1/n` is correct (at `n = 2`, via an `ε`-family) |
| **C2** Three drones | a run that starts out of position, passes through a genuine three-way meeting, and settles |
| **C1** Nondeterminism | measured it instead of assuming it |
| **D1 / D2** Cleanup | two dead definitions removed; D2 closed as unnecessary |

### Three things worth knowing

**The plan's B5 hazard was real.** `LeftSync` is step-indexed; Lemma 3.7's
conclusion is a real-time deadline, and the step-indexed version of the lemma is
not merely inelegant — it looks *false*, because a drone heading right can sit
outside its interval mid-step and be back inside by the next event. The fix was
a thin real-time layer, ~340 lines, touching nothing else. The question `PLAN.md`
asked to record — *should the time-indexed predicate have been primary from the
start?* — has an answer, and it is **no**: it would have taxed 500 theorems to
pay for one proof.

**`convergesBy` carries one hypothesis beyond the standing invariant**:
`ApartOnBoundaries` on the *starting* configuration. That is not slack —
§3.20's counterexample shows the statement is false pointwise — and two one-line
lemmas discharge it. Three concrete configurations, including an `n = 3` one
that *exercises* the case rather than avoiding it, show the theorem is not
vacuous.

**C1 turned out seven-eighths wrong as previously described.** Three documents
had claimed that `newDir`'s priority order was "one resolution" of the paper's
nondeterminism. Checking every pair of simultaneously-due events: two
combinations are impossible, five agree, and the one that differs is the paper's
bounce — where the alternative provably walks a drone off its own endpoint. The
real gap is the *definition of a meet* (ours requires approach, the paper's is
positional).

### What was not finished, and why

- **C1′** — making `step` a relation so the theorem quantifies over all
  resolutions. `PLAN.md` had it at **M**; it is not. Roughly thirty primitive
  lemmas unfold `newDir` and would need re-deriving from a specification, and
  every statement in all 31 files gains a trajectory parameter. Re-sized to
  **L** and left open.
- **C3′** — sharpness for general `n` needs an `n`-drone cascade rather than a
  four-configuration trace. **M**, left open.

Both are recorded in `STATUS.md` §4 and `PLAN.md` at their true sizes.
`STATUS.md`, `PLAN.md`, `INSIGHTS.md` (four new entries) and `README.md` are
current, and `scripts/refresh_status.py`'s self-check passes.
