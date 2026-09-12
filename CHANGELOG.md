# Changelog

What changed, when, and what it cost. Newest first.

Each entry is the account you would want after a `git pull`: what landed, the
few things worth knowing that are not obvious from the diff, and — the part
that matters most in a project like this — **what was not finished, and why**.

The long forms live elsewhere: `STATUS.md` for what is proved, `PLAN.md` for
what is next, `INSIGHTS.md` for what the work taught, `GUIDE.md` for how to
follow the convergence proof.

---

## 2026-09-12 — session handoff: S6 complete, and nothing is scheduled  *(branch `safety`)*

Four entries below are one session's work: S6a, S6b, S6c and S6d, which is the
whole of S6. The item existed because `rust/traces.sh` said, correctly and in as
many words, that six of its eight blocks were a regression test and not a
differential one. It no longer says that.

The four steps are not four attempts at the same thing. Each shrank a different
part of what a reader has to check by hand:

| | |
|---|---|
| S6a | the two halves now quantify over **the same integers** — the fence is over an ordered ring and `ℤ` is an instance |
| S6b | the spec predicates **execute**, so a trace evaluates the specification rather than a transcription of it |
| S6c | the safety traces are **derived from Lean**, not recorded from the binary |
| S6d | the safety specifications are **generated from Lean**, not transcribed |

**State at handoff.** 841 theorems, `sorry`-free; `121 verified, 0 errors`; every
trace block checked against Lean; no proof holes; all three generated spec files
current. The full suite is `lake build`, `scripts/audit.py`,
`scripts/no_sorry.py`, `rust/verify.sh`, `rust/traces.sh`,
`scripts/no_proof_holes.py`, `scripts/lean_to_verus.py --check`, and
`scripts/check_traces.py` (which `rust/traces.sh` runs when `lake` is on the
path). `lake` needs `PATH=$HOME/.elan/bin:$PATH`.

**What is still a human read**, and no amount of further work on this track
removes all of it: that `traj_ok` assembles `obs_ok`, `fence_dir` and `leg_ok`
the way the Lean `trajOk` does; the two `link_ok` index clauses the generator
refuses (`INSIGHTS.md` §27); and the two proof structures, which stay separate
whatever the definitions do.

**Nothing is scheduled next, and that is deliberate.** Track A is complete and
so is S6. What remains in `PLAN.md` is four directions that differ in kind, so
the next session should ask rather than pick:

* **The `D` abstraction** — carry an overshoot allowance through Lemma 3.1,
  `TurnSpacing` and non-Zeno, buying non-Zeno at `(1/n − 2D)/V` under the sharp
  hypothesis `D < 1/(2n)`. Honest caveat: the events fire exactly in the current
  model, so this proves nothing new today. It is an interface for a future
  imperfect-turning model, and a statement of precisely what the non-Zeno
  argument needs.
* **Heterogeneous speeds** — a rewrite, not a margin, and deliberately deferred.
  `INSIGHTS.md` §23 is the diagnostic that says why.
* **The rest of S4** — instantiating the control-authority hypotheses against a
  *specific* airframe. An engineering exercise, and it needs an airframe.
* **Track B** — convergence under cooperation, whose central question is a
  genuinely open research problem.

Two documentation defects were fixed on the way, both predating this session:
`rust/README.md` still described the `rust-verus` branch and told a reader to
expect `80 verified`, and `PLAN.md`'s header still said 594 theorems.

---

## 2026-09-12 — S6d: the safety specifications, generated  *(branch `safety`)*

The step that removes the transcription. S6a put the two halves over the same
integers; S6b made the specifications executable, which catches a trace that
violates one but not a specification that is wrong; S6c derived the traces from
Lean. None of those reaches a `leg_ok` that faithfully says the wrong thing.

**Fourteen `spec fn`s are now generated** — `rust/src/spec/fence_model.rs` from
`Dpss/FenceInt.lean`, `separation_model.rs` from the new
`Dpss/SeparationInt.lean` — joining the 24 the team model already had. CI
regenerates all three and fails on drift. `Vehicle` moved to
`rust/src/vehicle.rs`, hand-written as `Dir` and `Snapshot` are: the generator
translates arithmetic, not types.

**A second shape, not a second copy.** The team model's definitions are
functions of the configuration, so the generator supplies `c: Snapshot`; the
safety ones take their arguments explicitly, so it reads the binders. Keeping
that as an attribute of the source left `model.rs` byte-identical. The grammar
gained the propositional connectives (`∧ ∨ ¬ →`, the last right-associative),
Lean's dot notation, and the anonymous constructor `⟨a, b, c⟩`.

**And one refusal, which is the part worth reading.** `link_ok`'s two index
clauses subtract sample numbers: ℕ subtraction in Lean, truncating at zero;
`int` subtraction in Verus, not. They agree under the `src k ≤ k` the predicate
itself states — which is exactly the kind of *it is fine here* argument a
translator must not be allowed to make. It refuses, those two clauses stay
hand-written with the Lean named beside them, and both the generated header and
`rust/src/comms.rs` say so. `INSIGHTS.md` §27.

**Checked live.** Reversing `hold_leg` in the Lean fence and regenerating turns
`121 verified, 0 errors` into `117 verified, 4 errors`; dropping the doubling
from the Lean `pairLegOk` costs one more. A generator that had quietly stopped
being used would show neither.

841 theorems, `sorry`-free; `121 verified, 0 errors`; 38 generated `spec fn`s.

### S6 is complete, and what is left is a read

* That `traj_ok` assembles `obs_ok`, `fence_dir` and `leg_ok` the way the Lean
  `trajOk` does — a quantifier, so not generated, the same exclusion the team
  model makes for its standing conditions.
* The two refused `link_ok` clauses.
* The proof structures, which stay separate whatever the definitions do.

---

## 2026-09-12 — S6c: the safety traces, from Lean; S6 done  *(branch `safety`)*

`rust/traces.sh` has said since they were written that six of its eight blocks
were a regression test and not a differential one. It no longer has to.

**The six safety blocks are one trajectory.** That is the finding, and it was not
in the plan's sizing, which said "define the worst-case simulator" — singular by
accident rather than by insight. A drone against a wall, a pair closing, a pair
across a stale link: the same adversary, flying at the fence with the sensor
reading high by the whole sensing allowance. What differs is the **vehicle**. The
separation blocks are the fence blocks in the excess-separation coordinate under
the doubled vehicle; the stale-link blocks are those again with `age · dmax`
folded into its sensing term. Which is exactly what `Dpss/Separation.lean` and
`Dpss/Comms.lean` proved — the two transfers turning up in the traces.

So `Dpss/FenceTrace.lean` is short. `Sim.trajOk` proves the adversary obeys the
whole vehicle contract for any well-formed vehicle and any margin — not a fact
about the recorded numbers, so changing them cannot make it vacuous — and
`Sim.low_nonneg` proves the three sufficient-margin blocks clear of the fence by
the fence theorem rather than by evaluation. Only the rows are `decide`.

**Two scripts meet on one file.** `EmitTraces.lean` prints the blocks from those
definitions; `scripts/check_traces.py` compares its output with
`rust/traces.expected`; `rust/traces.sh` compares the same file with the verified
binary. The Lean check runs from `traces.sh` when `lake` is on the path, and is a
step of its own in Lean CI — the Verus job pins Verus, Rust and Z3 and has no
Lean toolchain, which is deliberate and stays that way.

**The `contract:` lines are excluded, and should be.** They are the Rust's own
executable specifications (S6b) evaluated on the trace, which is a fact about the
Rust. The script drops them and says so.

**The negative control is on both sides now.** The reversal that loses ground is
rejected by the executable specification at `k=4`, and `bad_not_trajOk` proves no
`trajOk` holds of it.

826 theorems, `sorry`-free; `121 verified, 0 errors`; every trace block checked
against Lean.

### S6 is done, and S6d is not

* **S6d — extending the generator to the safety specs — was optional and is not
  done.** It is the only step that would remove part of the human read, and the
  read it would remove is the one S6a already made short.
* **What none of this establishes** is that the Verus `leg_ok` and the Lean
  `LegOk` are the same predicate. Same integers, same shape, same names, same
  order, same evaluated traces — and still a human read.

---

## 2026-09-12 — S6b: the specifications, executed  *(branch `safety`)*

The step the plan calls the one that matters most, and the reason is that a
`spec fn` never runs. Every theorem about a wrong specification stays true — of
a system nobody wanted — and no trace test can reach that, because a trace
exercises the controller and the controller is five lines. `INSIGHTS.md` §1 is
this project's own instance: 145 passing theorems did not notice a definition
that falsified the headline result.

**Eleven `_ex` functions**, across `rust/src/fence.rs`, `separation.rs` and
`comms.rs`. Each is ordinary executable Rust with an `ensures` clause saying it
returns exactly the corresponding specification's truth value, and Verus proves
it. Running one is running the specification.

**The quantified predicates needed a theorem rather than a horizon.** Nothing
executable computes `traj_ok`, which quantifies over every sample. So
`traj_ok_iff_steps` proves `traj_ok` is exactly `traj_step_ok` at every sample,
and `traj_step_ok_ex` computes that — which makes "checked on a prefix" precise
instead of apologetic. `pair_traj_ok_iff_steps` and `link_ok_iff_steps` do the
same. `comms_ok_implies_steps` runs one way only, and deliberately: a trace
records the gap and its estimate, and those do not determine the two positions
behind them, so nothing recovers `link_ok` from a trace.

**Every trace block now carries a `contract:` line.** Two new blocks come with
it: a *realizable* stale link — the worst-case gap traces apply the steady-state
staleness from `k = 0`, which is a bound and not a history, so `link_ok`'s own
clauses had nothing to be evaluated on — and the **negative control**, because a
check that cannot fail is not a check. That last block is a drone whose reversal
loses ground, which `leg_ok`'s `hold_leg` clause forbids, and the same
executable specification rejects it: `FAILS first at k=4`.

`121 verified, 0 errors`; `traces.sh` passes; no proof holes.

### What is **not** done

* **The six safety blocks are still regression-only.** Their columns are
  recorded from the binary, not derived from Lean. `rust/traces.sh` says so, and
  raising them is S6c.
* **That the Verus `leg_ok` and the Lean `LegOk` are the same predicate is still
  a human read.** S6a made it a short one; only S6d would remove part of it.
* **The trace harness is `#[verifier::external]`**, so the `requires` clauses of
  the `_ex` functions are not checked when it calls them. They hold by
  inspection of the constants, and nothing verified depends on the harness.

---

## 2026-09-12 — S6a: the fence was never about the reals  *(branch `safety`)*

`rust/traces.sh` says in as many words that six of its eight blocks are a
regression test and not a differential one. S6 is the item that fixes that, and
S6a is its first step — not a test at all, but the deletion of a gap that a
reader of the two halves had to close by hand.

**The fence argument is ordered-ring arithmetic.** `Traj`, `safe_all` and
`low_nonneg` use addition, subtraction and comparison: no division, no
completeness, no limits. So `Dpss/Fence.lean`, `Dpss/Separation.lean` and
`Dpss/Comms.lean` are now stated over an arbitrary ordered ring, with `ℝ` one
instance among others. `Dpss/Continuous.lean` still lands in `ℝ`, as it must —
it is where the mean value theorem is used.

**At `ℤ` the two developments are about the same integers.** `Dpss/FenceInt.lean`
is the instantiation, written to be read beside `rust/src/fence.rs`: the Verus
`struct Vehicle`, `wf`, `fence_dir`, `safe`, `leg_ok`, `obs_ok` and `traj_ok`
transliterated, and the five `proof fn`s stated argument for argument. Every
proof in it applies the general theorem; none repeats an argument.

**`Dpss/Fence.lean` was restructured to have the Rust's shape.** The per-leg
content — `LegOk`, `ObsOk`, `turn_le_next`, `low_nonneg_leg`, `safe_step` — is
now a layer of its own, and the trajectory theorems iterate it. That is how
`rust/src/fence.rs` was already organized; the two files now correspond node by
node rather than structure-against-predicate. `Traj.turn_le_pos_succ`,
`safe_succ`, `safe_all`, `low_nonneg` and `pos_nonneg` keep their names and
statements, and three of them are now one line.

**A side effect worth having:** `fenceDir`, `Traj`, `PairTraj` and `Sharp.traj`
are no longer `noncomputable`. Real division was what forced that
(`INSIGHTS.md` §11), and there is none in the fence. `FenceInt.trace_breach`
cashes it immediately: the integer trajectory that breaches a short margin, with
both the vehicle contract and the breach discharged by `decide`, at exactly the
numbers `rust/traces.expected` records.

### What is **not** done

* **S6b — exec mirrors of the spec predicates** — is the step that matters most
  and is untouched. `traj_ok`, `leg_ok`, `obs_ok`, `pair_leg_ok` and `link_ok`
  never execute, so no trace test can catch a wrong one.
* **S6c** — the six safety blocks of `rust/traces.expected` are still recorded
  from the binary. `traces.sh` still says so, correctly.
* **`margin_sharp` stays over `ℝ`.** It halves the deficiency to build its
  witness, so it needs a field. The construction is general, which is what
  `trace_breach` uses; a general integer sharpness statement is not claimed.

795 theorems, `sorry`-free; `lake build` clean. The Rust is untouched by this
step, so `100 verified, 0 errors` and the traces stand as they were.

---

## 2026-09-12 — S5: safety when the network degrades; Track A complete  *(branch `safety`)*

Three answers, different in character. `Dpss/Comms.lean`, `rust/src/comms.rs`.

**1. The fence needs no network at all.** Structural rather than a theorem, and
worth saying loudly: nothing in `Fence.Traj` mentions another drone. A total
communications failure does not weaken the fence by an epsilon.

**2. Staleness is sensing error.** A report `a` samples old localizes the
neighbour to `eps + a·Dmax`; with own sensing that is `2·eps + a·Dmax`, so

```
M ≥ 2·(Dmax + turn + eps) + A·Dmax
```

One sample of staleness costs exactly one `Dmax`, and nothing else changes.
**Delay and loss are one hypothesis** — a message lost is a message not yet
arrived. `Vehicle.pair` of S3 is the case `A = 0`, so this generalizes S3
rather than sitting beside it.

**3. After convergence, separation is free.** `sConvergesBy` puts every drone in
its own respaced segment; `standoff_tiles` puts consecutive segments exactly `d`
apart; `separated_of_segments` — one `linarith` — says confinement *is*
separation.

So **the communication requirement is transient**: the inflated margin buys
coordination during phase 1, and afterwards geometry maintains the invariant.
That settles what the degraded-mode fallback should be — *hold to your own
segment* — with no new mechanism, because it is the steady state. All three
properties the plan asked of a fallback are proved: inside the fence
(`standoffLeftEnd_nonneg`, `standoffRightEnd_le_one`), separated
(`gap_ge_of_hold`), and starving nobody (`hold_covers` — the segments and
footprints tile `[0,1]` exactly).

`100 verified, 0 errors`. Two new traces: margin `50 = 2·(10+3+2) + 2·10` clears
a standoff of 5 at `low = 6`; on the *fresh* margin of 30, a two-sample delay is
enough for the gap to go **negative** — the pair flies through itself.

### Track A is complete

| | |
|---|---|
| S0 | the standoff shear is exact |
| S1 | bounded speed is a change of clock |
| S2 | the margined fence, proved sharp |
| S3 | margined separation, at the model and the controller |
| S4 | `Dmax = V·Δt`, derived |
| S5 | staleness priced, and the fallback proved |

### What is **not** done

* **Heterogeneous speeds.** A rewrite, not a margin: uniform speed is what makes
  an escort stay together without a grouped representation, so dropping it takes
  out `EscortsCoherent`, `Dpss/Coherence.lean` and Lemmas 3.2–3.4.
* **The turn allowance, and that reversals complete within a period.** Facts
  about control authority that no speed bound determines. They stay as
  hypotheses, where an engineer can see what the vehicle is being asked to do.
* **`A` is a hypothesis**, like `Dmax`. What is proved is the exchange rate.
* **Track B — convergence under cooperation — is untouched**, and its central
  question (an `n`-independent phase-1 bound) is an open research problem.

774 theorems, `sorry`-free; `100 verified, 0 errors`; traces agree with Lean.
`INSIGHTS.md` §24.

---

## 2026-09-12 — S1 and S4: the last two uniform idealizations  *(branch `safety`)*

### S1 — bounded speed is a change of clock

`Dpss/Kinematics.lean`. The plan sized this as the expensive item, because unit
speed is cashed in by `pos_sub_eq_of_dirConst` — *distance travelled equals
elapsed time* — which non-Zeno, Lemma 3.5, Lemma 3.7 and the sharpness family
all consume. It is not expensive, for one reason:

> if every drone has the same speed at the same instant, **speed is a clock**.

With common speed `v(t)` and `τ(t) = ∫₀ᵗ v`, the bounded-speed system at real
time `t` *is* the unit-speed system at unit time `τ(t)`. `Clock` axiomatizes the
reparameterization by the speed bounds it must satisfy rather than by an
integral, so no integration theory is imported and the interface is what a
vehicle report contains.

`converges_by_real_time`: synchronized by real time `(2 − 1/n) / vmin`.

The accounting is worth stating: **convergence uses the lower bound and only the
lower bound** — going faster never hurts, so `V` never appears — and **non-Zeno
uses neither**, since `τ(T)` is a real number however fast the drones went.

`vmin_zero_stalls` turns this track's standing correction into a theorem: with
`vmin = 0` the constant clock `τ ≡ 0` satisfies the whole contract and every
drone stays exactly where it started, for ever. Bounding speed from above alone
makes the theorem *false*, not merely weaker.

### S4 (core) — `Dmax` is no longer a hypothesis

`Dpss/Continuous.lean`. `Vehicle.ofSpeed` sets `Dmax = V · Δt`;
`lipschitz_of_deriv` converts a derivative bound into the Lipschitz bound the
argument uses — Mathlib's mean value theorem, and the only appeal to analysis on
this track; `flight_nonneg` concludes `0 ≤ x t` at **every real instant**, with
no sampling in the statement.

`Flight.low` is `sInf` of a leg's image. It needs the infimum to *exist*, never
to be attained, so no compactness or extreme-value argument appears and the
whole thing still goes through Fence.lean's discrete induction.

### What this session did **not** finish

* **The turn allowance and the completion of reversals remain hypotheses, and
  should.** A speed bound cannot supply them: a fast drone with strong actuators
  has a small turn allowance and a slow one with weak actuators a large one.
  They are facts about control authority, and they sit in `Flight`'s hypotheses
  where an engineer can see them.
* **S1 covers uniform speeds only.** Heterogeneous speeds are a rewrite, not a
  margin — uniform speed is what makes an escort stay together without a grouped
  representation, so dropping it takes out `EscortsCoherent`,
  `Dpss/Coherence.lean` and Lemmas 3.2–3.4.
* **S5 is not started.** No comms model, no delay, no message loss, no
  degraded-cooperation fallback.

754 theorems, `sorry`-free; `91 verified, 0 errors`. `INSIGHTS.md` §23 records
the diagnostic that would have re-sized four of this track's items before any of
them were started: ask whether an idealization is *uniform across the system*,
not how many files mention it.

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
