# PLAN — the roadmap

The forward-looking document. `STATUS.md` records what **is** proved;
`INSIGHTS.md` records what was **learned**; `GUIDE.md` walks the finished work
package; this file records what to do **next** and in what order.

**The work package is complete.** What follows is a backlog of new directions,
plus the record of what each finished item built and taught.

> The original scoping document — the decisions taken at the start, and the one
> planning error they contained — is `PLAN-original.md`.

**How to use this.** Work the critical path top to bottom. Each item states the
target, the ingredients that already exist, the approach, and a **done-when**
that is checkable. Do not start an item whose dependencies are open.

**When an item is finished**, move it to *Completed* at the bottom and record
two things: **what was built**, and the **insight** — whatever would not be
obvious to someone reading only the resulting Lean. Insights that generalise
beyond this project also go in `INSIGHTS.md`; the note here is what a person
picking up *this* roadmap needs.

---

## Where things stand

**826 theorems, all `sorry`-free** (594 of them the work package; the rest are
Track A). Non-Zeno is proved. **Theorem 2.1 is
proved** — `convergesBy`, for every `n`, with the bound exactly `2 − 1/n` —
**shown attained for every `n`**, and **proved for every resolution** of the
paper's nondeterminism.

| Done | Open |
|---|---|
| A, B1–B7, C1, C1′, C2, C3, C3′, D1, D2 | — |

**The work package is complete.** What follows is a backlog of new directions,
not unfinished business.

---

## Critical path

**Track A — a drone-level controller** (branch `safety`). The mathematics is
finished; what is on the critical path now is making it apply to a vehicle.
Safety first; convergence under cooperation is Track B and is *recorded, not
scheduled*.

| # | Item | Size | State |
|---|---|---|---|
| S0 | Does the standoff shear hold? | S | ✅ done — yes, exactly |
| S2 | The margined fence | M | ✅ done — proved, sharp, executable |
| S3 | Margined separation | S | ✅ done — both halves, in Lean and Verus |
| S1 | Kinematics: bounded motion into the team model | M | ✅ done — uniform speeds |
| S4 | The continuous layer | XL | ◐ core done — `Dmax = V·Δt` derived |
| S5 | Decentralized safety under a comms model | L | ✅ done — both halves |
| S6 | Raise the safety traces to a real differential test | M | ✅ S6a–S6c done; S6d optional, not done |

**Track A is complete.** A drone-level controller with fencing and separation
guarantees exists, in Lean and in Verus, against a vehicle described by
measurable numbers and a network described by a bound on message age.

### S6 — raise the safety traces to a real differential test  ⟨M⟩  ✅ done

**The known weakness in what Track A ships.** `rust/traces.sh` runs two kinds of
block. `cfgS` and `spread` are a genuine differential test: Lean proves those
runs by `decide`, the generator produces the spec Verus proves the executable
step equals, and the binary must reproduce them. The six `fence` / `separation` /
`stale link` blocks are **only a regression test** — they were recorded from the
binary, because `Fence.Traj` and friends are structures over `ℕ → ℝ` and do not
execute. They guard against the Rust changing; they do not check it against Lean.

Four steps, in the order they pay:

* **S6a — generalize the fence over an ordered ring, instantiate at `ℤ`.** ⟨S⟩
  ✅ **done.** `Dpss/Fence.lean`, `Dpss/Separation.lean` and `Dpss/Comms.lean`
  are now stated over an arbitrary ordered ring; `margin_sharp` stays over `ℝ`
  as expected, since it halves the deficiency to build its witness.
  `Dpss/FenceInt.lean` is the `ℤ` instantiation, written in the Rust's own
  packaging — unbundled `Vehicle` with a separate `wf` — so that it can be read
  beside `rust/src/fence.rs` a definition at a time.

  Two things came out of it that were not in the sizing. First,
  `Dpss/Fence.lean` now has the Rust's **shape**: the per-leg content is a layer
  of its own (`LegOk`, `ObsOk`, `turn_le_next`, `low_nonneg_leg`, `safe_step`)
  and the trajectory theorems iterate it, which is how `rust/src/fence.rs` was
  already organized — so the correspondence is node for node instead of
  structure-against-predicate, and three of the old proofs collapsed to one
  line. Second, the fence definitions are **computable** now that no real
  division is involved, which is what S6c needs; `FenceInt.trace_breach` is
  already a `decide`-proved integer breach at the numbers
  `rust/traces.expected` records.
* **S6b — exec mirrors of the spec predicates.** ⟨S⟩ ✅ **done.** Eleven `_ex`
  functions across `rust/src/fence.rs`, `separation.rs` and `comms.rs`, each
  with `ensures result == <the spec predicate>`, and every trace block now
  carries a `contract:` line that is the specification evaluated on it sample by
  sample. `121 verified, 0 errors`.

  The quantified predicates needed one thing the sizing did not mention: no
  executable function computes `traj_ok`, which quantifies over every sample. So
  `traj_ok_iff_steps` proves `traj_ok` is exactly `traj_step_ok` at every sample
  and the `_ex` function computes *that*, which makes "checked on a prefix" a
  precise statement rather than an apology. `pair_traj_ok_iff_steps` and
  `link_ok_iff_steps` do the same; `comms_ok_implies_steps` runs one way only,
  because a trace records the gap and its estimate and those do not determine the
  two positions behind them.

  And a negative control, because a check that cannot fail is not a check: the
  last trace block is a drone whose reversal loses ground, which `leg_ok`'s
  `hold_leg` clause forbids, and the same executable specification rejects it —
  `FAILS first at k=4`.
* **S6c — `decide`-proved integer traces in Lean.** ⟨M⟩ ✅ **done.**
  `Dpss/FenceTrace.lean` defines the adversary, `EmitTraces.lean` prints the
  blocks, and `scripts/check_traces.py` compares them with the recorded file —
  run by `rust/traces.sh` locally and by Lean CI, since the Verus job has no
  Lean toolchain.

  The sizing said "the worst-case simulator". There is only **one**: the six
  safety blocks are the same trajectory, and what differs between them is the
  *vehicle*, not the adversary. The separation blocks are the fence blocks in
  the excess-separation coordinate with the doubled vehicle, and the stale-link
  blocks are those again with `age · dmax` folded into its sensing term — which
  is what `Dpss/Separation.lean` and `Dpss/Comms.lean` proved in the first
  place, showing up in the traces. Six blocks, six lines of definition, one
  theorem (`Sim.trajOk`, for any well-formed vehicle and any margin), and the
  sufficient-margin blocks are clear of the fence by `Sim.low_nonneg` rather
  than by evaluation.
* **S6d — extend the generator to the safety specs.** ⟨M, higher risk⟩ ✅
  **done, with one deliberate refusal.** Fourteen `spec fn`s across
  `rust/src/spec/fence_model.rs` and `separation_model.rs` are now generated
  from `Dpss/FenceInt.lean` and `Dpss/SeparationInt.lean`, so the predicates a
  wrong transcription would hide in are not transcribed at all.

  The grammar extensions the sizing predicted were needed, and one it did not.
  The predicted ones: propositional connectives (`∧ ∨ ¬ →`, the last
  right-associative), explicit binders, Lean's dot notation, and the anonymous
  constructor `⟨a, b, c⟩`. The one it did not: **a second shape**. The team
  model's definitions are functions of the configuration; the safety ones take
  their arguments explicitly. That is a parameter-passing convention, not a
  grammar, and keeping it as a source attribute left `model.rs` byte-identical.

  **The refusal is the interesting part.** `link_ok`'s two index clauses
  subtract sample numbers, which is ℕ subtraction in Lean and `int` subtraction
  in Verus — truncating in one, not in the other. They agree under the
  `src k ≤ k` the predicate itself states, so a translator *could* be talked
  into it; this one refuses, and the two clauses stay hand-written with the Lean
  beside them. `INSIGHTS.md` §27.

  Checked live rather than assumed: reversing `hold_leg` in the Lean fence turns
  `121 verified` into `117 verified, 4 errors`, and forgetting the doubling in
  the Lean pair costs one more.

**Done when** `traces.sh` can truthfully say all blocks are checked against
Lean. ✅ It now does, and `scripts/check_traces.py` is the other half of that
sentence: `traces.sh` checks the binary against the recorded file, the script
checks the recorded file against Lean.

The one thing Lean does not attest is the `contract:` lines, and it should not:
they are the Rust's own executable specifications evaluated on the trace, which
is a fact about the Rust. The script drops them before comparing and says so.

**What this still does not establish.** The four steps do not prove the Lean
theorem and the Verus theorem are the same theorem, and nothing here was ever
going to. What they did was shrink what a reader has to check by hand, in four
different ways: same integers (S6a), the specifications evaluated rather than
inspected (S6b), the traces derived from Lean rather than recorded (S6c), and
the specifications themselves generated rather than transcribed (S6d). What is
left is the `traj_ok`-shaped quantifiers, the two `link_ok` index clauses, and
the proof structures, which stay separate regardless.

---

What remains beyond that is not on this track, and none of it is a change of
coordinates — `INSIGHTS.md` §23 is the diagnostic that says so:

* **Heterogeneous speeds.** A rewrite, and the reason is structural: uniform
  speed is what makes an escort stay together without a grouped representation.
  It would take out `EscortsCoherent`, `Dpss/Coherence.lean` and Lemmas 3.2–3.4.
  The ACL2 mechanization carries the grouped representation; adopting it here is
  the honest route if this is ever wanted.
* **The rest of S4.** The turn allowance and the completion of reversals cannot
  be derived from a speed bound — they are facts about control authority. What
  remains is to instantiate them from a *specific* vehicle model, which is an
  engineering exercise against a chosen airframe rather than a proof obligation.

**S1 carries a correction to its own sizing.** A survey of the development found
that bounding speed from *above* is not enough: a lower bound `v_min > 0` is
**required**, because `Dpss/EventuallyTurns.lean` is false without it — a drone
crawling arbitrarily slowly never turns, so no pair meets, so Lemma 3.5 and
Theorem 2.1 both fail. The survey also found the cheapest two insertion points,
which are worth doing before anything structural:

* **Overshoot `D` into Lemma 3.1 only.** `pos_le_leftEnd_of_turnsRight` and
  `rightEnd_le_pos_of_turnsLeft` weaken to `≤ leftEnd + D` / `≥ rightEnd − D`;
  every consumer already reads them as inequalities. Buys non-Zeno at
  `(1/n − 2D)/V` under the new and sharp hypothesis `D < 1/(2n)`.
* **Footprint `r`, routed through `gap` rather than `pos`.** Because `2r` is a
  constant, `gap_advance` is unchanged, and with it `sepRate`, `meetTime`, all
  of `Meeting.lean`'s gap algebra and the escort layer. Eight definitions
  change; no proof restructuring. (This is the same shear S0 proved, in the
  coordinates the existing files already use.)

What would be a **rewrite**, and is therefore deferred: per-drone heterogeneous
speeds. Uniform speed is what makes an escort stay together without a grouped
representation (`Dpss/Events.lean` says so in as many words), so dropping it
takes out `EscortsCoherent`, `Coherence.lean`, and Lemmas 3.2–3.4. Keep speed
uniform across drones and bounded, and the work roughly halves.

---

## Completed on this branch

**S5 — safety when the network degrades.** `Dpss/Comms.lean`,
`rust/src/comms.rs`. Staleness is sensing error, at one `Dmax` of margin per
sample of age; delay and loss are one hypothesis. And after convergence,
separation is maintained by geometry with no messages at all — which makes the
communication requirement transient and settles what the fallback should be.
`hold_covers` completes it: the fallback starves nobody.

*Insight:* the fallback was already in the development. The open design question
was answered by composing two theorems proved for other reasons, and the proof
is one `linarith`. `INSIGHTS.md` §24.

**S4 (core) — `Dmax` derived.** `Dpss/Continuous.lean`. `Vehicle.ofSpeed` gives
`Dmax = V·Δt`; `lipschitz_of_deriv` converts a derivative bound into it via
Mathlib's mean value theorem; `flight_nonneg` holds at every real instant with
no sampling in the statement.

*Insight:* `Flight.low` as `sInf` of a leg's image needs the infimum to *exist*,
never to be attained — so a statement quantified over all real instants goes
through a discrete induction with no compactness anywhere.

**S1 — bounded speed is a change of clock.** `Dpss/Kinematics.lean`. If every
drone has the same speed at the same instant, speed is a clock: the
bounded-speed system at real time `t` is the unit-speed system at unit time
`τ(t)`. Convergence by real time `(2 − 1/n)/vmin`, and `vmin_zero_stalls` proves
that a lower bound is required rather than convenient.

*Insight:* convergence uses only the **lower** speed bound and non-Zeno uses
neither; the upper bound earns its keep at the controller, as the fence's
`Dmax`. Worth checking which bound a result actually needs before assuming it
needs both.

**S3 — margined separation, both halves.** The model half in
`Dpss/Standoff.lean`: `toPoint` gains an inverse, the standoff step is the point
step read in standoff coordinates, and `sTimeToNextEvent_eq` shows the duration
is the minimum of deadlines an engineer would have written. `sConvergesBy` is
Theorem 2.1 under standoff, at `(2 − 1/n)·(1 − (n−1)d)` — *better* than the
point bound. The controller half in `Dpss/Separation.lean` and
`rust/src/separation.rs`: the pair guarantee is the fence guarantee on the
excess separation with the vehicle doubled.

*Insight:* build the transfer as a **map between the two structures, in both
directions**, rather than proving the target theorem again under new hypotheses.
The forward map gives the guarantee with no second induction; the backward map
gives sharpness for free. `INSIGHTS.md` §22.

**S2 — the margined fence.** `Dpss/Fence.lean` and `rust/src/fence.rs`. One
drone, one wall, a sampled controller; three idealizations removed at once.
`Traj.low_nonneg` is a statement about every instant proved by discrete
induction; `margin_sharp` proves the margin `Dmax + turn + eps` exactly tight,
unconditionally. Both fences, the right one by explicit reflection.
`87 verified, 0 errors`; the verified controller breaches at runtime exactly
when the margin is short.

*Insight:* parameterize by **displacement per sample**, not speed. It is what a
flight test measures, it keeps Verus in integers with no scaling argument
needed, and it removes the continuous-time layer from the Lean proof — three
unrelated wins from one choice of units. `INSIGHTS.md` §20.

**S0 — the standoff shear.** `Dpss/Standoff.lean`. `yᵢ = xᵢ − i·d` turns
separation into ordering; `toPoint_advance` says the dynamics commute; the event
predicates pull back one for one. The segments respace rather than shear, and
`coverage_exact` says the respacing loses nothing when the standoff is two
half-footprints.

*Insight:* when an item is sized "S if X, else L", build X first — not a
prototype of either branch. A day converted an open question about the shape of
a quarter's work into a change of constants. `INSIGHTS.md` §21.

---

---

## Backlog

New work, none of it blocking anything.

### E1 — a Rust implementation, verified against this spec with Verus  ⟨L⟩

> **Approved and under way on the `rust-verus` branch.** The full build plan,
> its milestones and their current state are `rust/PLAN.md`. What follows is the
> scoping that fed into it.

**Target.** An executable implementation of Algorithm A in Rust, proved in
[Verus](https://github.com/verus-lang/verus) to meet the specification this
development pins down — so that the artefact is not only a proof *about* the
algorithm but a proof-carrying *implementation of* it.

**What the Lean side already supplies.** The specification, unambiguously:
`Config`, the three events, `newDir`'s resolution (and `Dpss/Nondeterminism.lean`'s
proof that every legitimate resolution agrees with it), `timeToNextEvent`, the
standing `Invariant` and `ApartOnBoundaries`, and the target property
`ConvergesBy`. Those are the obligations to restate in Verus.

**The hard part, named up front.** Lean's model is over `ℝ`; Verus reasons
about executable Rust, where the natural choices are rationals, fixed point, or
floats. `STATUS.md`'s "known modelling risks" already flags that the ACL2
development is rational-valued and that its termination intuitions do not
transfer for free. A faithful port must either
* carry rationals explicitly (and accept that the implementation is not what
  anyone would fly), or
* prove the discretization sound against the real-valued spec — which is the
  interesting version, and the larger one.

**Suggested shape.**
1. Port the *state* and the *event schedule* to Verus, with `spec fn`s mirroring
   `Config`, `borderTime`, `meetTime`, `separationTime`, `droneNextTime`.
2. Prove the executable `step` preserves the invariant — the analogue of
   `invariant_step`, which is where most of the value is: it is a real safety
   property of real code (drones stay on the perimeter, never overtake).
3. State `ConvergesBy` and either import the bound as an assumption discharged
   by this Lean development, or re-prove it in Verus.

**Done when.** A Verus crate that builds with `verus --verify`, whose
`step`/`run` carry the invariant, with a README mapping each Verus obligation to
the Lean theorem it mirrors.

**Worth recording in advance.** Step 2 is worth doing even if step 3 is not —
a verified-safe implementation with an unverified convergence bound is still a
much stronger artefact than an unverified one, and it is the part that a
practitioner would actually use.

---

## Completed



What was built, and what it taught. In the order it happened.

---

### Stage 0–1 — the model and its invariants

**Built.** `Config`, the three events, motion between them, the event
schedule, `step` and `run`, and the standing `Invariant` (on the perimeter, in
order, escorts coherent) proved preserved along any run.

**Insights.**

- **The escort is emergent, not primitive.** The literature describes a
  meeting pair as beginning "joint motion of indefinite duration", which reads
  like it needs a first-class co-moving group. It does not: because all drones
  share one speed, a co-located pair pointing the same way *stays* co-located
  automatically. That deleted a whole planned layer.
- **Make the update a function of the whole state.** Several events come due
  at the same instant routinely, not exceptionally. Composing individual
  updates would force an ordering that then needs justifying; defining each
  drone's post-event heading as a function of the entire configuration
  (`newDir`) makes simultaneity automatic. The price is a visible priority
  order rather than one smeared across update code.
- **Invariants enforced by construction beat invariants inherited.**
  `escortsCoherent_step` was written with three hypotheses and Lean reported
  all three unused — the property is guaranteed by the *scheduler*, which
  always offers an escorting pair its separation deadline, so a step can never
  overshoot it. This pattern repeated six times; every time, deleting the
  hypothesis gave a stronger theorem.

---

### Validation — traces, and two things they overturned

**Built.** Complete symbolic traces at `n = 2` (steady state, and a converging
one) and `n = 3`, each proved for *every* step index by induction; periodicity
checked against the paper's `2/n`; the convergence time checked against the
`2 − 1/n` bound.

**Insights.**

- **A concrete case beat 145 theorems.** `AtSeparation` originally required
  the pair to be *escorting* — co-located **and heading the same way**. Two
  drones converging on their shared boundary have *opposite* headings right up
  to the instant they meet, so no separation fired, the meet branch took over,
  and the right-hand drone was driven **out of its own interval**. The bug
  silently falsified the target theorem and was invisible to everything proved
  so far, because nothing forced the definitions to be exercised.
  > A formalization's danger is not a wrong proof — Lean stops those. It is a
  > wrong **definition** supporting a flawless proof of something else.
- **Numerical agreement is cheap evidence and worth buying.** Two independent
  checks against numbers the paper states (the period `2/n`, the bound
  `2 − 1/n`) both agree. A model that had drifted would be unlikely to
  reproduce either.

---

### A — Non-Zeno  ✅

**Built.** `nonZeno : ∀ T : ℝ, ∃ k, T < (c.run hn k).time`. Every step turns at
least one drone (unconditional, cascades included); consecutive turns of one
drone are `1/n` apart; so `n+1` steps buy `1/n` of clock.

**Insights.**

- **When a source hand-waves, find your own route before reconstructing
  theirs.** The paper's argument rests on a claim it calls "not hard to show"
  and does not show, and which I could not reconstruct. The counting route is
  self-contained, avoids the disputed claim, and reuses a lemma the
  convergence proof needed anyway.
- **This is the property the ACL2 mechanization assumes.** Its event-stepper
  is admitted as a *partial* function and `step-time-always-terminates` rides
  into its top-level theorem unproved. The two published artefacts were
  complementary; this closes the gap between them.
- **Gap 2 was a phantom.** I spent a commit proving domination lemmas to
  contain a worry about "spurious" border deadlines. Flying a drone for exactly
  `borderTime` lands it on `0` or `1` — that is what the quantity *is* — so the
  event genuinely fires. The lemmas were not needed.
- **Non-Zeno turned out to be load-bearing, not a terminus.** "Every drone
  eventually turns" — which Lemma 3.5 needs — is *only* provable once the clock
  cannot stall. Without it a drone could sit still forever, never turning and
  never leaving `[0,1]`.

---

### B2 — Lemmas 3.3 and 3.4  ✅

**Built.** Both, each conditional on the single `BothLeftApart` obstruction
that Lemma 3.2 also waits on — not on an assumed `BalanceNonneg`.

**Insight.** Both reduce to one question: does the starting configuration give
a nonnegative **balance**? Both do, for free. For 3.3, an escorting pair's
balance is exactly *twice its separation deadline*, and escort coherence says
that deadline is never in the past — so the balance is nonnegative **because
the scheduler makes it so**. For 3.4, ordering carries the neighbour past the
boundary too, so both terms are nonnegative separately.

A first attempt was vacuous: I split each lemma into "starting balance" plus
"delegate to 3.2", and Lean reported the delegating halves' hypotheses unused —
correctly, since those wrappers proved nothing.

---

### B4 — Lemma 3.6  ✅

**Built.** Turn persistence, **unconditionally** — no dependence on
`BothLeftApart`.

**Insight.** It came almost free from work done for another purpose. Its
load-bearing step — *a drone that reverses to leftward is co-located with its
right-hand neighbour* — had been proved to close one branch of Lemma 3.2's
obstruction. Whatever can reverse a rightward drone (a meet, a separation, or
the right border) leaves it on top of its neighbour.

---

### B7 — the symmetric half  ✅

**Built.** A reflection map (`pos ↦ 1 − pos`, headings flipped, indices
reversed) proved to commute with `advance`, `step` and `run`, and the transfer
principle `rightSync_iff_leftSync_mirror`.

**Insights.**

- **"By symmetry" is free on paper and not in Lean.** Four words in the source;
  here a reflection map, reflection laws for every local quantity and every
  event, invariance of the global deadline, and three commutation theorems.
  **It was not on my work list until I went looking**, which is the real lesson:
  a step the source treats as a triviality about the *mathematics* may be
  substantial work about the *formalization*.
- **The priority orders do not correspond.** `newDir` checks the left border
  first; its reflection checks the right border first. Harmless only because
  paired branches are mutually exclusive — which had to be proved.
- **The tie-break flips.** `escortDir` and `escortDirLeft` reflect into each
  other *except exactly on the shared boundary*, where one reads
  `pos < boundary` and the other `boundary < pos`. The mathematics is
  symmetric; a strict inequality is not.

---

### B3 — Lemma 3.5  ✅

**Built.** `exists_coLocated_within_one` — every adjacent pair becomes
co-located within one unit of time — plus `exists_coLocated_of_approaching`,
`gap_sub_eq_of_dirsConst`, and `exists_firstRight`/`exists_firstLeft`.

**Insights.**

- **The paper's distance computation survived intact.** The bound
  `(z − w) + (x − y)/2 ≤ 1` formalizes exactly as written. What it needed was
  the *exact* elapsed time to each drone's first turn, not a bound on it — the
  result comes out at exactly 1, so a chain of inequalities would not close.
- **Which drone turns first does not matter.** The two orderings give the same
  total, so the proof needs no case split on that — only on which index is
  larger, to name the phases. That halved the work.
- **Lemma 3.2's by-product carried it.** *A drone heading right can only
  reverse by becoming co-located with its right-hand neighbour* — proved months
  of commits earlier for a different purpose — is what makes an approaching
  pair's gap close at a steady rate: neither drone can turn while they are
  apart. That single lemma has now paid for itself four times.
- **`HaveMetBy` did **not** need to become locally checkable.** The
  history-shaped definition was adequate here. B5 did not need it either — it
  consumes the meeting index by searching back for the last one, in two lines —
  so D2 was closed as unnecessary rather than done.
- **Gap and balance are the difference and the sum.** The gap moves at the
  difference of the two velocities, the balance at their sum. That is why a
  pair heading apart has a growing gap and a constant balance — B1's key
  observation, seen from the other side.

### B1 — Lemma 3.2  ✅

**Built.** `PairPhase`, the three-clause invariant, proved preserved by a step
and along a run; `balanceNonneg_of_pairPhase`; and **`leftSync_of_separation`**
— Lemma 3.2 with no hypothesis beyond left synchronization of the left drone.
`leftSync_of_escorting` is Lemma 3.3, likewise unconditional.

**Insights.**

- **Deriving beat guessing.** Three shapes were tried and two were wrong before
  the derivation was written down; the derived one worked essentially first
  time. The cost of the guessing was several days of commits.
- **Clause 2 is the one that matters.** *Heading apart ⟹ balance zero.* It is
  not decoration: the pinning argument needs the balance **exactly** zero, not
  merely nonnegative, so clause 1 alone is not an invariant.
- **A pair that is apart cannot change phase.** The whole difficulty collapses
  once you notice this: every event that could deliver `left` to one drone and
  `right` to the other requires *this pair* to be co-located, and either border
  event forces co-location by ordering. So an apart pair carries its balance
  across untouched, and only the co-located case needs work.
- **Lemma 3.4 does not get the invariant from its own hypothesis.** Reaching
  the shared boundary gives a *nonnegative* balance, not a zero one, so a pair
  heading apart from there may carry a strictly positive balance and clause 2
  fails. 3.4 therefore takes the invariant as a hypothesis rather than being
  unconditional — an asymmetry with 3.2 and 3.3 I did not anticipate.

### B1 — earlier, partial

**Built.** The pair **balance** and its laws; `BothLeftApart` isolated as the
sole obstruction, with two of its three routes closed; the positional core
(`pinned_of_balance_zero`); the pinned-clock lemma; `ApartOnBoundary` and its
preservation.

**Insights so far.**

- **The paper's timing argument is really positional.** *"Drone j+1 must have
  taken at least as long to turn around as drone j"* becomes arithmetic on
  interval endpoints once the balance is in hand.
- **A lemma that read as obvious was false.** *"A co-located pair heading apart
  sits on the boundary it shares"* — refuted by four drones stacked at one
  point, the two middle ones each escorting the *outward* neighbour.
  > When a case analysis stubbornly refuses to close, suspect the goal.
  > Building the counterexample took less time than the failed proof, and
  > unlike the attempt it produced something permanent.
- **In an event-driven model, "time advances each step" is false.** A step
  takes zero time when an event is already due. That breaks the tidy "bound
  the step by the remaining budget" story — and then turns into a *tool*, since
  a step of no time cannot move the balance either.
- **Three invariant shapes, two wrong.** Guessing cost more than deriving
  would have. The derivation is `STATUS.md` §8a.

---

### B5 — Lemma 3.7, and the real-time layer  ✅

**Built.** `Dpss/RealTime.lean` — `posIn`, `InStep`, `LeftSyncAt`,
`RightSyncAt`, and the bridges to the step-indexed notions — then
`Dpss/InductionStep.lean` — `leftSyncAt_next`, plus `ApartOnBoundaries` and its
propagation along a run.

**Insights.**

- **The hazard this item was flagged with was real, and the recommended fix was
  the right one.** `LeftSync` is indexed by step; the lemma's conclusion is a
  deadline in real time. Adding a time-indexed predicate alongside the existing
  one, and relating the two *before* attempting the lemma, is exactly what
  worked.
- **Should the time-indexed predicate have been primary from the start? No.**
  The recorded question has an answer, and it is the opposite of what the hazard
  note expected. `ConvergesBy` — the target — is index-shaped, every earlier
  lemma is index-shaped, and the real-time layer is needed *only* in Lemma 3.7,
  where a drone's state is read strictly inside a step. Making it primary would
  have taxed 500 theorems to pay for one. The right shape is what happened:
  index-shaped throughout, with a thin real-time layer introduced where the
  argument demands it and discharged back into indices immediately.
- **The index-shaped reading is genuinely weaker, and weaker in the one place
  it matters.** A drone heading right can sit left of its endpoint mid-step and
  be back inside its interval by the next event. So a step-indexed Lemma 3.7 is
  not merely inelegant — it looks false.
- **One lemma carried the whole real-time layer.** A linear function
  nonnegative at both ends of an interval is nonnegative throughout it.
  Position, gap and balance are all affine in time within a step, so every
  "true at the events, therefore true in between" argument is that lemma with
  different names substituted. Three lines, used six times.
- **"No time, no motion" is the trade between index order and time order.**
  Steps of zero length are routine here, so `time_m ≤ time_k` does not give
  `m ≤ k`. But it does give equal positions, and in every place the proof
  wanted the index inequality what it actually needed was the position.
- **The paper's two leftward cases are one case.** It splits on whether the
  pair is together *now*; taking the last co-located index at or before the
  deadline covers both, with an empty range when they are together. That halved
  the case analysis.

---

### B6 — Theorem 2.1  ✅

**Built.** `Dpss/Convergence.lean` — `convergesBy`, `sync_at_of_time`,
`allSync_of_time`, the real-time mirror transfer, and three concrete
configurations that discharge every hypothesis.

**Insights.**

- **The final induction is the paper's, unchanged.** Drone `0` free, every pair
  met by 1, `+1/n` per drone. What took the work was not the induction but
  making each of its three inputs exist.
- **The bound is exact, to the last `1/n`.** `1 + (n−1)/n = 2 − 1/n` with
  nothing to spare — as it had to be, since C3 then showed the bound attained.
  Any analysis that had leaked an `ε` anywhere would have been visible here as a
  worse constant.
- **`ApartOnBoundaries` is the one thing the paper never has to say.** A
  co-located pair heading apart is on the boundary it shares — obvious about
  the algorithm's reachable states, false about configurations in general
  (§3.20), and therefore a hypothesis on the start. Finding that it *also*
  needed reflecting for the right-hand half was a small surprise; "by symmetry"
  keeps charging rent.
- **Stating the goal as a `Prop`-valued definition from day one paid off.** The
  repository was never `sorry`-ful, the target was always precisely visible,
  and discharging it was a one-line theorem at the end rather than a
  renegotiation of what had been aimed at.

---

### C1 — measuring the nondeterminism  ✅ *(C1′ remains)*

**Built.** `Dpss/Priority.lean` — the eight-way comparison, `newDirMeetFirst`,
and `newDirMeetFirst_leaves_interval`.

**Insights.**

- **Measure a gap before believing your own description of it.** `Step.lean`
  had described the priority order as "one resolution" of the paper's
  nondeterminism for months. Seven of its eight competing cases turn out to be
  forced, and the eighth is not a free choice either. The honest description was
  cheaper to compute than to guess — one afternoon against a standing caveat in
  three documents.
- **The agreements have one reason.** A separating drone is standing on a
  boundary, and from a boundary the escort heading is forced. That is why the
  table is mostly "agree" rather than coincidence.
- **The real gap was somewhere else.** Not the priority order but the
  *definition of a meet*: ours requires the pair to be approaching, the paper's
  is positional. Naming the gap correctly is most of what C1 delivered, and it
  also reveals that C1′ is L rather than M.

---

### C2 — three drones that settle  ✅

**Built.** `Dpss/ThreeConverge.lean` — `cfgS` and its four-step trace into the
existing steady state, `cfgS_three_way_meeting`, `cfgS_not_sync_at_start`, and
`run_cfgB_at` generalizing the cycle to an arbitrary start time.

**Insights.**

- **The obvious start configuration is not synchronized.** Each drone on its
  own left endpoint, all heading right — and drone `0` is out of its interval
  within an instant and reaches `2/3` before anything turns it. A good reminder
  that `Sync` is a "from now on" property, not a property of a moment.
- **The three-way meeting cost nothing extra.** It arrived on its own in the
  first converging trace attempted. Configurations that exercise the hard
  machinery are not rare; the two-drone traces simply cannot express them.
- **Generalizing a trace over its start time is free if the step lemmas already
  are.** `step_cfgB` and `step_cfgC` were stated for an arbitrary clock from
  the beginning, so `run_cfgB_at` was the same induction with `t` carried
  through. Worth doing to every concrete trace on the way in.

---

### C3 — the bound is attained  ✅ *(C3′ remains for general `n`)*

**Built.** `Dpss/Sharpness.lean` — the `spreadE ε` family, its four-step trace,
and `bound_sharp`.

**Insights.**

- **A family is not much harder than an instance, if the instance was done
  right.** The `ε`-trace is the `spread` trace with `1/4` replaced by a
  variable. What it cost was replacing `norm_num` with `linarith` and naming
  the two hypotheses `0 < ε` and `ε < 1/3` that the arithmetic needs.
- **The witness is a *right*-synchronization failure.** The natural guess is
  that the late-converging drone is the one still to the left of its interval.
  It is not: drone `0` overshoots to the **right** and does not come back until
  `3/2 − ε`. Sharpness of a bound stated as "left and right synchronized" can
  be witnessed by either half, and the other half was the one to look at.
- **Sharpness is what makes the proof worth checking.** Had `2 − 1/n` been
  loose, an analysis losing an `ε` would still have been "correct". It is not
  loose, so the exactness of the induction in B6 is load-bearing rather than
  aesthetic.

---

### D1, D2 — cleanup, one by deletion and one by not doing it  ✅

**Built.** `Config.Together` and `Config.Valid` removed. `HaveMetBy` left
alone.

**Insights.**

- **A dead predicate is not neutral.** `Together` and `CoLocated` said almost
  the same thing and only one was used; leaving both invites a reader to prove
  something about the wrong one. Same for `Valid` against `Invariant`.
- **D2 was a contingency that never fired, and that is worth recording.** The
  ACL2 team found a history-shaped `have-met` "difficult to work with in a
  mechanized proof" and recasting it locally was what made their development
  tractable. Here it caused no trouble at all: Lemma 3.5 produces the meeting
  index and Lemma 3.7 consumes it by searching back for the last one. The
  likely difference is ACL2's untyped first-order setting rather than the shape
  of the predicate — so an experience report from one prover is evidence about
  that prover, not a law.

---

### C3′ — sharpness for every `n`  ✅

**Built.** `Dpss/SharpnessGeneral.lean` — the `ladder` family, `ladder_state`,
`ladder_outside`, and `bound_sharp_general`.

**Insights.**

- **The plan's route was not the cheap one.** The item was sized for the
  paper's `n`-drone cascade: `2(n−1)` phases, each a configuration given by a
  formula in the phase index, each needing a minimum over `Fin n`. None of it
  was needed. Lemma 3.1 plus one gap argument bounds the first turn without
  computing a single intermediate configuration.
- **The gap argument is the whole trick.** On a ladder every gap is `d` and
  stays `d` while all drones head right; a drone that turns left must be
  co-located with its right-hand neighbour; so the first drone to turn is the
  one that has no right-hand neighbour. That single observation replaces the
  entire outbound phase of the trace.
- **A lower bound needs less than a trace.** The trace says where every drone
  is at every moment; the theorem needs only that *one* drone is outside its
  interval at *one* late instant. Sizing the item from the construction rather
  than from the statement is what made it look like an `M`.

---

### C1′ — the nondeterminism as a relation  ✅

**Built.** `Dpss/Nondeterminism.lean` — `LegitDir`, `StepRel`, `IsRun`,
`not_strictly_inside_of_grouped`, `legitDir_unique`, `isRun_eq_run`,
`convergesBy_of_isRun`, and `ExamplesThree.triple` as the non-vacuity witness.

**Insights.**

- **Read the source again before executing the plan.** The item was sized at
  `L` on the assumption that the development had to be re-proved over
  trajectories. The paper's own sentence — *"our upper bound only concerns
  phase 2, where these issues do not arise"* — says it does not, and that
  sentence is a provable claim about reachable states. The estimate was made
  from the Lean side without re-reading the twenty lines of prose that defined
  the problem.
- **The ambiguity has a crisp geometric characterization.** The two escort
  headings differ exactly when the meeting point is strictly inside the middle
  drone's own interval — which is word for word what the paper describes. Once
  that is written down, the impossibility proof is four cases and each closes on
  an invariant that was already proved.
- **A collapse theorem is better than a refactor.** Re-proving 350 theorems
  over trajectories would have produced the same corollary and taught nothing.
  Proving the relation is a function on reachable states explains *why* the
  nondeterminism never mattered — and leaves a witness (`triple`) showing it is
  real everywhere else.
- **Keep the width honest.** A specification that quietly admits only one value
  makes uniqueness vacuous. `triple_ambiguous` exhibits a configuration where
  the open clause genuinely admits two headings, so the collapse theorem has
  content.

---

## Standing hazards

- **Two attempts at B1 failed by guessing an invariant's shape.** Derive, write
  down, then prove.
- **Measure a gap before restating it.** C1 spent months in three documents as
  a caveat that turned out to be seven-eighths wrong.
- **Size an item from the statement, not from the construction.** C1′ and C3′
  were both sized for the obvious route and both fell to a short argument. Look
  for the argument before budgeting for the machinery.
- **Re-read the source before executing a plan item.** C1′'s `L` estimate was
  made without re-reading the paragraph that defined the problem, which said
  the work was unnecessary.
- **When a case analysis will not close, suspect the goal.** Building the §3.20
  counterexample took less time than the failed proof did, and produced
  something permanent.
- **`sorry` is never acceptable here** — CI enforces it, and the whole value of
  the artefact is that its claims are checkable.
- **Run `scripts/audit.py` before quoting a theorem count.** It has been wrong
  in commit messages three times.
- **Edit `STATUS.md` by section boundary, not by prose matching.** Four silent
  edit failures so far, each behind a commit message claiming otherwise.
