# DPSS formalization — status

<!-- BEGIN:META -->
**Generated:** 2026-09-12  
**Commit at time of writing:** `d42b1703191b`  
**Toolchain:** Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release), Mathlib v4.33.1
<!-- END:META -->

> **Companion:** `INSIGHTS.md` records the non-obvious things this project
> taught us — the bug a concrete trace caught that 145 theorems missed, why the
> non-Zeno proof departs from the paper's, and the Lean mechanics that cost
> real time. Read it before extending the work.

This document is written to be *audited*, not just read. Every claim about what
is proved is backed by machine output reproduced verbatim in §6, and §7 tells
you how to regenerate it yourself. §4 is the part to read if you want to know
what is **not** done; it was for a long time deliberately longer than §3, and
most of it is now struck through rather than deleted, so that a reader can see
what changed instead of having to diff.

---

## 1. Scope, as agreed

| Decision | Choice |
|---|---|
| How far | Stages 0–3 committed; the `2 − 1/n` proof itself a stretch goal — **reached**, §3.28 |
| Algorithm | **A only** (all drones already hold correct estimates) |
| Time model | **Continuous real time** — positions and times in `ℝ` |
| Verification | Read both primary papers in full before writing Lean |
| Write-up | Teaching-grade commentary in every file |

Target theorem, from Avigad–van Doorn (arXiv:2008.04262) Theorem 2.1:

> Assuming all the drones have the correct estimates, they are all synchronized
> at time `2 − 1/n`.

---

## 2. Stage status

| Stage | Deliverable | State |
|---|---|---|
| 0 | Toolchain, Mathlib project, papers read, `[verify]` items resolved | **done** |
| 1 | Definitional layer: state, events, runs, order invariant, non-Zeno | **done** |
| 2 | `Synchronized` defined; Theorem 2.1 stated | **done** |
| 3 | Sanity tests at `n = 2, 3` | both traced, converging and steady; the phase-1 refutation is out of scope, see gap 6 |
| 4 | Close the `2 − 1/n` proof | **done** — `convergesBy`, §3.29. Lemmas 3.1–3.7 all proved |
| 5 | Phase-1 upper bound (open problem) | explicitly out of scope |
| — | **The whole work package** | **complete** — §9 |

Stage 1 broken down:

| Piece | State |
|---|---|
| Geometry: assigned intervals, endpoints | done |
| `Config` (time, positions, directions) | done |
| Motion between events (`advance`) | done |
| Ordering invariant under motion | done |
| The three events as state transformations | done |
| Per-event scheduling (when each event comes due) | done |
| Combining them into `timeToNextEvent` (a minimum) | done |
| `timeToNextEvent` strictly positive (local non-Zeno) | done |
| `step` and runs | done |
| Drones stay on the perimeter (`onPerimeter_step`) | done |
| Lemma 3.1: where a drone may turn | done |
| Crossing an interval costs `1/n` of time | done |
| Escorts stay coherent (`escortsCoherent_step`) | done |
| Invariants hold along a whole run (`invariant_run`) | done |
| Concrete examples; bounce regression test | done |
| Full `n = 2` trace; synchronized forever; period 1 | done |
| Converging `n = 2` trace, checked against the bound | done |
| `n = 3` steady state; period `2/n`; simultaneous events | done |
| **Non-Zeno** (`nonZeno`) | **done** |
| Reading the system **between** events (real time) | done |
| Lemmas 3.2–3.7 | done |
| **Theorem 2.1** (`convergesBy`) | **done** |
| The bound is **attained**, not merely proved | done at `n = 2` |

---

## 3. What is actually proved

<!-- BEGIN:COUNTS -->
**658 theorems**, all `sorry`-free, across 34 files (`BalanceInvariant.lean` 321 lines, `Basic.lean` 213 lines, `Coherence.lean` 386 lines, `Convergence.lean` 314 lines, `Counterexample.lean` 170 lines, `Dynamics.lean` 228 lines, `Events.lean` 246 lines, `EventsTurn.lean` 320 lines, `EventuallyTurns.lean` 136 lines, `Examples.lean` 805 lines, `ExamplesThree.lean` 375 lines, `InductionStep.lean` 265 lines, `IntModel.lean` 845 lines, `LeftSyncLemmas.lean` 224 lines, `Meeting.lean` 443 lines, `Mirror.lean` 737 lines, `NextEvent.lean` 315 lines, `NonZeno.lean` 143 lines, `NonZenoProof.lean` 160 lines, `Nondeterminism.lean` 461 lines, `PairBalance.lean` 472 lines, `PhaseInvariant.lean` 123 lines, `Priority.lean` 273 lines, `Reachable.lean` 207 lines, `RealTime.lean` 341 lines, `Schedule.lean` 214 lines, `Sharpness.lean` 363 lines, `SharpnessGeneral.lean` 384 lines, `Step.lean` 249 lines, `Synchronization.lean` 161 lines, `ThreeConverge.lean` 552 lines, `TurnPersistence.lean` 99 lines, `TurnSpacing.lean` 116 lines, `Turning.lean` 180 lines).
<!-- END:COUNTS -->

### 3.1 `Dpss/Basic.lean` — geometry and snapshots

Drone `i` is assigned the interval `[i/n, (i+1)/n]`. (The paper uses 1-based
indexing with `[(i-1)/n, i/n]`; Lean's `Fin n` is 0-based, so every cross-check
against the paper carries an off-by-one. This is documented at the top of the
file.)

- `rightEnd_sub_leftEnd` — every assigned interval has width exactly `1/n`.
  This is the quantity that becomes the `1/n` in the final bound.
- `leftEnd_lt_rightEnd` — intervals are nondegenerate.
- `rightEnd_eq_leftEnd_succ` — **adjacent drones share an endpoint.** The point
  a meeting pair escorts each other to.
- `leftEnd_zero`, `rightEnd_last` — the end drones' intervals reach the
  perimeter borders.
- `Config` — a snapshot: time, positions, directions. Carries **no estimates**;
  Algorithm A assumes them correct, which makes them redundant. The ACL2
  mechanization drops them for the same reason.

### 3.2 `Dpss/Dynamics.lean` — motion, and the ordering invariant

`advance c dt` flies every drone `dt` forward at unit speed, nobody turning.

- `gap_advance` — **the engine of the file.** The gap between adjacent drones
  evolves linearly: `gap + sepRate · dt`, where `sepRate ∈ {-2, 0, +2}`
  (approaching / holding station / separating). Nearly everything else follows
  from this plus `linarith`.
- `sepRate_of_approaching`, `sepRate_nonneg_of_not_approaching` — the case split
  that decides whether ordering is at risk at all.
- **`ordered_advance`** — *the main result so far.* If the team starts ordered
  and flies forward by no more than the time to the next collision, it stays
  ordered. Not free: drones heading at each other close at rate 2, so flying too
  far makes them pass through each other — the model stays well-defined and
  simply stops describing DPSS.
- `ordered_of_adjOrdered` — lifts pairwise ordering to the full order relation
  by induction on index distance.

**Anti-vacuity checks.** A wrong definition can support perfectly pretty
theorems, so `meetTime` is pinned down independently:

- `gap_eq_zero_at_meetTime` — fly approaching drones exactly that long and the
  gap is exactly zero, i.e. they really are co-located. Without this,
  `ordered_advance` could be guarding a quantity unrelated to collisions.
- `gap_pos_before_meetTime` — the gap is strictly positive strictly earlier, so
  `meetTime` is the *first* collision, not merely *a* collision.

### 3.3 `Dpss/Events.lean` — the three events

Events change **directions only**; positions are untouched. That is why the
ordering obligation lives entirely in `Dynamics.lean`.

- `doBorder` / `doMeet` / `doSeparate`, with `AtLeftBorder`, `AtRightBorder`,
  `CoLocated`, `Escorting`, `AtSeparation` saying when each fires.
- `escorting_doMeet` — after a meet, both drones point the same way.
- `sepRate_eq_zero_of_escorting` + `coLocated_advance_of_escorting` — **an
  escort needs no special representation.** Because speeds are uniform, a
  co-located pair pointing the same way stays co-located automatically. The
  brief worried that "modelling a co-moving group as first-class is probably
  the right call"; it turns out not to be necessary.
- `doSeparate_dir_left` / `doSeparate_dir_right` — after separating, the left
  drone heads left and the right drone heads right. Lemma 3.2 of the paper
  opens with exactly this.
- `not_approaching_doSeparate` — a just-separated pair is not closing, so it
  cannot re-collide without first turning around.
- `adjOrdered_doMeet` / `_doSeparate` / `_doBorder` — events preserve ordering.

### 3.4 `Dpss/Schedule.lean` — when each event comes due

Each event kind gets a time, and **each time gets a correctness theorem**
saying that flying for exactly that long really does establish that event's
precondition. That pairing is the whole point: a scheduler returning
plausible-looking numbers unrelated to the events it claims to schedule would
sail through a convergence proof and mean nothing.

- `pos_eq_zero_of_le` / `pos_eq_one_of_ge` — **who can be at a border.** The
  border predicates deliberately do *not* stipulate which drone is involved;
  that would be building a conclusion into a definition. Instead these recover
  it: if a drone sits on the left border then so does everyone to its left,
  pinned between that drone and the edge of the perimeter.
- `separationTime`, `leftBorderTime`, `rightBorderTime` — all of the form
  "signed distance ÷ unit speed", signed so the time is nonnegative exactly
  when the event is *ahead* of the drone rather than behind it.
- `pos_eq_commonEnd_at_separationTime`, `atLeftBorder_at_leftBorderTime`,
  `atRightBorder_at_rightBorderTime`, `coLocated_at_meetTime` — the four
  correctness theorems.
- `atSeparation_at_separationTime` — an escorting pair stays escorting as it
  flies, so the separation becomes due for *both* drones simultaneously.
- **`separationTime_nonneg_doMeet` / `separationTime_pos_doMeet`** — the real
  content of `escortDir`: after a meet, the separation it creates is genuinely
  in the future, *strictly* so unless the pair met exactly on their shared
  boundary. That exceptional case is the paper's *bounce* — a meet and a
  separation coinciding. Everywhere else, a meet buys strictly positive time
  before the next event for that pair, which is exactly the kind of fact
  non-Zeno gets assembled from.

### 3.5 `Dpss/NextEvent.lean` — the time to the next event

Takes the **minimum** over all the scheduled times and proves the fact that
matters.

- `borderTime` + `borderTime_pos` — a drone not currently at a border has
  strictly positive time to reach one.
- `separationTime_eq_zero_iff` — a separation is due exactly when the pair sits
  on its shared boundary; the direction factor never vanishes and so never
  interferes.
- `NoEventDue` — no event of any kind is due at this instant. The subtle clause
  is the meet one: a meet is due when a pair is co-located **and closing**, not
  merely co-located. A co-located pair moving apart has just separated and owes
  nothing. Had this been plain `CoLocated`, the predicate would have excluded
  every mid-escort configuration — a perfectly ordinary state — and the theorem
  below would have been close to vacuous.
- `EscortsCoherent` — escorts point at the boundary they are escorting to.
  Guaranteed by any meet event (`separationTime_nonneg_doMeet`); assumed of a
  start configuration.
- **`timeToNextEvent_pos`** — *the main result of the file.* If no event is due
  right now, the team can fly a strictly positive stretch before anything
  happens. No zero-length steps, so an event sequence cannot stall.

**What this is not.** `timeToNextEvent_pos` is the *local* half of non-Zeno and
nothing more. Infinitely many strictly positive steps can still sum to a finite
time — that is exactly how Zeno behaviour works. Ruling it out needs a uniform
lower bound on the step sizes, following Avigad–van Doorn §2. Not started.

### 3.6 `Dpss/Step.lean` — one step of the system

Fly to the next event, then let everything due fire. Because several events can
come due at once, each drone's post-event direction is a function of the whole
configuration (`newDir`) rather than a composition of updates, so simultaneity
is automatic and no ordering of updates needs justifying.

`newDir` resolves competition as **border > separation > meet**. Most of these
can never compete: a drone cannot meet both neighbours (that needs opposite
headings), nor separate from both (the two points differ). A separation and a
meet *can* coincide — the genuine ambiguity the paper leaves open — and giving
separation priority looked like *one* resolution among several. It is not:
§3.31 shows the order is forced in seven of its eight competing cases, and
§3.33 shows the paper's actual open case cannot arise on a reachable
configuration. Gap 5 is closed.

Proved: `adjOrdered_step` (a step never flies past a collision, so nobody
overtakes) and `step_time_lt` (time strictly advances when nothing was due).
`run` is the orbit of `step`; `NonZeno` is *stated*.

### 3.7 `Dpss/Turning.lean` — **Lemma 3.1**

The first result here that is a named theorem *of the paper*.

- `rightEnd_le_pos_of_turnsLeft` — a rightward drone can only turn left at or
  beyond its right endpoint.
- `pos_le_leftEnd_of_turnsRight` — the mirror image.

Every case is forced: a border turn is at the perimeter edge, past the
endpoint; a separation is exactly on it; a meet reverses the drone only if the
pair met beyond it; and the remaining events cannot apply to a drone heading
that way at all.

`turn_separation` — a drone turning right and later left has crossed its entire
interval, a distance of `1/n`.

### 3.8 `Dpss/NonZeno.lean` — crossing costs time

- `pos_sub_eq_of_dirConst` — while a drone holds its heading, its position
  advances exactly as time does. This is where the normalization "one unit of
  distance per unit of time" is finally cashed in.
- `time_advance_of_crossing` — therefore crossing the interval costs at least
  `1/n` of time. With Lemma 3.1: **consecutive turns of one drone are at least
  `1/n` apart.**

A subtle off-by-one is documented in the file. A step flies *first* and turns
*afterwards*, so a drone turning during step `k` flew with heading
`(run k).dir i` but turned at position `(run (k+1)).pos i`. Getting that
backwards would have silently wrecked every bound in the file.

### 3.9 `Dpss/Synchronization.lean` — the goal, stated

- `onPerimeter_step` — **the first genuine invariant of the running system**
  rather than a fact about one step in isolation. Drones never leave `[0,1]`,
  because a step never flies longer than any drone's time to the border it is
  heading for.
- `LeftSync` / `RightSync` / `Sync` / `AllSync` — the paper's safety property,
  quantified over run indices. Not a weakening: motion between events is
  monotone, so a drone inside its interval at every event time is inside it at
  *every* time.
- **`ConvergesBy`** — Theorem 2.1 as a formal statement. A `Prop`-valued
  definition rather than a `theorem` with a `sorry`, so the repository stays
  provably `sorry`-free while still recording the target precisely.
- `convergesBy_of_one` — the `n = 1` case, **proved**. Mathematically trivial,
  but it confirms the definitions are not mis-signed or vacuous.

### 3.10 `Dpss/Coherence.lean` — the last assumption, discharged

`EscortsCoherent` — escorts point at the boundary they are escorting to — had
been *assumed* everywhere it was needed. It is now proved.

**`escortsCoherent_step` needs no hypotheses at all.** That was a surprise: I
wrote it with `OnPerimeter`, `AdjOrdered` and the old coherence as premises and
Lean reported all three unused. The reason is structural — `droneNextTime`
always includes an escorting pair's `separationTime` among the candidates it
minimises over, so **a step can never overshoot a separation**. Coherence is
enforced by the scheduler rather than inherited.

The proof is a case analysis on which branch of `newDir` fired for drone `i`.
A border event, a separation, or a meet with the right neighbour each settle
the sign immediately. Two branches need `commonEnd_le_pos_of_both_left`: if a
co-located pair both end up heading left, they must be at or beyond their
shared boundary — established by asking what could have turned drone `i+1` that
way, and finding every possibility puts it there.

**And so the invariants close under iteration**, which is the point at which
this development stops reasoning about isolated steps and starts reasoning
about the running system:

- `Invariant` — on the perimeter, in order, escorts coherent.
- `invariant_step`, **`invariant_run`** — preserved by a step, hence along an
  entire run.
- `onPerimeter_run`, `ordered_run`, `time_mono_run` — drones never leave the
  perimeter, never overtake one another, and time never runs backwards. Ever.
- `convergesBy_of_one'` — Theorem 2.1 at `n = 1`, now **unconditional**. What
  was previously a hypothesis ("assume they stay on the perimeter") is a
  theorem.

### 3.11 `Dpss/Examples.lean` — concrete configurations and a full trace

Everything else here is universally quantified, and nothing forces the
definitions to be *satisfiable*. A formalization whose hypotheses can never be
met proves a great deal about nothing at all.

**Working one concrete case found a real bug.** `bounce` is two drones meeting
exactly on the boundary they share — the paper's *bounce*, a meet and a
separation at the same instant. `AtSeparation` originally required the pair to
be **escorting**, i.e. co-located *and heading the same way*. But two drones
converging on their shared boundary have **opposite** headings right up to the
instant they meet. So no separation fired, the meet branch took over, and the
right-hand drone was sent **left — out of its own interval**, permanently
destroying the very property this development exists to prove. It was invisible
to 145 passing theorems.

`bounce_newDir_d0`, `bounce_newDir_d1` and `bounce_separates` now pin the
correct behaviour down as a regression test.

#### A complete trace at `n = 2`

The system is `noncomputable` (real division, and `newDir` uses classical
choice) so it cannot be `#eval`ed. The trace is therefore built as symbolic
proof: `timeToNextEvent_two` reduces the team-wide deadline to a `min`, and
three step equations do the rest.

    approach ──1/4──▶ atBoundary ──1/2──▶ atEnds ──1/2──▶ atBoundary ──▶ ⋯

- `step_approach`, `step_atBoundary`, `step_atEnds` — one step each, exactly.
- **`run_approach`** — by induction, the configuration at *every* step index.
  The system alternates forever between the two steady-state configurations.
- **`approach_allSync`** — **the first end-to-end result about a running DPSS
  system here**: not a property of one step but of the entire infinite future.
  Every drone stays inside its own interval for all time.
- `approach_converges` — Theorem 2.1 holds for this configuration, and
  comfortably: the `n = 2` bound is `3/2` and this team is synchronized at time
  zero.
- **`approach_period`** — the steady state repeats with period **1** in time.
  The paper gives the steady-state period as `2/n`, which at `n = 2` is exactly
  1. **This is an independent check of the model against a number the paper
  states**, and it agrees.

#### A trace that actually converges

`approach` is already synchronized at time zero, so it only shows the steady
state is a *fixed point*. `spread` is the real test — the paper's worst case
for `n = 2`, scaled to a concrete gap. Both drones start near the left border
heading right, **not quite together**, so they never meet. They run all the way
out to the right border, and only then turn, meet, and escort back.

    spread ─3/4─▶ chase ─1/8─▶ escortBack ─3/8─▶ atBoundary ─▶ (steady cycle)

- `spread_not_allSync_zero` — **this team starts out of position.** At step 1
  the left drone sits at `3/4`, far outside its interval `[0, 1/2]`. So there
  is genuine convergence here to demonstrate, not just a fixed point.
- `run_spread` — the configuration at every step index, by induction.
- **`spread_allSync_three`** — from step 3 onward, every drone is confined to
  its own interval **forever**.
- **`spread_sync_within_bound`** — synchronization happens at time `5/4`, and
  Theorem 2.1 promises `2 - 1/n = 3/2`. The trace sits inside the bound, as it
  must. **A second independent numerical check against the paper.**
- `spread_converges` — Theorem 2.1 itself, for this configuration.

Also `approach_invariant`: the standing invariant of a run is satisfiable,
without which every theorem conditioned on `Invariant` would hold vacuously.

This section vindicates the ordering decision made at the very start: validate
the model (Stage 3) before proving the headline theorem about it (Stage 4).

### 3.12 `Dpss/ExamplesThree.lean` — three drones

With only two drones, several parts of the model are never exercised: there is
no **middle** drone, so `SepLeft` never fires for a drone that also has a
right-hand neighbour, and no two events ever fire at once. Avigad–van Doorn
call `n = 3` the first interesting case.

The intervals are `[0, 1/3]`, `[1/3, 2/3]`, `[2/3, 1]`, and the steady state is
a two-configuration cycle:

    B = (1/3 ←, 1/3 →, 1 ←)  ──1/3──▶  C = (0 →, 2/3 ←, 2/3 →)  ──1/3──▶  B

**Each step fires two events simultaneously** — the middle drone separates from
one neighbour while an end drone bounces off a border. That simultaneity is the
entire reason `newDir` is a function of the whole configuration rather than a
composition of updates, and it had never been tested before this file.

- `step_cfgB`, `step_cfgC` — one step each, exactly.
- `run_cfgB` — the configuration at every step index.
- `cfgB_allSync`, `cfgB_converges` — synchronized forever; Theorem 2.1 holds.
- **`cfgB_period`** — the period is `2/3`, which is `2/n` at `n = 3`. **A third
  independent numerical check against the paper**, and the first at a team size
  where drones interact three-way.
- `cfgB_invariant` — the standing invariant is satisfiable at `n = 3` too.

Writing this caught a mistake of mine: I asserted the middle and right drones
were *not* approaching in configuration B. They are, and Lean rejected the
lemma until it was stated correctly.

### 3.13 `Dpss/PairBalance.lean` — opening Lemma 3.2

Lemma 3.2 is the gate to the convergence proof: *if drone `j` is left
synchronized and `j`, `j+1` separate at their common endpoint, then `j+1` is
left synchronized too.* Lemmas 3.3, 3.4 and 3.7 all quote it.

The paper argues it through timing — *"drone `j+1` must have taken at least as
long to turn around as drone `j`"* — with a picture. That is awkward to
formalize directly. The same content packs into a single number, the pair's
**balance** about the boundary they share:

    balance = (pos j − commonEnd) + (pos (j+1) − commonEnd)

- `pairBalance_advance` — it evolves linearly at `sign j + sign (j+1)`, so it
  is **constant whenever the drones head opposite ways**, which is exactly what
  they do immediately after separating and again while approaching.
- `pairBalance_eq_zero_of_atSeparation` — **a separation zeroes it.**
- `commonEnd_le_pos_of_coLocated` — **its sign decides where the pair can
  meet**: nonnegative balance means any co-location happens at or beyond the
  shared boundary, which is exactly the induction hypothesis Lemma 3.2 carries.
- `leftEnd_le_pos_of_pairBalance` — the payoff. A nonnegative balance keeps the
  right-hand drone at or beyond its own left endpoint, i.e. **left
  synchronized**.
- `leftSync_of_balanceNonneg` — **Lemma 3.2, modulo one obligation.**

#### The obligation, reduced to one configuration

`BalanceNonneg` — the balance, once zero, never goes negative — is written as a
*definition*, not assumed as a hypothesis, so it stays visible as open and
cannot be used by accident.

It is now narrowed to a single named configuration class. The balance falls
only when both drones head left; and when both head left while **co-located**
they are escorting, so the scheduler cannot run the step past their separation,
which is exactly where the balance reaches zero. `pairBalance_nonneg_step`
proves all of that. What is left is:

> **`BothLeftApart`** — both drones of the pair heading left *while apart*.
> The only way the balance can go negative.

`balanceNonneg_of_never_bothLeftApart` closes the loop: rule that class out and
the balance stays nonnegative forever, hence Lemma 3.2.

Two further pieces of the timing argument are proved:
`pos_eq_leftEnd_of_turnsRightAt_of_leftSync` — **a left-synchronized drone
turns round exactly at its left endpoint** (Lemma 3.1 puts the turn at or
before it; synchronization forbids going beyond), and its mirror image. That is
the paper's one-line *"since it is left synchronized, we know it is at its left
endpoint"*, and it is what fixes the drone's turn time at exactly `1/n` after
leaving the boundary — hence no later than its neighbour's.

#### Two of the three branches are closed

`BothLeftApart` can appear at a step in exactly three ways:

1. **the left drone reverses to leftward** — *impossible*. Whatever reverses a
   rightward drone — a meet with its neighbour, a separation from it, or the
   right perimeter border — leaves it **co-located** with that neighbour, so it
   is never *apart*. `coLocated_of_turnsLeft`.
2. **neither drone reverses** — *impossible*. They were already escorting and
   uniform speed keeps them together. `coLocated_step_of_both_left`.
3. **the left drone holds its heading while the right one reverses** — **open.**

Case 3 is where drone `j`'s left synchronization has to work, and the useful
discovery is that the argument is **positional, not temporal**. In the
preceding state the pair heads in opposite directions, so the balance is
constant; from a separation it is zero, so the two are displaced from the
shared boundary by *equal* amounts. Left synchronization caps the left drone's
displacement at `1/n`, hence caps the right drone's at `1/n` too — putting it
at or *before* `rightEnd (j+1)`. But Lemma 3.1 only permits it to reverse at or
*beyond* that point. So the two coincide exactly, both drones are pinned to
their endpoints, and the left drone must reverse as well — contradicting the
premise of case 3.

The **mathematical core of case 3 is now proved**:
`pos_next_le_rightEnd_of_balance_zero` (with the balance at zero, left
synchronization caps where the partner can be — at or *before* its own right
endpoint) and **`pinned_of_balance_zero`** (so if the partner does turn, Lemma
3.1's lower bound meets that upper bound exactly, pinning *both* drones to
their endpoints).

What is left is bookkeeping, not mathematics, and it is fiddlier than it looks
for one reason: **a step can legitimately take zero time**, when an event is
already due. So showing the left drone *turns* at its endpoint — rather than
merely being entitled to — means ruling out an unbounded run of zero-length
steps in which it sits there heading outward. `nonZeno` rules that out
globally, so the ingredients exist; assembling them over run indices is the
remaining work. Plus the invariant that the balance is exactly zero while the
pair moves apart.

### 3.14 `Dpss/EventsTurn.lean` — **every step turns a drone**

**A1 and A2** of the work package, complete and unconditional. Independent of
every convergence lemma.

`Turning.lean` showed consecutive turns of one drone are at least `1/n` apart.
To turn that into "only finitely many events fit in a bounded interval" needs
the other half: each event actually reverses somebody. Then `k` steps force
some drone to turn about `k/n` times, and the `1/n` spacing bounds the elapsed
time from below.

A step's length is set by one of exactly three deadlines, and each is handled:

- `someDroneTurns_of_atLeftBorder` / `_atRightBorder` — a drone reaching the
  perimeter edge reverses. (With `not_atLeftBorder_of_atRightBorder`: a drone
  cannot be at both ends at once.)
- `someDroneTurns_of_separation` — an escorting pair arrives heading the *same*
  way and leaves heading opposite ways, so exactly one of them has turned.
- `someDroneTurns_of_meet` — a meeting pair arrives heading *opposite* ways and
  leaves heading the same way, so again exactly one has turned.

The meet case rests on an identity worth naming on its own,
`escortDirLeft_next_eq_escortDir`: when a pair is co-located, the heading the
left drone adopts on meeting its right neighbour and the heading the right
drone adopts on meeting its left neighbour are **the same direction**. That is
what makes an escort an escort.

**`someDroneTurns_step`: every step of the system reverses at least one drone,
with no hypotheses at all.** The proof picks the drone whose deadline attained
the minimum (via `Finset.exists_mem_eq_inf'`), splits on which of its three
deadlines that was, and discharges each. Borders are handled first and
unconditionally, so the meet and separation cases may assume no drone is at a
border — exactly what they need.

The hard part was **cascades**: three or more drones arriving together, so a
drone meeting its right neighbour may simultaneously be separating from its
left one. `someDroneTurns_of_meet_due` handles it by case analysis on which
`newDir` branch claims each drone. Every branch closes on the same observation:
a drone cannot sit on two different boundaries at once, because
`leftEnd i < commonEnd i < commonEnd (i+1)`.

With `turn_separation` from §3.7 — consecutive turns of one drone are at least
`1/n` apart — this is **the other half of non-Zeno**. What remains is counting:
`k` steps force turns, turns are spaced, so time cannot stand still.

### 3.15 `Dpss/TurnSpacing.lean` — turns of one drone are spaced out

**A3** of the work package, less the counting.

`Turning.lean` established *where* a drone may turn; `NonZeno.lean` established
that crossing between those two points costs `1/n` of time. This file joins
them along a run:

> **`time_gap_of_consecutive_turns`** — between two consecutive turns of the
> same drone, at least `1/n` of time elapses.

Between them the drone holds a single heading (`dir_const_of_no_turns`) and
crosses its whole assigned interval, endpoint to endpoint, because that is the
only place it is allowed to reverse.

**Non-Zeno now has both halves.** Every step turns somebody (§3.14); turns of
any one drone are `1/n` apart (here). What remains is purely the counting:
`k` steps force `k` turns spread over only `n` drones, so some drone turns at
least `k/n` times, and its turns are spaced — so the clock must have advanced
by roughly `k/n²`, without bound. That is a pigeonhole over `Fin n` and nothing
about DPSS.

### 3.16 `Dpss/NonZenoProof.lean` — **non-Zeno, proved**

> `nonZeno : ∀ T : ℝ, ∃ k, T < (c.run hn k).time`

The system cannot pack infinitely many events into a finite stretch of time.
Every instant is eventually passed.

**This is the property the existing ACL2 mechanization could not establish.**
Its event-stepper was admitted as a *partial* function and
`(step-time-always-terminates)` is carried as an unproved hypothesis into its
top-level convergence theorem. Avigad–van Doorn give an argument but never
mechanize it.

The argument here is **not the paper's**. Theirs rests on a claim about
consecutive left turns propagating between neighbours that I could not
reconstruct (§3.7). This one counts instead:

1. **Every step turns at least one drone** — §3.14, unconditional.
2. **Consecutive turns of one drone are `1/n` apart in time** — §3.15.
3. So among any `n+1` consecutive steps some drone must turn **twice**, there
   being only `n` drones — and those two turns cost `1/n` of clock.

Hence `n+1` steps buy `1/n` of time, `m(n+1)` steps buy `m/n`, and `m` can be
as large as we like. The only non-DPSS ingredient is the pigeonhole
(`Fintype.exists_ne_map_eq_of_card_lt`).

Supporting: `run_add` (stepping `k` then `j` is stepping `k+j`),
`time_mono_run'` (the clock never runs backwards over any stretch), and
`exists_first_turn_after` (a drone that turns has a *first* turn after any
earlier index, with nothing in between — via `Nat.find`).

#### What this does and does not claim

It proves non-Zeno **for this Lean model of Algorithm A**, under the standing
`Invariant` — which §3.10 proves is preserved and §3.11 proves is satisfiable.

It does **not** literally discharge the ACL2 hypothesis: that would require
their model, not this one. What it establishes is the property they had to
assume, in a setting that is strictly more faithful in one respect — ACL2 has
no reals, so their positions are rational, while these are `ℝ`.

It also inherits this development's own restriction: `newDir` picks **one**
resolution of the nondeterminism the paper leaves open when three or more
drones converge (gap 6). A fully general result would quantify over all
resolutions.

### 3.17 `Dpss/LeftSyncLemmas.lean` — **Lemmas 3.3 and 3.4**, and `have met`

With the balance in hand, both corollaries of Lemma 3.2 are short: each needs
only its *starting* configuration to put the balance at or above zero, and in
both cases that falls out at once.

- **Lemma 3.3** (`leftSync_of_escorting_left`) — an escorting pair's balance is
  exactly twice its separation deadline, and escort coherence (proved
  unconditionally in §3.10) says that deadline is never in the past. **The
  balance is nonnegative because the scheduler makes it so.**
- **Lemma 3.4** (`leftSync_of_pos_ge`) — if the left drone has reached the
  shared boundary, ordering carries its neighbour past it too, so both terms of
  the balance are nonnegative separately.
- **Lemma 3.2** is restated in the same form (`leftSync_of_atSeparation`) for
  comparison.

**All three now depend on exactly one open condition**: that the pair is never
`BothLeftApart`. Not on an assumed `BalanceNonneg` — that is discharged from
the starting balance by `balanceNonneg_of_never_bothLeftApart`. So closing the
single remaining case of §3.13 closes 3.2, 3.3 and 3.4 together.

#### `have met`

Lemmas 3.5–3.7 are all phrased in terms of a pair having *met* by some time,
and nothing modelled that. `HaveMetBy` does: **the pair was co-located at some
moment no later than `T`**. The paper's two cases — started together moving the
same way, or involved in a meet or bounce — are both instances of it.

A note left in the file for whoever continues: the ACL2 team reported that
phrasing this over execution *history* "drew heavily on human intuition about
system behaviour and was difficult to work with in a mechanized proof", and
that recasting it as a **locally checkable** predicate over a drone and its
immediate neighbour was what made their development tractable. `HaveMetBy` is
the history-shaped one. If Lemma 3.5 or 3.7 becomes unwieldy, that is the first
thing to change.

### 3.18 `Dpss/TurnPersistence.lean` — **Lemma 3.6**, unconditionally

> If the pair has not been together since step `a`, and drone `i` is heading
> left at step `b`, then it has been heading left ever since `a`.

Short here, because `PairBalance.lean` already proved the load-bearing step for
its own reasons: **a drone that reverses to leftward is co-located with its
right-hand neighbour**. Whatever can reverse a rightward drone — a meet, a
separation, or the right border — leaves it on top of its neighbour.

So over a stretch in which the pair is never together, the left drone never
turns left (`not_turnsLeftAt_of_never_coLocated`); and a drone found heading
left at the end of such a stretch must have been heading left throughout, since
it cannot have turned left and had it turned right it would still be heading
right (`dir_left_of_no_turnsLeft`).

**No dependence on `BothLeftApart`** — this one is complete.

The paper phrases `a` as "the last time before `t` that they bounced or
separated"; here it is any step after which they have not been together, which
is the property the proof actually uses and is easier to supply.

### 3.19 `Dpss/PhaseInvariant.lean` — why a drone ends up heading where it does

Closing Lemma 3.2's last case needs to know not just *that* a drone ends a step
heading some way, but **why**. `newDir_left_cases` and `newDir_right_cases`
turn `newDir i = left` (or `right`) into the disjunction of events that could
have produced it.

Also `coLocated_of_turnsRight` in §3.13's file — the mirror of the earlier
result: a drone reversing to **rightward** is co-located with its **left-hand**
neighbour. Whatever can reverse a leftward drone — a meet with its left
neighbour, a separation from it, or the left border — leaves it on top of that
neighbour.

**What this is for, and what is missing.** The target is: *a co-located pair
ending a step heading apart is sitting exactly on the boundary it shares* —
the post-separation configuration, and the only way to be in it. That pins the
balance at zero while the pair moves apart, which is the invariant the last
case of Lemma 3.2 runs on.

Two routes are immediate and are proved (`pos_eq_commonEnd_of_sepRight` and its
mirror). The rest is a nine-way analysis over the two case lemmas, most
branches closing because **a meeting pair always agrees on where to go**
(`meeting_pair_agrees`) so it cannot leave a meeting in opposite directions.
**That analysis is not done.** Doing it will want the two case lemmas
strengthened to carry the negations of the earlier branches, which `split_ifs`
supplies but the current statements discard.

### 3.20 `Dpss/Counterexample.lean` — **a lemma that is false**

The target of §3.19 was:

> *a co-located pair that ends a step heading apart is sitting exactly on the
> boundary they share.*

It reads as obviously true — heading apart is what a pair does **after
separating**, and separations happen on the boundary. Working the case analysis
with the branch negations carried, one combination refused to close. It refused
because **the statement is false**, and this file proves it so.

Four drones stacked at `3/8`, heading alternately:

    drone 0 →     drone 1 ←     drone 2 →     drone 3 ←        all at 3/8

The middle pair is `(1, 2)`; their shared boundary is `1/2`.

* Drone 1 is meeting its **left** neighbour, and `3/8` is past drone 1's own
  left endpoint `1/4`, so it escorts **leftward**.
* Drone 2 is meeting its **right** neighbour, and `3/8` is short of drone 2's
  right endpoint `3/4`, so it escorts **rightward**.

Neither is separating from the other — that would need them at `1/2`. So the
pair leaves the step heading apart at a point that is **not** their shared
boundary. `not_forall_apart_implies_on_boundary` states the refutation.

**What it means.** The lemma needs **reachability**. In a state the algorithm
can actually produce, a pair heading apart has just separated, so the statement
is presumably true where it is needed — but it must be carried as an induction
hypothesis, not proved pointwise. My attempt did neither, which is why it would
not close.

It is also exactly the nondeterminism Avigad–van Doorn flag: three or more
drones converging, a middle drone free to escort either neighbour. Here *two*
middle drones each pick the outward neighbour and the pair splits early.

**Second time in this project** that reaching for a concrete instance overturned
something that read as obvious — the first was the bounce bug (§3.11).

### 3.21 `Dpss/Reachable.lean` — the invariant the counterexample called for

§3.20 showed the pointwise statement is false. So it is an **invariant**, and
this file builds it.

`ApartOnBoundary` — *a co-located pair heading apart sits on the boundary it
shares* — false pointwise, true along runs.

Two moves carry the preservation argument, and both are proved:

- **`apart_transfer`** — the crux. A pair heading apart separates at rate 2, so
  if it is *still* co-located after flying forward, the gap must have been zero
  **and the step must have taken no time at all**. The configuration carries
  over unchanged, and with it the induction hypothesis. This is what the
  counterexample's route runs into: it forces the pair to have been co-located
  and already heading apart *before* the step.
- **`not_apart_of_meet`** — a meeting pair cannot leave the meeting heading
  apart, because both drones adopt the *same* heading
  (`escortDirLeft_next_eq_escortDir`). That kills most of the remaining routes.

**What is not done:** the full preservation theorem, which enumerates how
`newDir` could have delivered `left` to one drone and `right` to the other and
applies the above to each route. The two hard moves exist; what remains is the
enumeration, and §3.20 is the map of which branch needs which move.

### 3.22 `Dpss/EventuallyTurns.lean` — every drone turns, and how soon

A step towards **Lemma 3.5**. Its proof opens with *"eventually `j` turns
around at or before it reaches 0, and `j+1` turns around at or before it
reaches 1"* — taken for granted, as it should be on paper.

Formally it needs an argument, and it is **where non-Zeno finally pays for
itself** beyond being a headline result:

- A drone that never turned would hold one heading forever, so its position
  would track elapsed time exactly (`pos_sub_eq_of_dirConst`).
- Non-Zeno says elapsed time is **unbounded**.
- So it would leave the perimeter, which `onPerimeter_run` forbids.

Without non-Zeno the clock could stall and the drone sit still forever, never
turning and never leaving `[0,1]`. **This lemma could not have been proved
earlier in the development.**

- `exists_dir_right_of_dir_left` and its mirror; `exists_turn` — every drone
  turns, whichever way it starts.
- `time_bound_of_dir_left` / `_right` — the quantitative form Lemma 3.5 needs:
  a drone cannot head left for longer than its distance to `0`, nor right for
  longer than its distance to `1`. These are the `w` and `z` of the paper's
  proof, which bounds the meeting time by `z − w ≤ 1`.

### 3.23 `Dpss/Mirror.lean` — the perimeter reflected (**B7**, part 1)

Avigad–van Doorn get right synchronization in four words — *"by symmetry"* —
which on paper is honest and in Lean is not. The way to make it honest is a
**reflection**: flip the perimeter end-for-end, reverse every heading, renumber
the drones backwards.

    position   x  ↦  1 − x        heading  →  ↦  ←        index  i  ↦  n−1−i

The algorithm is invariant under that, so right synchronization of a run *is*
left synchronization of the mirrored run, and every result proved on the left
transfers for free.

Done here:

- `mirrorIdx`, an involution that reverses the drone ordering.
- `leftEnd_mirrorIdx` / `rightEnd_mirrorIdx` — **the endpoints swap**: the
  reflected drone's left endpoint is the reflection of the original's right
  endpoint.
- `Config.mirror`, `mirror_mirror` (an involution on configurations).
- `onPerimeter_mirror`, `ordered_mirror` — the reflection respects the standing
  invariant.
- `leftEnd_le_mirror_pos_iff` and its partner — **the point of the exercise**:
  staying at or beyond your *left* endpoint in the mirrored world is staying at
  or before your *right* endpoint in this one.

**Part 2, done so far:** every local ingredient of a step now has its
reflection law.

- Index identities, including the one everything rests on:
  `nextIdx (mirrorIdx (nextIdx i h)) = mirrorIdx i`.
- `gap_mirror`, `sepRate_mirror`, `coLocated_mirror`, `approaching_mirror`,
  `escorting_mirror`.
- `atLeftBorder_mirror` / `atRightBorder_mirror` — the two border events swap.
- `borderTime_mirror` — a drone's time to its border is **unchanged**: which
  border it heads for swaps, and so does its distance to it.
- `meetTime_mirror`, `separationTime_mirror`.
- **`timeToNextEvent_mirror`** — the global deadline is invariant. This one
  could *not* be done per-drone: `droneNextTime i` consults the pair to `i`'s
  right while its reflection consults the pair to the reflected drone's *left*,
  so per-drone deadlines genuinely do not correspond. What corresponds is the
  candidate *sets*, so the minima agree; the proof bounds each side by the
  other and gets the second direction from the involution.
- `atSeparation_mirror`, `sepRight_mirror`, `meetRight_mirror` — `SepRight`
  becomes `SepLeft` and `MeetRight` becomes `MeetLeft`.

**Part 2 is complete.**

- `newDir_mirror` — the heading a step installs commutes with reflection. Seven
  branches on each side, paired by the correspondences above. The pairing
  *crosses* the priority order (the left border is checked first on one side
  and second on the other), which is harmless because paired branches are
  mutually exclusive — proved as `not_sepLeft_of_sepRight` and friends.
- `advance_mirror`, **`step_mirror`**, **`run_mirror`** — flying, stepping and
  running all commute with reflection.
- **`rightSync_iff_leftSync_mirror`** — *the transfer principle*. Right
  synchronization of a run **is** left synchronization of the mirrored run.
- `invariant_mirror` — the reflection of a well-behaved configuration is well
  behaved, so the principle applies wherever the invariant is assumed.

One subtlety was real: `escortDir` and `escortDirLeft` reflect into each other
**except exactly on the shared boundary**, where they tie-break oppositely —
one reads `pos < boundary`, the other `boundary < pos`, and at equality those
disagree. Both lemmas carry a disequality hypothesis, discharged where used: a
meet is only consulted once a separation is ruled out, and for a co-located
pair a separation *is* being on the boundary.

That is the kind of thing "by symmetry" hides. The mathematics is symmetric;
the **definitions** are not quite, because a strict inequality has to break the
tie one way and reflection turns that into breaking it the other.

A recurring obstacle worth noting: these predicates carry the index inside a
*proof argument*, which blocks `rw` with "motive is not type correct". Four
congruence lemmas (`approaching_congr` and friends) exist purely to substitute
the index first and close by proof irrelevance.

### 3.24 `Dpss/BalanceInvariant.lean` — **B1: Lemma 3.2, unconditional**

The three-clause invariant derived in §8a, stated as `PairPhase` and proved
preserved:

1. `0 ≤ balance`;
2. heading `(left, right)` ⟹ `balance = 0`;
3. `BothLeftApart` ⟹ the left drone sits on its left endpoint.

`pairPhase_step`, `pairPhase_run`, `balanceNonneg_of_pairPhase`, and then
**`leftSync_of_separation`** — Lemma 3.2 with no hypothesis beyond left
synchronization of the left drone, which is its own. **`leftSync_of_escorting`**
is Lemma 3.3, likewise.

**The pleasant part.** A pair that is **apart** cannot change phase at all.
Every event that could deliver `left` to one drone and `right` to the other —
`SepRight`, `MeetRight`, `SepLeft` and `MeetLeft` on the right drone — requires
*this pair* to be co-located, and either border event forces co-location by
ordering. So an apart pair simply carries its balance across untouched, and the
whole difficulty collapses into the co-located case, which §3.21 had already
enumerated.

**What clause 2 is for.** It is not decoration: the pinning argument
(`pinned_of_balance_zero`) needs the balance to be *exactly* zero, not merely
nonnegative. That is why clause 1 alone is not an invariant.

**An asymmetry worth recording.** Lemma 3.4 does **not** get the invariant from
its own hypothesis. Reaching the shared boundary gives a nonnegative balance but
not a zero one, so a pair heading apart from there may carry a strictly positive
balance and clause 2 fails. `leftSync_of_reached_boundary` therefore takes
`PairPhase` as a hypothesis — which a caller inside a run can always supply,
since `pairPhase_run` proves it is preserved. 3.2 and 3.3 are unconditional;
3.4 is conditional on an invariant rather than on an obstruction, which is a
strictly better position than before.

### 3.25 `Dpss/Meeting.lean` — **B3: Lemma 3.5**

> `exists_coLocated_within_one` — every adjacent pair becomes co-located within
> **one unit of time**.

The uniform timing result that makes the bound `n`-independent. Without it the
argument degrades to linear in `n`, which is what Kingston et al.'s original
proof gave.

**Why it goes through cleanly.** A fact that fell out of Lemma 3.2's work: a
drone heading right can only reverse by becoming co-located with its
**right-hand** neighbour, and one heading left only with its **left-hand** one.
So while an approaching pair stays apart, *neither drone can turn* — their gap
closes at a steady rate 2 and non-Zeno gets the clock to zero.

**The phase accounting.** With `x ≤ y` the starting positions, `w` where the
left drone first heads right and `z` where the right one first heads left: the
gap grows until the **first** of the two turns and is constant until the
**second**, after which the pair approaches. The elapsed times add and the
bound collapses to

    (z − w) + (x − y)/2  ≤  1

using only that positions lie in `[0,1]` and `x ≤ y`. **Which drone turns first
does not matter** — the two orderings give the same total.

Supporting: `gap_sub_eq_of_dirsConst` (one equation for every phase — the gap
moves at the *difference* of the two velocities, where the balance moves at
their *sum*), and `exists_firstRight`/`exists_firstLeft`, which give the first
turn **and exactly when it happens**. The exactness is essential: the bound
comes out at exactly 1, so a chain of inequalities would not have closed.

---

### 3.26 `Dpss/RealTime.lean` — reading the system between events

`LeftSync` and `RightSync` quantify over **step indices**. Lemma 3.7's
conclusion is a deadline in **real time**, and its proof reads drone `j`'s
heading and position at the instant `t`, which is in general strictly inside a
step. The two readings are not the same, and the index one is the weaker
exactly where the lemma needs strength: a drone heading right can sit left of
its endpoint mid-step and be back inside its interval by the next event.

So this file adds the real-time layer, with no choice and no partial function:

    posIn p i s = pos_p i + sign (dir_p i) · (s − time_p)
    InStep p s  = time_p ≤ s ≤ time_{p+1}

`exists_lastBefore` (non-Zeno again) supplies a step for every instant, so
nothing is lost by never naming *the* step of `s`.

One fact carries the file. **A linear function nonnegative at both ends of an
interval is nonnegative throughout it** (`nonneg_of_endpoints`). Position, gap
and balance are all affine in time within a step, so every "it holds at the
events, therefore it holds in between" argument is that lemma with different
names substituted.

A second small tool used everywhere afterwards: **if the clock does not move
between two indices, no drone moves either** (`pos_eq_of_time_le`). Steps of
zero length are routine — an event already due costs no time — and this is what
lets index order and time order be traded against each other.

`LeftSyncAt` / `RightSyncAt` are the real-time predicates, related to the
index-shaped ones in both directions.

---

### 3.27 `Dpss/InductionStep.lean` — **B5: Lemma 3.7**

> `leftSyncAt_next` — drone `i` left synchronized from time `T`, and the pair
> `(i, i+1)` having met by then, gives drone `i+1` left synchronized from
> `T + 1/n`.

The last lemma before the assembly. Two cases, on what drone `i` is doing at
the instant `T`:

* **heading right.** Within `1/n` it is at or beyond the boundary it shares
  with `i+1` — it started at or right of its own left endpoint and that
  boundary is `1/n` further on — and ordering then carries `i+1` past its own
  left endpoint. When drone `i` finally does turn, it turns *onto* its
  neighbour (`coLocated_of_turnsLeft`), and the pivot lemma below takes over.
* **heading left.** Take the **last index at or before `T` at which the pair
  was co-located**, which exists precisely because they have met. Lemma 3.6
  says `i` has been heading left ever since, so it was at least as far right
  then as it is now, hence already left synchronized there.

The paper splits the leftward case by whether the pair is together *now*. Here
both halves are one argument, with an empty range when they are.

**The pivot.** Both branches end at the same configuration — the pair
co-located with the left drone heading left — and
`leftSync_next_of_coLocated_left` discharges it as Lemma 3.3 (the pair is
escorting) or Lemma 3.2 (it is separating), according to the right drone's
heading.

**The extra hypothesis.** The separating half needs to know the pair is on the
boundary it shares, which is `ApartOnBoundary` — *false* pointwise (§3.20) and
proved preserved by a step in §3.21. It therefore enters as a condition on the
**starting** configuration, `ApartOnBoundaries`, and is propagated along the
run. Two sufficient conditions are supplied: no two adjacent drones on the same
point, or every drone heading the same way.

---

### 3.28 `Dpss/Convergence.lean` — **B6: Theorem 2.1**

> `convergesBy (hn : 0 < n) (hi : c.Invariant) (hab : c.ApartOnBoundaries) :
>  ConvergesBy c hn`

The headline result. `Synchronization.lean` has carried the statement as a
`Prop`-valued definition since the beginning precisely so that this day could
come without a `sorry` in between; it is now a theorem.

The assembly is the paper's own three lines with the pieces named:

1. drone `0` is left synchronized always — its left endpoint is the perimeter's
   left border, which `onPerimeter_run` says nobody crosses;
2. every adjacent pair has met by time 1 — Lemma 3.5 (**B3**);
3. each drone hands left synchronization to its right-hand neighbour at a cost
   of `1/n` — Lemma 3.7 (**B5**);
4. right synchronization is left synchronization of the reflected run —
   `rightSyncAt_iff_leftSyncAt_mirror`, built on **B7**.

**The bound is exact.** Drone `i` is left synchronized at `1 + i/n` in this
development's 0-based indexing, and `i = n − 1` gives `1 + (n−1)/n = 2 − 1/n`.
Nothing is lost anywhere, which had to be so — see §3.30.

Also proved in the stronger real-time form, `sync_at_of_time`: every drone is
inside its own interval at every **instant** from `2 − 1/n` on, not merely at
the event times. That is the form the paper states.

**Not vacuous.** Three concrete configurations discharge every hypothesis and
the general theorem reproduces the conclusions their traces established by
hand — including `cfgB`, whose left pair is co-located and heading apart, so
`ApartOnBoundaries` is satisfied while *exercising* the case rather than
avoiding it.

---

### 3.29 `Dpss/ThreeConverge.lean` — **C2: three drones that settle**

§3.12 built the three-drone steady state and proved it cycles. Every trace
there starts synchronized and stays so, so nothing showed the system ever
*reaches* that state.

`cfgS` is the configuration anyone writes down first — each drone on its own
left endpoint, all heading right — and it is **not** synchronized:

    t = 0     0 →     1/3 →    2/3 →
    t = 1/3   1/3 →   2/3 →    1 ←      the right drone bounces
    t = 1/2   1/2 →   5/6 ←    5/6 ←    middle and right meet, escort back
    t = 2/3   2/3     2/3      2/3      all three at one point
    t = 1     1/3 ←   1/3 →    1 ←      = the steady state `cfgB`

Drone `0` is carried out of `[0, 1/3]` almost at once and reaches `2/3` before
anything turns it round; `cfgS_not_sync_at_start` records that the run genuinely
starts out of position. It settles at time 1 against a bound of `5/3`.

**The three-way meeting.** Step 3 is the configuration two drones cannot
produce and that the work package asked for by name — and it is where the
paper's nondeterminism is visible. The middle drone is at once co-located with
drone `0`, which is still heading right (a *meet*), and standing on the
boundary it shares with drone `2` (a *separation*). `newDir` gives separation
priority, so it turns left and takes drone `0` with it. See §3.31 for how much
of that is really a choice.

---

### 3.30 `Dpss/Sharpness.lean` — **C3: the bound is attained**

Gap 4 closed. §3.28 shows the drones are synchronized *by* `2 − 1/n`; the paper
also claims that bound is **sharp**, and nothing here checked it. One
configuration cannot: `spread` converges at `5/4` against `3/2`.

A family can. `spreadE e` is the paper's own worst case at `n = 2` — drone `0`
at the left border, drone `1` a distance `e` ahead, both heading out:

| step | time | state |
|---|---|---|
| 0 | `0` | `0 →`, `e →` |
| 1 | `1 − e` | `1−e →`, `1 ←` |
| 2 | `1 − e/2` | both at `1 − e/2 ←` |
| 3 | `3/2 − e` | both at `1/2`, separating |

Drone `0` is outside `[0, 1/2]` for the whole return leg, so at the instant
`3/2 − 2e` it sits at `1/2 + e`. Choosing `e` small pushes that instant as close
to `3/2 = 2 − 1/2` as one likes:

> `bound_sharp (B : ℝ) (hB : B < 2 − 1/2)` — some configuration satisfying
> both standing conditions has a drone outside its own interval at an instant
> at or after `B`.

Sharpness **at `n = 2`**. The paper's construction works for every `n` and the
general version needs an `n`-drone cascade, which is a much larger trace. What
this settles is the thing that matters for judging the proof: the `2 − 1/n` in
§3.28 is not slack a sharper argument could tighten.

---

### 3.31 `Dpss/Priority.lean` — **C1: measuring the nondeterminism**

§3.6 records `newDir`'s priority order — `border > separation > meet >
unchanged` — as *one resolution* of a choice the paper leaves open. This file
checks that claim by brute force: for every pair of events that can be due at
one drone at one instant, compute both answers and compare.

Seven of the eight combinations are not choices at all.

| both due | separation says | meet says | |
|---|---|---|---|
| right border + `MeetRight` | `left` | `left` | agree |
| left border + `MeetLeft` | `right` | `right` | agree |
| left border + `SepLeft` | — | — | **impossible** |
| right border + `SepRight` | — | — | **impossible** |
| `SepRight` + `MeetRight` | `left` | `left` | agree |
| `SepRight` + `MeetLeft` | `left` | `left` | agree |
| `SepLeft` + `MeetRight` | `right` | `right` | agree |
| `SepLeft` + `MeetLeft` | `right` | `left` | **differ** |

The reason the agreements happen is uniform: a separating drone is standing on
a boundary, and from a boundary the escort heading is forced.

The one disagreement is the paper's **bounce** — two drones meeting head-on
exactly on the boundary they share — and it is not a free choice either.
`newDirMeetFirst` is the alternative resolution, defined so that the comparison
is a theorem rather than an argument, and `newDirMeetFirst_leaves_interval`
shows it walks the drone off its own left endpoint. That is exactly the failure
the `n = 2` trace caught (§3.11) and the reason `AtSeparation` does not demand
that the pair be escorting.

**What is left of gap 5 is therefore not the priority order.** It is what a
*meet* is: here `MeetRight i` requires the pair to be *approaching*, so a drone
co-located with both neighbours has at most one meet due and its own heading
decides which. The paper treats meeting as positional, so a middle drone may
pair with either neighbour whatever it was doing before.

---

### 3.32 `Dpss/SharpnessGeneral.lean` — **C3′: sharp at every `n`**

Gap 9 closed. §3.30 shows the bound attained at `n = 2` by tracing four
configurations. `PLAN.md` sized the general case as the paper's `n`-drone
cascade: `2(n−1)` phases, each a configuration given by a formula in the phase
index, each needing a minimum over `Fin n` computed by hand.

**The trace is never computed.** Two observations about Lemma 3.1 replace it.

Start the drones on a **ladder** — drone `i` at `i·d`, all heading right. No
pair is co-located, so while all head right every gap stays exactly `d`. Now
suppose some drone turns left: `coLocated_of_turnsLeft` says it is co-located
with its right-hand neighbour, so its gap is zero, and the gap is `d`.
Contradiction — *unless the drone has no right-hand neighbour*. So the first
drone to turn is `n−1`, and Lemma 3.1 puts its turn at `rightEnd (n−1) = 1`.
Positions track time exactly while headings are fixed, so **nothing turns
before time `1 − (n−1)d`** (`ladder_state`).

Drone `0` therefore heads right past `1/n` until at least that time, and Lemma
3.1's other half — a leftward drone reverses only at or before its left
endpoint — sends it all the way back to `0` without stopping. It re-enters
`[0, 1/n]` only at `2w − 1/n ≥ 2 − 2(n−1)d − 1/n`, which tends to `2 − 1/n`.

> `bound_sharp_general (hn2 : 2 ≤ n) (B : ℝ) (hB : B < 2 − 1/n)` — some
> well-formed configuration has a drone outside its own interval at an instant
> at or after `B`.

At `n = 1` the statement is false and must be: a single drone's interval is the
whole perimeter, so it is synchronized from the start and `2 − 1/1 = 1` is not
attained.

---

### 3.33 `Dpss/Nondeterminism.lean` — **C1′: the relation, and its collapse**

What is left of gap 5, closed — and closed by proving the caveat away rather
than by paying for it.

`StepRel` is the step as a **relation**: fly to the next event, then let the
headings be any legitimate resolution of what is due. `IsRun` is a trajectory
of it. `LegitDir` specifies the legitimate resolutions, with the paper's own
open case left genuinely open:

> it does not specify what happens when a group of three or more drones come
> together and determine that three of them are within the middle drone's
> interval; in that case, **the middle drone can escort either neighbor to
> their common border**. — Avigad–van Doorn §2

`PLAN.md` sized this as re-proving the development over an arbitrary
trajectory. **That is not what the file does**, because the same passage of the
paper says why it is unnecessary:

> Neither of these issues bears on the results reported below, since our upper
> bound only concerns **phase 2, where these issues do not arise**.

That is a claim about reachable states, and it is provable.

**The collapse.** The two escort headings differ exactly when the meeting point
lies strictly inside the middle drone's own interval — which is precisely "three
of them are within the middle drone's interval".
`not_strictly_inside_of_grouped` shows that cannot happen. Suppose it does, at
`p` with `leftEnd i < p < rightEnd i`, no border or separation due. The pair
`(i, i+1)` is together at `p < commonEnd i`: heading apart puts them *on*
`commonEnd i` by `ApartOnBoundary`, and escorting points them at `commonEnd i`,
which is to the right — so drone `i` heads right. Then the pair `(i−1, i)` is
together at `p > commonEnd (i−1)`: heading apart puts them on `commonEnd (i−1)`,
escorting points them left, and `i−1` right with `i` left needs `i` heading
left. Every case closes.

So `legitDir_unique` — the specification has exactly **one** solution — and
`isRun_eq_run`: every trajectory of the relation *is* the run of the function.
`convergesBy_of_isRun` and `nonZeno_of_isRun` follow, and with them every
theorem in the development becomes a theorem about every resolution.

**The freedom is real off the reachable set.** `ExamplesThree.triple` is a
three-drone configuration where the middle drone is together with both
neighbours and the two escort headings genuinely differ, so `LegitDir` really is
wider than `newDir` and the collapse theorem is not vacuous.
`triple_not_reachable` then records what the collapse implies about it: the
algorithm never builds one.

---

## 4. What is **not** proved — read this part

This is the honest gap list, ordered by importance. It is much shorter than it
was; the four items that used to head it are closed, and are kept struck
through so that a reader can see what changed rather than having to diff.

1. ~~**Theorem 2.1 is not proved in general.**~~ **Closed** — §3.28.
   `convergesBy` proves it for every `n`, with the bound exactly `2 − 1/n`, and
   `sync_at_of_time` proves the stronger real-time form. Lemmas 3.1–3.7 are all
   proved; 3.2, 3.3, 3.5, 3.6 unconditionally, 3.4 conditional on the phase
   invariant which is proved preserved.

   One hypothesis beyond the standing `Invariant`: `ApartOnBoundaries` on the
   **starting** configuration — a co-located pair heading apart sits on the
   boundary it shares. §3.20 shows it is false as a pointwise fact about
   arbitrary configurations, and §3.21 proves it preserved, so it is a genuine
   condition on the start and nothing more. Any configuration with no two
   adjacent drones on one point satisfies it, as does any with all drones
   heading the same way.

2. ~~**The symmetric half is not started.**~~ **Closed** — §3.23, and used in
   §3.28. Kept as a record that it had not been counted as work: Avigad–van
   Doorn dispose of it in four words — *"by symmetry it suffices to show all
   the drones are left synchronized"* — and on paper that is honest. In Lean it
   needed a reflection map proved to commute with `advance`, `step` and `run`,
   reflection laws for every local quantity and every event, and invariance of
   the global deadline.

3. ~~**The `n = 3` work covers only the steady state.**~~ **Closed** — §3.29.
   `cfgS` starts out of position, is proved not synchronized at the start,
   passes through a genuine three-way meeting, and settles at time 1 against a
   bound of `5/3`.

4. ~~**The traces are single configurations, not the sharp worst case.**~~
   **Closed at `n = 2`** — §3.30. `bound_sharp` shows no `B < 2 − 1/n` is a
   correct bound, via an `ε`-family. The general-`n` version needs an `n`-drone
   cascade and is not done.

5. ~~**The nondeterminism is not modelled.**~~ **Closed** — §3.31 and §3.33.
   §3.31 measured the freedom: `newDir`'s priority order is forced in seven of
   its eight competing cases, and the eighth is the paper's bounce, where the
   alternative resolution provably walks a drone out of its own interval.
   §3.33 then models what remains as a **relation** — `StepRel`, admitting
   every legitimate heading update including the paper's open choice for a
   middle drone — and proves that on any configuration satisfying the standing
   conditions the choice collapses: the relation has exactly one successor, so
   every trajectory is the run, and `convergesBy_of_isRun` holds for all of
   them.

   This is what the paper itself asserts — *"our upper bound only concerns
   phase 2, where these issues do not arise"* — now proved rather than quoted.

6. **Stage 3's original headline goal is out of scope, and the plan was wrong
   to list it.** `PLAN-original.md` §5.2 proposed refuting the false `3T`
   bound. That bound is about **phase 1** — estimate propagation — which is
   Algorithm B. This development models Algorithm A, where estimates are
   correct by assumption and absent from `Config`. Unreachable here, not merely
   unfinished. Recorded as a planning error.

7. ~~**Unused definitions.**~~ **Closed** — `Config.Together` and
   `Config.Valid` are removed. A dead predicate in a development like this is
   not neutral: it invites a reader to prove something about the wrong one.

8. **Algorithm B is entirely out of scope** — wrong estimates, changing
   perimeter, drones joining or leaving. That is where the original proof broke
   and where the open problem lives.

9. ~~**Sharpness for general `n` is not checked.**~~ **Closed** — §3.32.
   `bound_sharp_general` shows no `B < 2 − 1/n` is a correct bound, for every
   `n ≥ 2`, without tracing the paper's `n`-drone cascade.

**What remains open is item 6 and item 8**: the phase-1 refutation, which is
unreachable in this scope by construction, and Algorithm B, which was never in
it. Everything the work package listed is done.

### Known modelling risks

- **Sharpness leaves no slack.** `2 − 1/n` is attained, so any analysis losing
  even an `ε` will not close.
- **Localize, don't globalize.** The ACL2 team reported that predicates defined
  over execution *history* resisted mechanization, while locally checkable
  predicates over a drone and its neighbour worked. Our `gap` / `sepRate` /
  `Escorting` are all local, which is deliberate.
- **Rationals vs reals.** ACL2 has no reals; their model is rational-valued.
  Ours is more faithful, but their termination intuitions do not transfer free.
- **The 0-based vs 1-based index shift** is a standing source of off-by-one
  errors when comparing against the paper.

---

## 5. Non-Zeno: the contribution, and it is done

I originally described Stage 1 as "most of the work and none of the glory."
That was wrong, and reading arXiv:2205.11697 in full is what corrected it.

**The ACL2 mechanization does not prove termination.** Its event-stepping
function `step-time` was admitted as a *partial* function via the `def::ung`
macro, and the assumption appears as an explicit hypothesis in the top-level
convergence theorem:

```lisp
(defthm dpss-location-convergence-after-2T-1
 (implies (and (wf-ensemble ens)
               (step-time-always-terminates))   ; admitted, never proved
          (dpss-location-convergence (step-time (- (* 2 (TEE)) (ONE)) ens))))
```

That hypothesis **is** the non-Zeno property. Avigad–van Doorn supply an
argument for it (§2 of their paper) but never mechanize it. So:

| | non-Zeno argument | mechanized |
|---|---|---|
| Avigad–van Doorn | yes | no |
| ACL2 (Greve et al.) | no (assumed) | yes |

Closing that gap is a genuine contribution rather than a reproduction, and it
stands independently of the `2 − 1/n` proof.

### ✅ Done

`Dpss/NonZenoProof.lean` proves

> `nonZeno : ∀ T : ℝ, ∃ k, T < (c.run hn k).time`

for this Lean model of Algorithm A, `sorry`-free, under the standing
`Invariant` — which §3.10 proves preserved and §3.11 proves satisfiable, so the
result is not vacuous. `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound`.

See §3.16 for the argument and a careful statement of what it does and does not
claim — in particular it does **not** literally discharge the ACL2 hypothesis,
which would require their model rather than this one.

It no longer inherits a *choice* of resolution, though: §3.33 models the step
as a relation admitting every legitimate resolution and proves the relation has
exactly one successor on any reachable configuration, so `nonZeno_of_isRun`
holds for every trajectory.

**A departure worth flagging.** I am *not* following the paper's own non-Zeno
argument. It rests on the claim that "if drone `i+1` makes two consecutive left
turns, then drone `i` must turn right in the interim", which it calls not hard
to show and does not show. I could not reconstruct it: a right turn by `i+1`
comes either from separating from `i` — at which instant `i` turns **left** —
or from meeting `i` left of their shared boundary, at which instant `i` does
not turn at all. It may still be true, but formalizing an unverified sketch is
the one move this particular project cannot afford. The route taken instead —
interval-crossing (§3.7–3.8) plus counting (§3.14–3.16) — is self-contained,
avoids the disputed claim entirely, and reuses a lemma the convergence proof
needs anyway.

The authors invite exactly this: *"given sufficient interest and resources, a
proper measure for step-time could be developed and used to dispatch this
assumption, further strengthening our results."*

---

## 6. Axiom audit — full machine output

Lean records which axioms each theorem depends on. A proof containing `sorry`
depends on `sorryAx`, and that is impossible to hide. **`sorryAx` appears zero
times below.** `propext`, `Classical.choice` and `Quot.sound` are the three
standard axioms of Lean's logic and are what ordinary mathematics uses.

<!-- BEGIN:AUDIT -->
```
'DPSS.Config.le_nextIdx' depends on axioms: [propext, Quot.sound]
'DPSS.Config.dir_left_of_apart' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.dir_right_of_apart' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.apart_zero_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.dt_eq_zero_of_pinned' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.bothLeft_pinned_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.balance_nonneg_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pairPhase_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pairPhase_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.balanceNonneg_of_pairPhase' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pairPhase_of_atSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pairPhase_of_escorting_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftSync_of_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftSync_of_escorting' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftSync_of_reached_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Dir.flip_left' does not depend on any axioms
'DPSS.Dir.flip_right' does not depend on any axioms
'DPSS.Dir.flip_flip' does not depend on any axioms
'DPSS.Dir.sign_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Dir.sign_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Dir.sign_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Dir.sign_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Dir.eq_left_or_right' depends on axioms: [propext]
'DPSS.Dir.sign_flip' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.rightEnd_sub_leftEnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.leftEnd_lt_rightEnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.rightEnd_eq_leftEnd_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.leftEnd_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.rightEnd_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.leftEnd_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.rightEnd_last' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.ext' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.separationTime_advance' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.gap_advance_of_dir_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.sepTime_nonneg_left_border' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.sepTime_nonneg_right_border' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.sepTime_eq_zero_at_commonEnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.sepTime_nonneg_at_leftEnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.sepTime_nonneg_of_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.sepTime_nonneg_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.commonEnd_lt_commonEnd_next' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftEnd_next_eq_commonEnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.droneNextTime_le_separationTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.commonEnd_le_pos_of_both_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.escortsCoherent_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.invariant_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.invariant_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.onPerimeter_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.ordered_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.time_mono_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.convergesBy_of_one'' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.posIn_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.inStep_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.rightSyncAt_iff_leftSyncAt_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.apartOnBoundaries_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftSyncAt_index' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftSyncAt_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.rightSyncAt_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.sync_at_of_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.convergesBy' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.allSync_of_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.convergesBy_of_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.convergesBy_of_dir_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.approach_apartOnBoundaries' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.approach_converges_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spread_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spread_converges_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgB_apartOnBoundaries' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgB_converges_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.hn4' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.h12' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.nextIdx_f1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.cascade_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.cascade_dir_f0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.cascade_dir_f1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.cascade_dir_f2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.cascade_dir_f3' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.leftEnd_f1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.commonEnd_f0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.commonEnd_f1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.commonEnd_f2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.cascade_coLocated' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.cascade_not_on_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.cascade_meetLeft_f1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.cascade_meetRight_f2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.cascade_newDir_f1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.cascade_newDir_f2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.apart_off_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Counterexample.not_forall_apart_implies_on_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.advance_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.advance_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.advance_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.advance_zero_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.advance_advance_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.nextIdx_val' does not depend on any axioms
'DPSS.Config.sepRate_advance' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.gap_advance' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.sepRate_of_approaching' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.sepRate_nonneg_of_not_approaching' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.gap_eq_zero_at_meetTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.gap_pos_before_meetTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.meetTime_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.gap_nonneg_advance' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.ordered_of_adjOrdered' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.ordered_advance' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.setDir_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.setDir_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.setDir_dir_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.setDir_dir_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.gap_setDir' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.nextIdx_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.doMeet_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.doSeparate_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.doBorder_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.adjOrdered_doMeet' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.adjOrdered_doSeparate' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.adjOrdered_doBorder' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.escorting_doMeet' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.doMeet_dir_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.doMeet_dir_next' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.doSeparate_dir_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.doSeparate_dir_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.not_approaching_doSeparate' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.doBorder_dir_of_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.doBorder_dir_of_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.sepRate_eq_zero_of_escorting' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.coLocated_advance_of_escorting' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.someDroneTurns_of_atLeftBorder' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.not_atLeftBorder_of_atRightBorder' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.someDroneTurns_of_atRightBorder' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.someDroneTurns_of_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.escortDirLeft_next_eq_escortDir' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.prevIdx_nextIdx' depends on axioms: [propext, Quot.sound]
'DPSS.Config.someDroneTurns_of_meet_due' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.atBorder_of_advance_borderTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.someDroneTurns_of_border_deadline' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.meet_due_of_meet_deadline' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.separation_due_of_separation_deadline' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.someDroneTurns_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.someDroneTurns_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.exists_dir_right_of_dir_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.exists_dir_left_of_dir_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.exists_turn' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.time_bound_of_dir_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.time_bound_of_dir_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.d0_next' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.commonEnd_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.leftEnd_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.bounce_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.bounce_dir_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.bounce_dir_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.bounce_h' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.bounce_coLocated' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.bounce_atSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.bounce_approaching' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.bounce_newDir_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.bounce_newDir_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.bounce_separates' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.fin2_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.approach_pos_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.approach_pos_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.approach_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.hn2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.timeToNextEvent_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.droneNextTime_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.droneNextTime_d0_approaching' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.droneNextTime_d0_apart' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.nextIdx_d0_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.atBoundary_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.atBoundary_dir_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.atBoundary_dir_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.atEnds_pos_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.atEnds_pos_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.atEnds_dir_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.atEnds_dir_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.atBoundary_timeToNext' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.atEnds_timeToNext' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.step_atBoundary' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.step_atEnds' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.approach_timeToNext' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.step_approach' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.leftEnd_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.rightEnd_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.rightEnd_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.run_approach' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.approach_pos_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.approach_allSync' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.approach_converges' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.approach_period' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spread_pos_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spread_pos_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spread_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.chase_pos_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.chase_pos_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.chase_dir_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.chase_dir_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.escortBack_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.escortBack_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spread_timeToNext' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.chase_timeToNext' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.escortBack_timeToNext' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.not_sepRight_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.not_meetRight_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.not_sepLeft_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.not_meetLeft_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.newDir_d0_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.step_spread' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.step_chase' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.step_escortBack' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.run_spread_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.run_spread_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.run_spread_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.run_spread' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spread_not_allSync_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spread_pos_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spread_allSync_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spread_sync_within_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spread_converges' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.hn3' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.h01' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.h12' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.nextIdx_e0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.nextIdx_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.fin3_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.leftEnd_e0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.rightEnd_e0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.leftEnd_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.rightEnd_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.leftEnd_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.rightEnd_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.commonEnd_e0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.commonEnd_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.timeToNextEvent_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.droneNextTime_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.droneNextTime_apart' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.droneNextTime_approaching' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.not_sepRight_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.not_meetRight_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.not_sepLeft_e0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.not_meetLeft_e0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgB_pos_e0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgB_pos_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgB_pos_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgB_dir_e0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgB_dir_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgB_dir_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgC_pos_e0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgC_pos_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgC_pos_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgC_dir_e0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgC_dir_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgC_dir_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgB_timeToNext' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgC_timeToNext' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.prevIdx_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.prevIdx_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.step_cfgB' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.step_cfgC' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.run_cfgB' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgB_in_intervals' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgB_allSync' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgB_converges' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgB_period' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgB_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.exists_greatest_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.apartOnBoundaries_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.apartOnBoundaries_of_not_coLocated' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.apartOnBoundaries_of_dir_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftSync_next_of_coLocated_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftSyncAt_next' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Dir.isign_left' does not depend on any axioms
'DPSS.Dir.isign_right' does not depend on any axioms
'DPSS.Dir.cast_isign' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Dir.isign_mul_self' does not depend on any axioms
'DPSS.Dir.isign_ne_zero' does not depend on any axioms
'DPSS.intRightEnd_sub_intLeftEnd' depends on axioms: [propext]
'DPSS.IntConfig.ext' depends on axioms: [propext]
'DPSS.IntConfig.advance_time' does not depend on any axioms
'DPSS.IntConfig.advance_pos' does not depend on any axioms
'DPSS.IntConfig.advance_dir' does not depend on any axioms
'DPSS.IntConfig.step_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.step_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.run_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.run_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.gap_advance' depends on axioms: [propext, Quot.sound]
'DPSS.IntConfig.two_dvd_sepRate' depends on axioms: [propext]
'DPSS.IntConfig.onLattice_advance' depends on axioms: [propext, Quot.sound]
'DPSS.IntConfig.onLattice_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.onLattice_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.two_mul_meetTime' depends on axioms: [propext, Quot.sound]
'DPSS.scaleR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.scaleR_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.div_eq_div_iff_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.div_lt_div_iff_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.div_le_div_iff_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_leftEnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_rightEnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_commonEnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_sign' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_coLocated' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_approaching' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_escorting' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_atSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_atLeftBorder' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_atRightBorder' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.cast_min_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_borderTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_separationTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_meetTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_droneNextTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_timeToNextEvent' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_escortDir' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_escortDirLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_sepRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_sepLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_meetRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_meetLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_newDir' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_advance' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.embed_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntConfig.intRun_converges' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntExamples.hn3' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntExamples.cfgSI_onLattice' depends on axioms: [propext, Quot.sound]
'DPSS.IntExamples.cfgSI_run_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntExamples.cfgSI_run_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntExamples.cfgSI_run_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntExamples.cfgSI_run_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.IntExamples.cfgSI_lattice_at_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pairBalance_nonneg_of_escorting_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pairBalance_nonneg_of_pos_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftSync_of_escorting_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftSync_of_pos_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftSync_of_atSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.timeToNextEvent_eq_zero_of_pinned' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pairBalance_step_of_time_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pairBalance_nonneg_step_of_pinned' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.haveMetBy_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.haveMetBy_of_start' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.haveMetBy_of_meet_deadline' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.dir_right_of_no_turnsLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.dir_left_of_no_turnsRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.not_turnsRightAt_of_never_coLocated' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.gap_of_approaching' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.exists_coLocated_of_approaching' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.exists_firstRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.exists_firstLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.gap_sub_eq_of_dirsConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.gap_of_separating' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.gap_of_parallel' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.exists_coLocated_within_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.haveMetBy_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.mirrorIdx_val' depends on axioms: [propext, Quot.sound]
'DPSS.mirrorIdx_mirrorIdx' depends on axioms: [propext, Quot.sound]
'DPSS.mirrorIdx_le_mirrorIdx' depends on axioms: [propext, Quot.sound]
'DPSS.cast_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.leftEnd_mirrorIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.rightEnd_mirrorIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.mirror_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.mirror_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.mirror_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.mirror_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.onPerimeter_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.ordered_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftEnd_le_mirror_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.mirror_pos_le_rightEnd_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.mirrorIdx_pos' depends on axioms: [propext, Quot.sound]
'DPSS.Config.mirrorIdx_lt' depends on axioms: [propext, Quot.sound]
'DPSS.Config.mirror_next_lt' depends on axioms: [propext, Quot.sound]
'DPSS.Config.nextIdx_mirrorIdx_next' depends on axioms: [propext, Quot.sound]
'DPSS.Config.gap_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.sepRate_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.coLocated_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.approaching_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.escorting_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.flip_eq_left_iff' depends on axioms: [propext]
'DPSS.Config.flip_eq_right_iff' depends on axioms: [propext]
'DPSS.Config.atLeftBorder_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.atRightBorder_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.borderTime_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.meetTime_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.separationTime_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.gap_mirror_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.approaching_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.escorting_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.coLocated_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.atSeparation_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.mirror_pair_idx' depends on axioms: [propext, Quot.sound]
'DPSS.Config.approaching_mirror_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.escorting_mirror_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.meetTime_mirror_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.separationTime_mirror_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.timeToNextEvent_mirror_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.timeToNextEvent_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.mirrorIdx_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.prevIdx_mirrorIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.atSeparation_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.sepRight_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.meetRight_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.sepLeft_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.meetLeft_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.escortDir_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.escortDirLeft_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.not_sepLeft_of_sepRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.not_meetLeft_of_meetRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_ne_commonEnd_of_meetRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_ne_leftEnd_of_meetLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.newDir_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.advance_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.step_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.run_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.rightSync_iff_leftSync_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.invariant_mirror' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.borderTime_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.borderTime_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.separationTime_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.separationTime_pos_of_escorting' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.meetTime_pos_of_approaching' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.droneNextTime_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.univ_fin_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.borderTime_of_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.borderTime_of_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.droneNextTime_le_borderTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.droneNextTime_le_meetTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.droneNextTime_le_borderTime_of_next_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.droneNextTime_le_borderTime_of_self_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.meetTime_le_borderTime_of_approaching' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.timeToNextEvent_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.timeToNextEvent_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.timeToNextEvent_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.step_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.advance_newDir_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_le_leftEnd_of_turnsRightAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.rightEnd_le_pos_of_turnsLeftAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_sub_eq_of_dirConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.time_advance_of_crossing' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.time_advance_of_crossing_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.run_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.time_mono_run'' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.exists_first_turn_after' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.time_advance_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.nonZeno' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.groupedRight_of_meetRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.groupedLeft_of_meetLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.legitDir_newDir' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.not_strictly_inside_of_grouped' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.escortDir_eq_escortDirLeft_of_grouped' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.legitDir_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.stepRel_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.escortsCoherent_advance' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.invariant_advance' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.apartOnBoundaries_advance' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.stepRel_eq_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.isRun_eq_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.convergesBy_of_isRun' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.nonZeno_of_isRun' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.triple_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.triple_dir_e0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.triple_dir_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.triple_dir_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.triple_ambiguous' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.triple_not_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pairBalance_advance' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pairBalance_advance_of_opposite' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pairBalance_eq_zero_of_atSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.commonEnd_le_pos_of_coLocated' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pairBalance_neg_of_coLocated_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftEnd_le_pos_of_pairBalance' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pairBalance_eq_two_mul_separationTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pairBalance_nonneg_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.coLocated_of_turnsLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.not_bothLeftApart_of_turnsLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.coLocated_of_turnsRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.coLocated_step_of_both_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_eq_leftEnd_of_turnsRightAt_of_leftSync' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_eq_rightEnd_of_turnsLeftAt_of_rightSync' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.rightEnd_next_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftEnd_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_next_le_rightEnd_of_balance_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pinned_of_balance_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.balanceNonneg_of_never_bothLeftApart' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftSync_of_balanceNonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.newDir_left_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.newDir_right_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_eq_commonEnd_of_sepRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_eq_commonEnd_of_sepLeft_next' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.meeting_pair_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.not_sepLeft_of_atLeftBorder' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.not_sepRight_of_atRightBorder' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.escortDir_eq_left_of_atRightBorder' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.escortDirLeft_eq_right_of_atLeftBorder' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.escortDir_eq_left_of_sepRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.escortDirLeft_eq_left_of_sepRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.escortDir_eq_right_of_sepLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.escortDirLeft_eq_left_of_sepLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.newDirMeetFirst_eq_newDir' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.newDirMeetFirst_of_bounce' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.newDirMeetFirst_leaves_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.apart_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.not_apart_of_meet' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.dir_left_of_newDir_apart' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.dir_right_of_newDir_apart' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.apartOnBoundary_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.nonneg_of_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.inStep_start' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.inStep_end' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.time_succ_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_succ_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.posIn_start' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.posIn_end' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_succ_eq'' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.le_posIn' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.posIn_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.posIn_le_posIn_next' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.exists_lastBefore' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_eq_of_time_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.gap_eq_of_time_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.coLocated_of_time_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftSyncAt_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.rightSyncAt_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftSync_of_leftSyncAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.rightSync_of_rightSyncAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftSyncAt_of_leftSync' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.rightSyncAt_of_rightSync' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftSyncAt_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_eq_zero_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_eq_one_of_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.coLocated_of_atLeftBorder' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_eq_commonEnd_at_separationTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.atSeparation_at_separationTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.atLeftBorder_at_leftBorderTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.atRightBorder_at_rightBorderTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.coLocated_at_meetTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftBorderTime_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.rightBorderTime_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftBorderTime_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.rightBorderTime_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.meetTime_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.separationTime_nonneg_doMeet' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.separationTime_pos_doMeet' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spreadE_pos_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spreadE_pos_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spreadE_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spreadE_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.chaseE_pos_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.chaseE_pos_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.chaseE_dir_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.chaseE_dir_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.chaseE_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.escortE_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.escortE_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.escortE_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spreadE_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spreadE_apartOnBoundaries' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spreadE_timeToNext' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.chaseE_timeToNext' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.escortE_timeToNext' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.step_spreadE' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.step_chaseE' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.step_escortE' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.run_spreadE_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.run_spreadE_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.run_spreadE_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.spreadE_outside' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Examples.bound_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.ladder_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.ladder_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.ladder_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.ladder_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.ladder_apartOnBoundaries' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.ladder_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.ladder_state' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.ladder_outside' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.bound_sharp_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.prevIdx_val' depends on axioms: [propext, Quot.sound]
'DPSS.Config.prevIdx_lt' depends on axioms: [propext, Quot.sound]
'DPSS.Config.nextIdx_prevIdx' depends on axioms: [propext, Quot.sound]
'DPSS.Config.newDir_of_noEvent' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.newDir_atLeftBorder' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.newDir_atRightBorder' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.newDir_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.step_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.step_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.step_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.timeToNextEvent_le_meetTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.adjOrdered_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.ordered_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.step_time_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.step_time_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.run_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.run_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.onPerimeter_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftSync_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.rightSync_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.sync_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.leftEnd_eq_zero_of_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.rightEnd_eq_one_of_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.sync_of_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.convergesBy_of_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS_pos_e0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS_pos_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS_pos_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS1_pos_e0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS1_pos_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS1_pos_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS1_dir_e0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS1_dir_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS1_dir_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS2_pos_e0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS2_pos_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS2_pos_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS2_dir_e0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS2_dir_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS2_dir_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS3_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS3_dir_e0' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS3_dir_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS3_dir_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS_apartOnBoundaries' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS_timeToNext' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.step_cfgS' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS1_timeToNext' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.step_cfgS1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS2_timeToNext' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.step_cfgS2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS3_timeToNext' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.step_cfgS3' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.run_cfgS_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.run_cfgS_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.run_cfgS_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.run_cfgS_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS_three_way_meeting' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS_not_sync_at_start' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.run_cfgB_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS_in_intervals' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS_allSync' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS_within_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.ExamplesThree.cfgS_converges' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.not_turnsLeftAt_of_never_coLocated' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.dir_left_of_no_turnsLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.dir_left_since_of_never_coLocated' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.dir_const_of_no_turns' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.time_gap_of_consecutive_turns' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.not_meetLeft_of_dir_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.not_meetRight_of_dir_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_eq_leftEnd_of_sepLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_eq_rightEnd_of_sepRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.rightEnd_le_pos_of_turnsLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_le_leftEnd_of_turnsRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.turn_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**658/658 clean — `sorryAx` appears zero times.**
<!-- END:AUDIT -->

---

## 7. How to verify this yourself

```bash
cd ~/dpss_lean
export PATH="$HOME/.elan/bin:$PATH"

# 1. Does it build clean? Expect exit 0 and no error output.
lake build && echo OK

# 2. Is there a `sorry` anywhere in the sources?
grep -rn "sorry" Dpss/          # expect: no matches

# 3. Regenerate the axiom audit in §6 from scratch.
python3 scripts/audit.py        # expect: "PASS: no theorem depends on sorryAx."
```

This also runs in CI on every push (`.github/workflows/lean_action_ci.yml`), so
a `sorry` cannot enter the repository unnoticed rather than merely being absent
today.

`scripts/refresh_status.py` regenerates the machine-generated blocks of *this
document* (§6, §8, the header, the theorem count) from the live repository, so
the numbers here cannot quietly drift away from the code. If you suspect this
file is stale, run it.

`scripts/audit.py` is committed alongside the sources. It extracts every
theorem name from `Dpss/*.lean` (tracking namespaces), asks Lean for each one's
axiom dependencies, and exits nonzero if any depends on `sorryAx`. It is the
same script that produced §6, so if §6 ever disagrees with a fresh run, trust
the fresh run and tell me.

**What the audit does and does not tell you.** It proves the *proofs* are
complete — no gaps, no assumptions smuggled in. It says nothing about whether
the *definitions* faithfully model DPSS. A perfect proof about a wrong model is
worthless, which is why Stage 3 (running the model at `n = 2, 3` and refuting
the known-false phase-1 bound) exists, and why it comes before Stage 4. Right
now the honest summary is: **the proofs are airtight and the model is largely
untested.** §4 item 4 is the one to watch.

---

## 8. Commit history

<!-- BEGIN:COMMITS -->
```
d42b170  2026-09-12  fix: the deep-link generator lost seventeen links to IntModel's twins
c8dc116  2026-09-12  docs: commit the E1 build plan, as a living document
8fcf4cb  2026-09-12  feat: M0 -- the Verus toolchain, pinned, plus M1's integer model
38aeffb  2026-09-12  docs: the last two sentences that still described closed work as open
fcd0d2f  2026-09-12  chore: bring the whole repo up to current status, and fix a red CI step
9027985  2026-09-12  docs: refresh STATUS.md generated blocks
f757d92  2026-09-12  docs: GUIDE.md covers the whole work package, with deep links
d7bef14  2026-09-12  docs: check the C and D group rows too
588a976  2026-09-12  docs: GUIDE and CHANGELOG catch up with the closed work package
f572c5b  2026-09-12  docs: the record catches up with C3' and C1'
ff6a26c  2026-09-12  feat: C1' -- the nondeterminism, as a relation, proved to collapse
e97593b  2026-09-12  feat: C3' -- the bound is attained for every n, with no cascade traced
e2ad74f  2026-09-12  docs: CHANGELOG.md -- the account you want after a git pull
be1079a  2026-09-12  docs: GUIDE.md -- how to follow the convergence proof
0ae43be  2026-09-12  docs: the record catches up with the proofs
e969f31  2026-09-12  feat: C1 -- measuring the nondeterminism instead of assuming it
8fe6e93  2026-09-12  feat: C2 -- three drones that start out of position and settle
b48f409  2026-09-12  feat: C3 -- the 2 - 1/n bound is attained, not merely proved
9c2214d  2026-09-12  refactor: D1 -- remove two superseded definitions
7753781  2026-09-12  feat: B6 -- Theorem 2.1, the 2 - 1/n bound, proved
5816c6a  2026-09-12  feat: B5 complete -- Lemma 3.7, the +1/n inductive step
20c9295  2026-09-12  feat: reading the system between events (B5, part 1)
cb2b7ac  2026-09-12  feat: B3 complete -- Lemma 3.5, every pair meets within time 1
5ec2469  2026-09-12  feat: how a gap evolves under fixed headings (B3, part 3)
148a893  2026-09-12  feat: the first turn, timed exactly (B3, part 2)
a80cdee  2026-09-12  feat: an approaching pair meets, within half its gap (B3, part 1)
87463f2  2026-09-12  feat: B1 complete -- Lemma 3.2, unconditional
d7a7147  2026-09-12  docs: refresh STATUS.md generated blocks
56882f2  2026-09-12  docs: PLAN.md records what each completed item built and taught
b91c5a2  2026-09-12  docs: PLAN.md is now the roadmap of work yet to be done
e36d467  2026-09-12  docs: derive B1's invariant instead of guessing at it
239b599  2026-09-12  feat: ApartOnBoundary is preserved by a step
4a98d33  2026-09-12  feat: B7 complete -- "by symmetry" made honest
57dd848  2026-09-12  feat: escort headings under reflection, and the tie-break that nearly bites
0aa2894  2026-09-12  feat: events swap under reflection (B7, part 2c)
9cdd781  2026-09-12  feat: the global deadline is invariant under reflection (B7, part 2b)
97067a2  2026-09-12  feat: reflected quantities and events (B7, part 2a)
92eb248  2026-09-12  feat: the perimeter reflected (B7, part 1)
28d112c  2026-09-12  feat: every drone eventually turns, and how soon
d0aaa02  2026-09-12  docs: record the symmetric half as a work item -- I had not counted it
49bac2d  2026-09-12  feat: the invariant the counterexample called for
eb396c4  2026-09-12  docs: actually fix the stale gap cross-references
2edf1c0  2026-09-12  docs: fix stale gap cross-references in the work package
5c128c2  2026-09-12  feat: a counterexample -- the lemma I was trying to prove is false
37a7159  2026-09-12  feat: why a drone ends up heading where it does
2e8b565  2026-09-12  feat: Lemma 3.6, unconditionally
0573e4d  2026-09-12  feat: a pinned left-synchronized drone freezes the clock
9cc4325  2026-09-12  feat: Lemmas 3.3 and 3.4, and the have-met predicate
dbf6c44  2026-09-12  feat: the positional core of Lemma 3.2's last case
55f60de  2026-09-12  docs: capture the key insights durably
4d9e80d  2026-09-12  feat: two of the three routes to Lemma 3.2's obstruction are closed
2db5f0b  2026-09-12  docs: record non-Zeno as done in section 5
c920cb3  2026-09-12  feat: non-Zeno, proved
80c4490  2026-09-12  feat: A3 -- consecutive turns of one drone are 1/n apart in time
fdb7427  2026-09-12  feat: A1 + A2 complete -- every step turns a drone, unconditionally
fe8a002  2026-09-12  feat: border deadlines are never spurious -- gap 2 was overstated
b3b3663  2026-09-12  feat: A1 -- every scheduled event turns a drone
e0f35b6  2026-09-12  feat: Lemma 3.2 reduced to a single configuration class
69e6577  2026-09-12  feat: the pair balance -- Lemma 3.2, modulo one invariance
4c4fe2d  2026-09-12  feat: three drones -- the first case where the middle-drone machinery runs
f268410  2026-09-12  feat: a converging n = 2 trace, checked against the paper's bound
f551b06  2026-09-12  feat: a complete n = 2 trace -- synchronized forever, period 1
00d447f  2026-09-12  fix: bounce events sent a drone out of its own interval
05f29ef  2026-09-12  feat: escorts stay coherent -- the last assumption discharged
f2d3eca  2026-09-12  docs: bring STATUS.md up to date, and guard it against silent edit failures
9f72d4c  2026-09-12  feat: Stage 2 -- synchronization defined, Theorem 2.1 stated
beb1ee8  2026-09-12  feat: crossing an interval costs at least 1/n of time
8213bd8  2026-09-12  feat: Lemma 3.1 -- where a drone is allowed to turn
f07504a  2026-09-12  feat: step function and runs
27bfd34  2026-09-12  docs: repair STATUS.md gap list, which the previous commit did not update
d9e7f2f  2026-09-12  feat: spurious border deadlines are dominated (and Lean caught a false lemma)
b7f4b0f  2026-09-12  feat: time to the next event, proved strictly positive
c12ef57  2026-09-12  feat: event scheduling, and make the status report self-refreshing
bc5bef8  2026-09-12  feat: the three DPSS events, plus an auditable status report
b5de469  2026-09-12  feat: motion between events, and the ordering invariant
fbeab29  2026-09-12  docs: ACL2 convergence proof is conditional on unproved termination
29d8b41  2026-09-12  feat: scaffold Lean 4 + Mathlib project and add the geometry layer
c4b40fd  2026-09-12  docs: verify brief against arXiv:2008.04262, fix one error, add Theorem 2.2
0d789d5  2026-09-12  docs: add Lean formalization plan for DPSS Algorithm A
0dc5ffd  2026-09-11  Add files via upload
bcdb11f  2026-09-11  Create README.md
971617b  2026-09-11  Initial commit
```
<!-- END:COMMITS -->

---

## 8a. B1, derived rather than guessed

I reached for three invariants before deriving the right one, and two were
wrong. Writing the derivation down so the fourth attempt is not a fourth guess.

### What has to be proved

`BalanceNonneg` — the pair's balance never goes negative — because
`leftSync_of_balanceNonneg` turns that into Lemma 3.2, and §3.17 turns Lemma
3.2 into 3.3 and 3.4 as well.

### Why the earlier attempts failed

1. *"A co-located pair heading apart is on its boundary"*, pointwise. **False**
   — §3.20 builds the counterexample.
2. `ApartOnBoundary`, the same statement as a run invariant. **True and proved**
   (§3.21), but it is conditioned on **co-location**, and the case that blocks
   Lemma 3.2 is the one where the pair is **apart**. Right theorem, wrong shape.

### The invariant

Three conjuncts, each earning its place:

| | Clause | Why |
|---|---|---|
| **(i)** | `0 ≤ balance` | what `leftSync_of_balanceNonneg` consumes |
| **(ii)** | pair heading `(left, right)` ⟹ `balance = 0` | supplies (i) when the pair separates, and drives the pinning argument |
| **(iii)** | `BothLeftApart` ⟹ `pos i = leftEnd i` | the only configuration that can drive the balance down |

### Why each clause is preserved

**(ii).** While the pair heads `(left, right)` the balance rate is
`sign(left) + sign(right) = 0`, so it is **constant** — note this is the *sum*,
unlike the gap, which uses the difference and grows at rate 2. So it suffices
that the pair can only *enter* that state with balance zero. Two cases:

- **Pair apart.** Then every event that could deliver `left` to one and `right`
  to the other is excluded, because each of `SepRight`, `MeetRight`,
  `SepLeft(next)`, `MeetLeft(next)` needs this pair co-located, and either
  border event forces co-location by ordering. So the pair was *already*
  `(left, right)` and the balance carries over.
- **Pair co-located.** Either a separation fired — which zeroes the balance
  outright — or, by §3.21's enumeration, the pair was already heading apart.

**(iii).** If the pair is `(left, left)` and apart, the preceding state was
`(left, right)`, so by (ii) the balance was zero; the positional core
(`pinned_of_balance_zero`, §3.13) then pins the left drone to `leftEnd i`.

**(i).** Falls out. The balance only decreases when both head left. Co-located,
that is an escort and the scheduler stops it exactly at zero
(`pairBalance_nonneg_step`). Apart, clause (iii) pins the left drone at its
left endpoint, where left synchronization freezes the clock
(`timeToNextEvent_eq_zero_of_pinned`) — so the balance does not move at all.

### What is already built

`pairBalance_advance`, `pairBalance_eq_zero_of_atSeparation`,
`pairBalance_eq_two_mul_separationTime`, `pairBalance_nonneg_step`,
`pinned_of_balance_zero`, `timeToNextEvent_eq_zero_of_pinned`,
`apart_transfer`, `coLocated_of_turnsLeft` / `_turnsRight`,
`newDir_left_cases` / `_right_cases`, `dir_left_of_newDir_apart` and its
partner. **Every ingredient above exists.** What is missing is the statement of
the three-clause invariant and its preservation proof, assembled from them.

---

## 9. The work package

> **The actionable roadmap lives in `PLAN.md`.** The table below is the
> summary.

**The work package is complete.** Every item is done, including the two that
were re-sized along the way.

| # | Item | Size | Notes |
|---|---|---|---|
| **A** | ~~**Non-Zeno**~~ | ✅ | the contribution ACL2 had to assume |
| A1 | ~~Every event turns at least one drone~~ | ✅ | `someDroneTurns_step`, unconditional |
| A2 | ~~The minimum is attained by a genuine event~~ | ✅ | folded into A1; gap 2 closed |
| A3 | ~~Consecutive turns `1/n` apart~~ | ✅ | §3.15 |
| A4 | ~~Assemble `NonZeno`~~ | ✅ | §3.16 |
| **B** | ~~**Theorem 2.1**~~ | ✅ | **the headline, and it is proved** |
| B1 | ~~Lemma 3.2~~ | ✅ | §3.24 — `leftSync_of_separation`, unconditional |
| B2 | ~~Lemmas 3.3, 3.4~~ | ✅ | §3.17, §3.24 |
| B3 | ~~Lemma 3.5~~ | ✅ | §3.25 — `exists_coLocated_within_one` |
| B4 | ~~Lemma 3.6 — turn persistence~~ | ✅ | §3.18, unconditional |
| B5 | ~~Lemma 3.7 — the `+1/n` inductive step~~ | ✅ | §3.27 — `leftSyncAt_next`, on the real-time layer §3.26 |
| **B6** | ~~Assemble `2 − 1/n`~~ | ✅ | **§3.28 — `convergesBy`** |
| B7 | ~~The symmetric half~~ | ✅ | §3.23 — `rightSync_iff_leftSync_mirror` |
| **C** | ~~**Fidelity**~~ | ✅ | every departure from the paper's model, closed |
| C1 | ~~Nondeterminism: measure it~~ | ✅ | §3.31 — the priority order is forced in 7 of 8 cases |
| **C1′** | ~~Nondeterminism: `step` as a **relation**~~ | ✅ | **§3.33 — `convergesBy_of_isRun`.** The relation collapses to the function on reachable states |
| C2 | ~~Converging `n = 3` trace; a genuine three-way meeting~~ | ✅ | §3.29 |
| C3 | ~~An `ε`-family showing the bound is *attained*~~ | ✅ | §3.30, at `n = 2` |
| **C3′** | ~~Sharpness for general `n`~~ | ✅ | **§3.32 — `bound_sharp_general`**, with no cascade traced |
| **D** | ~~**Cleanup**~~ | ✅ | complete |
| D1 | ~~Remove unused definitions~~ | ✅ | `Config.Together`, `Config.Valid` gone |
| D2 | ~~Make `HaveMetBy` locally checkable~~ | ✅ | **not needed** — B3 and B5 both went through with the history-shaped definition; see below |

Sizes are relative: **S** is a sitting, **M** is a session, **L** is the kind of
argument the paper spends a figure on and the ACL2 team spent 11K lines around.

### Two items that were re-sized, and then shrank again

**C1′ was listed as `M`, re-sized to `L`, and closed in a sitting.** The `L`
estimate was for the obvious route — make `step` a relation and re-prove the
development over an arbitrary trajectory, which reaches every file. What made
that unnecessary was re-reading the paper: the passage that flags the ambiguity
ends *"Neither of these issues bears on the results reported below, since our
upper bound only concerns phase 2, where these issues do not arise."* That is a
claim about reachable states, and proving it (§3.33) collapses the relation to
the function instead of carrying it through 31 files.

**C3′ was listed as `M` for an `n`-drone cascade** and closed without tracing
one (§3.32). Both re-sizings came from looking for the argument rather than
from executing the plan, which is the general lesson recorded in `INSIGHTS.md`
§17.

### D2, resolved by not doing it

The ACL2 team reported that `have-met` phrased over execution *history* "drew
heavily on human intuition about system behaviour and was difficult to work
with in a mechanized proof", and that recasting it as a **locally checkable**
predicate over a drone and its immediate neighbour was what made their
development tractable. `HaveMetBy` here is the history-shaped one, and D2 was
carried as a contingency in case Lemma 3.5 or 3.7 became unwieldy.

Neither did. Lemma 3.5 produces the meeting index directly, and Lemma 3.7
consumes it by taking the **last** co-located index at or before the deadline —
which is a search over history, and a two-line one. The contingency is closed
as unnecessary, which is worth recording precisely because the ACL2 experience
predicted otherwise: what made history painful for them was presumably ACL2's
untyped first-order setting, not the shape of the predicate.

