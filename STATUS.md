# DPSS formalization — status

<!-- BEGIN:META -->
**Generated:** 2026-09-12  
**Commit at time of writing:** `37a715921f2f`  
**Toolchain:** Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release), Mathlib v4.33.1
<!-- END:META -->

> **Companion:** `INSIGHTS.md` records the non-obvious things this project
> taught us — the bug a concrete trace caught that 145 theorems missed, why the
> non-Zeno proof departs from the paper's, and the Lean mechanics that cost
> real time. Read it before extending the work.

This document is written to be *audited*, not just read. Every claim about what
is proved is backed by machine output reproduced verbatim in §6, and §7 tells
you how to regenerate it yourself. §4 is the part to read if you want to know
what is **not** done — it is deliberately longer than §3.

---

## 1. Scope, as agreed

| Decision | Choice |
|---|---|
| How far | Stages 0–3 committed; the `2 − 1/n` proof itself is a stretch goal |
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
| 3 | Sanity tests at `n = 2, 3` | both traced; the phase-1 refutation is out of scope, see gap 6 |
| 4 | Close the `2 − 1/n` proof | Lemma 3.1 done; 3.2–3.8 not started |
| 5 | Phase-1 upper bound (open problem) | explicitly out of scope |

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

---

## 3. What is actually proved

<!-- BEGIN:COUNTS -->
**345 theorems**, all `sorry`-free, across 20 files (`Basic.lean` 218 lines, `Coherence.lean` 386 lines, `Counterexample.lean` 170 lines, `Dynamics.lean` 228 lines, `Events.lean` 246 lines, `EventsTurn.lean` 319 lines, `Examples.lean` 805 lines, `ExamplesThree.lean` 375 lines, `LeftSyncLemmas.lean` 224 lines, `NextEvent.lean` 315 lines, `NonZeno.lean` 143 lines, `NonZenoProof.lean` 160 lines, `PairBalance.lean` 468 lines, `PhaseInvariant.lean` 123 lines, `Schedule.lean` 214 lines, `Step.lean` 239 lines, `Synchronization.lean` 161 lines, `TurnPersistence.lean` 99 lines, `TurnSpacing.lean` 116 lines, `Turning.lean` 180 lines).
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
separation priority is one resolution. See gap 7.

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

---

## 4. What is **not** proved — read this part

This is the honest gap list, ordered by importance.

1. **Theorem 2.1 is not proved in general** — only at `n = 1`, and for specific
   `n = 2` and `n = 3` configurations. Lemma 3.1 is done and **Lemma 3.2 is
   half done** (§3.13: everything but ruling out `BothLeftApart`). **Lemmas 3.3
   through 3.8 are untouched.** Lemma 3.5 in particular ("every adjacent pair
   has met by time 1") is the uniform timing result that makes the bound
   `n`-independent, and nothing here approaches it. **This is now the main
   outstanding item.**

2. **The `n = 3` work covers only the steady state.** §3.12 proves the
   three-drone cycle and its period, which exercises the middle-drone and
   simultaneous-event machinery. But there is **no converging `n = 3` trace**
   — nothing that starts out of position and settles.

3. **The traces are single configurations, not the sharp worst case.** `spread`
   converges at `5/4` against a bound of `3/2`. Closing that last quarter needs
   the drones started *arbitrarily* close, i.e. a family parameterised by `ε`.
   That would show the bound is **attained**, which the paper asserts and this
   development does not check.

4. **The nondeterminism is not modelled.** When three or more drones converge
   the paper leaves open which neighbour the middle one escorts, and notes the
   strongest bound quantifies over all resolutions. `newDir` picks one. Every
   result here, non-Zeno included, inherits that restriction.

5. **Stage 3's original headline goal is out of scope, and the plan was wrong
   to list it.** `PLAN.md` §5.2 proposed refuting the false `3T` bound. That
   bound is about **phase 1** — estimate propagation — which is Algorithm B.
   This development models Algorithm A, where estimates are correct by
   assumption and absent from `Config`. Unreachable here, not merely
   unfinished. Recorded as a planning error.

6. **Unused definitions.** `Config.Together` is defined but unused, and
   `Config.Valid` has been superseded by `Config.Invariant` without removal.

7. **Algorithm B is entirely out of scope** — wrong estimates, changing
   perimeter, drones joining or leaving. That is where the original proof broke
   and where the open problem lives.

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
which would require their model rather than this one, and it inherits this
development's choice of one resolution of the paper's nondeterminism.

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
'DPSS.Config.together_refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.together_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
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

**345/345 clean — `sorryAx` appears zero times.**
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

## 9. The work package

What is left, sized. **B is the bulk and B1 is the gate** — Lemmas 3.3, 3.4 and
3.7 all quote it.

| # | Item | Size | Notes |
|---|---|---|---|
| **A** | ~~**Non-Zeno**~~ | ✅ | **complete** — the contribution ACL2 had to assume |
| A1 | ~~Every event turns at least one drone~~ | ✅ | `someDroneTurns_step`, unconditional |
| A2 | ~~The minimum is attained by a genuine event~~ | ✅ | folded into A1; gap 2 closed |
| A3 | ~~Consecutive turns `1/n` apart~~ | ✅ | §3.15 |
| A4 | ~~Assemble `NonZeno`~~ | ✅ | **§3.16 — done** |
| **B** | **Theorem 2.1** | | *the headline* |
| B1 | Lemma 3.2 — `BothLeftApart` case 3 | **L** | §3.13; needs a *reachability* invariant, see §3.20 |
| B2 | ~~Lemmas 3.3, 3.4~~ | ✅ | §3.17 — conditional on `BothLeftApart` only, as 3.2 is |
| B3 | Lemma 3.5 — every pair has met by time 1 | **L** | `HaveMetBy` now defined (§3.17); the proof is not |
| B4 | ~~Lemma 3.6 — turn persistence~~ | ✅ | §3.18, unconditional |
| B5 | Lemma 3.7 — the `+1/n` inductive step | M | |
| B6 | Assemble `2 − 1/n` | S | |
| **C** | **Fidelity** | | |
| C1 | Nondeterminism: a relation, not a function | M | gap 7; or document as a restriction |
| C2 | Converging `n = 3` trace; a genuine three-way meeting | M | gap 4 |
| C3 | An `ε`-family showing the bound is *attained* | M | gap 5 |
| **D** | Cleanup: unused definitions, `PLAN.md` scope fix | S | gaps 6, 8 |

Sizes are relative: **S** is a sitting, **M** is a session, **L** is the kind of
argument the paper spends a figure on and the ACL2 team spent 11K lines around.
