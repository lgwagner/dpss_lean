# DPSS formalization — status

<!-- BEGIN:META -->
**Generated:** 2026-09-12  
**Commit at time of writing:** `f268410a0149`  
**Toolchain:** Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release), Mathlib v4.33.1
<!-- END:META -->

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
| 1 | Definitional layer: state, events, runs, order invariant, non-Zeno | **in progress** — non-Zeno outstanding |
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
| **Non-Zeno proper (the counting step)** | **not started** |

---

## 3. What is actually proved

<!-- BEGIN:COUNTS -->
**266 theorems**, all `sorry`-free, across 12 files (`Basic.lean` 218 lines, `Coherence.lean` 386 lines, `Dynamics.lean` 228 lines, `Events.lean` 246 lines, `Examples.lean` 805 lines, `ExamplesThree.lean` 375 lines, `NextEvent.lean` 315 lines, `NonZeno.lean` 143 lines, `Schedule.lean` 214 lines, `Step.lean` 239 lines, `Synchronization.lean` 161 lines, `Turning.lean` 180 lines).
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

---

## 4. What is **not** proved — read this part

This is the honest gap list, ordered by importance.

1. **Non-Zeno: the counting step is missing.** The geometry is done —
   consecutive turns of one drone are at least `1/n` apart. What remains: every
   event turns at least one drone, each drone turns at most once per `1/n`,
   therefore only finitely many events fit in a bounded interval. That needs a
   pigeonhole over `Fin n`, and also gap 2. **This is the headline opportunity
   (§5) and it is not finished.**

2. **The minimum is not yet proved genuine.** `timeToNextEvent` minimises over
   `borderTime` for *every* drone, including interior ones where no border
   event is reachable. The local domination lemmas are proved; the chaining
   into "`timeToNextEvent` is attained by a genuine event" is not done.

   Instructive: my first attempt at the rightward version was **false**, and
   Lean caught it.

3. **Theorem 2.1 is not proved in general** — only at `n = 1`, and for one
   specific `n = 2` configuration. Lemma 3.1 is done; **Lemmas 3.2 through 3.8
   are untouched.** Lemma 3.5 in particular ("every adjacent pair has met by
   time 1") is the uniform timing result that makes the bound `n`-independent,
   and nothing here approaches it.

4. **The `n = 3` work covers only the steady state.** §3.12 proves the
   three-drone cycle and its period, which exercises the middle-drone and
   simultaneous-event machinery for the first time. But there is **no
   converging `n = 3` trace** — nothing that starts out of position and settles
   — and no configuration with three drones actually meeting at once, which is
   where the nondeterminism of gap 6 would bite.

5. **The traces are single configurations, not the sharp worst case.** `spread`
   converges at `5/4` against a bound of `3/2`. Closing that last quarter needs
   the drones started *arbitrarily* close together, i.e. a family parameterised
   by `ε` rather than one fixed gap. That would demonstrate the bound is
   **attained**, which the paper asserts and this development does not check.

6. **Stage 3's original headline goal is out of scope, and the plan was wrong
   to list it.** `PLAN.md` §5.2 proposed formalizing the Davis et al.
   counterexample to refute the false `3T` bound. That bound is about **phase
   1** — the propagation of *estimates* — which is Algorithm B. This
   development models Algorithm A, where estimates are correct by assumption
   and absent from `Config` entirely. The refutation is therefore unreachable
   here, not merely unfinished. Recording it as a planning error rather than
   silently dropping it.

7. **The nondeterminism is not modelled.** When three or more drones converge
   the paper leaves open which neighbour the middle one escorts, and notes the
   strongest bound quantifies over all resolutions. `newDir` picks one.

8. **Unused definitions.** `Config.Together` is defined but unused, and
   `Config.Valid` has been superseded by `Config.Invariant` without removal.

9. **Algorithm B is entirely out of scope** — wrong estimates, changing
   perimeter, drones joining or leaving.

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

## 5. Why Stage 1 matters more than I first said

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

Formalizing AvD's argument in Lean closes that gap. It is a genuine
contribution rather than a reproduction, it sits in Stage 1, and **it stands
even if the `2 − 1/n` proof never closes.**

**A departure worth flagging.** I am *not* following the paper's own non-Zeno
argument. It rests on the claim that "if drone `i+1` makes two consecutive left
turns, then drone `i` must turn right in the interim", which it calls not hard
to show and does not show. I could not reconstruct it: a right turn by `i+1`
comes either from separating from `i` — at which instant `i` turns **left** —
or from meeting `i` left of their shared boundary, at which instant `i` does
not turn at all. It may still be true, but formalizing an unverified sketch is
the one move this particular project cannot afford. The route taken instead
(interval-crossing, §3.7–3.8) is self-contained and reuses a lemma the
convergence proof needs anyway.

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
'DPSS.Config.not_meetLeft_of_dir_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.not_meetRight_of_dir_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_eq_leftEnd_of_sepLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_eq_rightEnd_of_sepRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.rightEnd_le_pos_of_turnsLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.pos_le_leftEnd_of_turnsRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.turn_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**266/266 clean — `sorryAx` appears zero times.**
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

## 9. Next steps, in order

1. ~~Everything through Lemma 3.1, the run invariants, and an `n = 2` trace.~~
   **Done.**
2. **A converging trace**: start `n = 2` unsynchronized (both drones together
   near a border) and show it settles, checking the paper's sharp `5/2`.
3. **Finish non-Zeno** (gap 1): every event turns a drone; pigeonhole over
   `Fin n`.
4. `n = 3`, and the known-false phase-1 bound.
5. Lemmas 3.2 → 3.7, then Theorem 2.1 itself.
