# A reader's guide to the whole work package

*For someone picking this up cold, or coming back after the session in which
the last item closed.*

The other documents each answer one question. `README.md`: what the project is.
`STATUS.md`: what is proved and what is not, written to be audited.
`INSIGHTS.md`: what the work taught. `PLAN.md`: what to do next.
`CHANGELOG.md`: what changed when. **This file walks the work package** — every
item, what it claimed, why it was needed, how it was proved, where it lives,
and what it cost.

**594 theorems, all `sorry`-free, across 33 files. The work package is
complete.**

---

## 0. The package at a glance

The package was written against the two published artefacts this project sits
between: Avigad–van Doorn's corrected hand proof (arXiv:2008.04262) and the
ACL2 mechanization of it (arXiv:2205.11697). Group **A** closes the gap between
them; group **B** is the headline theorem; group **C** closes the distance
between the model and the paper; group **D** is housekeeping.

| | Item | Where | §
|---|---|---|---|
| **A** | **Non-Zeno** — the clock cannot stall | [`NonZenoProof.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/NonZenoProof.lean) | [4](#4-group-a--non-zeno) |
| A1 | Every event turns at least one drone | [`EventsTurn.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/EventsTurn.lean) | 4.1 |
| A2 | The minimum is attained by a genuine event | folded into A1 | 4.1 |
| A3 | Consecutive turns of one drone are `1/n` apart | [`TurnSpacing.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/TurnSpacing.lean) | 4.2 |
| A4 | Assemble [`nonZeno`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/NonZenoProof.lean#L127) | [`NonZenoProof.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/NonZenoProof.lean) | 4.3 |
| **B** | **Theorem 2.1** — synchronization by `2 − 1/n` | [`Convergence.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean) | [5](#5-group-b--theorem-21) |
| B1 | Lemma 3.2 — separation passes left sync on | [`BalanceInvariant.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/BalanceInvariant.lean) | 5.2 |
| B2 | Lemmas 3.3 and 3.4 | [`BalanceInvariant.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/BalanceInvariant.lean) | 5.3 |
| B3 | Lemma 3.5 — every pair meets within time 1 | [`Meeting.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Meeting.lean) | 5.4 |
| B4 | Lemma 3.6 — turn persistence | [`TurnPersistence.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/TurnPersistence.lean) | 5.5 |
| B5 | Lemma 3.7 — the `+1/n` inductive step | [`InductionStep.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/InductionStep.lean) | 5.6 |
| B6 | Assemble `2 − 1/n` | [`Convergence.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean) | 5.7 |
| B7 | The symmetric half | [`Mirror.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Mirror.lean) | 5.8 |
| **C** | **Fidelity** — the model against the paper | | [6](#6-group-c--fidelity) |
| C1 | Nondeterminism: measure it | [`Priority.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Priority.lean) | 6.1 |
| C1′ | Nondeterminism: [`step`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L151) as a relation | [`Nondeterminism.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean) | 6.2 |
| C2 | A converging `n = 3` trace | [`ThreeConverge.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/ThreeConverge.lean) | 6.3 |
| C3 | The bound is attained at `n = 2` | [`Sharpness.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Sharpness.lean) | 6.4 |
| C3′ | The bound is attained at every `n` | [`SharpnessGeneral.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/SharpnessGeneral.lean) | 6.5 |
| **D** | **Cleanup** | | [7](#7-group-d--cleanup) |
| D1 | Remove superseded definitions | [`Basic.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Basic.lean) | 7.1 |
| D2 | Make [`HaveMetBy`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/LeftSyncLemmas.lean#L195) locally checkable | *not needed* | 7.2 |

Read the groups in order: **A** and **B** both stand on the model (§3) and on
Lemma 3.1, and **B5** additionally needs the real-time layer (§5.6). **C** and
**D** depend on nothing.

---

## 1. What the package claims, in four theorems

```lean
-- A: the clock along a run is unbounded
theorem nonZeno (hn : 0 < n) (hi : c.Invariant) : NonZeno c hn

-- B: every drone is inside its own segment from 2 − 1/n onwards
theorem convergesBy (hn : 0 < n) (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) : ConvergesBy c hn

-- C3′: and no smaller constant would do, at any team size
theorem bound_sharp_general (hn2 : 2 ≤ n) (B : ℝ) (hB : B < 2 - 1 / (n : ℝ)) : …

-- C1′: and it holds for every resolution of the paper's nondeterminism
theorem convergesBy_of_isRun (hn) (hi) (hab) (hf : IsRun c hn f) …
```

There is also a stronger form of B over **instants** rather than event indices —
[`sync_at_of_time`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean#L191), which is the form the paper states — and the [`AllSync`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Synchronization.lean#L84)
phrasing, [`allSync_of_time`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean#L207).

**Why non-Zeno is a contribution and not a reproduction.** The ACL2
mechanization admits its event-stepper as a *partial* function via `def::ung`
and carries the assumption into its top-level theorem as an explicit
hypothesis:

```lisp
(defthm dpss-location-convergence-after-2T-1
 (implies (and (wf-ensemble ens)
               (step-time-always-terminates))   ; admitted, never proved
          (dpss-location-convergence (step-time (- (* 2 (TEE)) (ONE)) ens))))
```

That hypothesis *is* non-Zeno. Avigad–van Doorn argue for it and do not
mechanize it; ACL2 mechanizes everything else and assumes it. The two published
artefacts were complementary, and **A** closes the gap — though see §4.3 for a
careful statement of what it does and does not claim.

---

## 2. Checking it yourself

```bash
lake build                        # Lean 4.33.1 + Mathlib v4.33.1; expect exit 0
grep -rn "sorry" Dpss/            # only prose mentions, never a tactic
python3 scripts/audit.py          # every theorem's axiom dependencies
python3 scripts/refresh_status.py # regenerate STATUS.md's generated blocks
```

`scripts/audit.py` fails if any theorem depends on `sorryAx`, and it runs in
CI. The line to look for:

```
'DPSS.Config.convergesBy' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Those three are Lean's standard axioms. `sorryAx` is not there, and it cannot
be hidden.

**Non-vacuity.** Both headline theorems are conditional on [`Invariant`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Coherence.lean#L341), so a
model in which nothing satisfies it would make them true for the empty reason.
Three concrete configurations discharge every hypothesis, and the general
theorems reproduce conclusions those traces had established by hand:

| Instance | Team | Exercises |
|---|---|---|
| [`approach_converges_general`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean#L256) | `n = 2` | drones apart, converging head-on |
| [`spread_converges_general`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean#L282) | `n = 2` | all drones heading the same way |
| [`cfgB_converges_general`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean#L309) | `n = 3` | a pair co-located **and heading apart** |

The third matters most: it satisfies [`ApartOnBoundaries`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/InductionStep.lean#L89) while *exercising* the
case rather than avoiding it.

---

## 3. The model everything stands on

Read this before A or B; both quote it constantly.

**Geometry.** The perimeter is `[0,1]`, drones move at unit speed, drone `i`
owns `[i/n, (i+1)/n]`. The paper numbers drones `1…n`; `Fin n` is `0…n−1`, so
every statement here is shifted by one. `commonEnd i = rightEnd i` is the
boundary drones `i` and `i+1` share.

**State.** `Config n` is a time, a position function and a heading function —
and **no estimates**, because Algorithm A assumes them correct, which is the
whole scope decision. [`Dpss/Basic.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Basic.lean).

**Motion.** `advance dt` flies everyone forward; `gap i` is the signed distance
to the right-hand neighbour and `sepRate i` the rate it changes at — `−2`, `0`
or `+2`. One equation, [`gap_advance`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Dynamics.lean#L93), is the engine of the file.
[`Dpss/Dynamics.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Dynamics.lean).

**The three events.** A drone reaches a perimeter border; a pair meets; a pair
separates at the boundary they share. [`Dpss/Events.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Events.lean).

> **Where a definition was wrong, and a trace caught it.** [`AtSeparation`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Events.lean#L113)
> originally required the pair to be *escorting* — co-located **and heading the
> same way**. Two drones converging on their shared boundary have *opposite*
> headings right up to the instant they meet, so no separation fired, the meet
> branch took over, and the right-hand drone was driven out of its own
> interval. The bug silently falsified the target theorem and was invisible to
> 145 theorems, because nothing forced the definitions to be exercised. A
> formalization's danger is not a wrong proof — Lean stops those. It is a wrong
> **definition** supporting a flawless proof of something else.

**The schedule.** [`borderTime`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/NextEvent.lean#L55), [`meetTime`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Dynamics.lean#L127), [`separationTime`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Schedule.lean#L87) per drone,
minimised into [`timeToNextEvent`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/NextEvent.lean#L274). [`Dpss/Schedule.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Schedule.lean), [`Dpss/NextEvent.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/NextEvent.lean).

**The step.** Fly to the next event, then let every due event fire *at once*:
each drone's new heading is [`newDir`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L105), a function of the **whole**
configuration, so simultaneity is automatic rather than an ordering that would
then need justifying. The price is a visible priority order —
`border > separation > meet > unchanged` — which §6.1 and §6.2 are about.
[`Dpss/Step.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean).

**The standing invariant.** `Config.Invariant`: every drone on the perimeter,
drones in left-to-right order, escorting pairs with a non-negative separation
deadline. Proved preserved by every step ([`invariant_step`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Coherence.lean#L347), [`invariant_run`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Coherence.lean#L354))
and proved satisfiable. [`Dpss/Coherence.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Coherence.lean).

> **Invariants enforced by construction beat invariants inherited.**
> [`escortsCoherent_step`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Coherence.lean#L236) was written with three hypotheses and Lean reported all
> three unused: the property is guaranteed by the *scheduler*, which always
> offers an escorting pair its separation deadline, so a step can never
> overshoot it. That pattern repeated six times, and each time deleting the
> hypothesis gave a stronger theorem.

**Lemma 3.1 — where a drone may turn.** [`Dpss/Turning.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Turning.lean). A rightward drone
turns left only at or beyond its own right endpoint; a leftward drone turns
right only at or before its left endpoint.

```lean
rightEnd_le_pos_of_turnsLeft  : c.TurnsLeft i  → rightEnd i ≤ c.pos i
pos_le_leftEnd_of_turnsRight  : c.TurnsRight i → c.pos i ≤ leftEnd i
```

This is the single most reused result in the development. It carries **A**
(§4.2), **B** (§5.2, §5.4), and **C3′** (§6.5), pointed a different way each
time. Its companion — *a drone that reverses to leftward is co-located with its
right-hand neighbour* ([`coLocated_of_turnsLeft`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/PairBalance.lean#L209)) — has paid for itself five
times.

---

## 4. Group A — Non-Zeno

**The claim.** `∀ T : ℝ, ∃ k, T < (c.run hn k).time`. The system cannot pack
infinitely many events into a finite stretch of time.

**Why it is not optional.** Without it the clock can stall, and then a drone
can sit still for ever, never turning and never leaving the perimeter — which
makes Lemma 3.5 (§5.4) false. Non-Zeno turned out to be load-bearing for the
convergence proof, not a separate headline.

### 4.1 A1, A2 — every event turns at least one drone

[`someDroneTurns_step`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/EventsTurn.lean#L282), [`Dpss/EventsTurn.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/EventsTurn.lean), **unconditional**.

Whatever sets the step's length — a border deadline, a meeting time, a
separation time — the event that deadline belongs to really does fire, and it
really does reverse somebody. The awkward cases are cascades, where several
events come due at one instant; [`newDir`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L105) being a function of the whole
configuration is what makes them harmless.

> **A2 was a phantom.** A commit went into proving domination lemmas to contain
> a worry about "spurious" border deadlines for interior drones. Flying a drone
> for exactly [`borderTime`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/NextEvent.lean#L55) lands it on `0` or `1` — that is what the quantity
> *is* — so the event genuinely fires. The lemmas were not needed, and A2
> folded into A1.

### 4.2 A3 — consecutive turns of one drone are `1/n` apart

[`time_gap_of_consecutive_turns`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/TurnSpacing.lean#L63), [`Dpss/TurnSpacing.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/TurnSpacing.lean).

Lemma 3.1 says a drone turns right only at or before its left endpoint and left
only at or beyond its right endpoint. So between two consecutive turns it has
crossed its whole interval — a distance of `1/n` — and at unit speed that costs
`1/n` of time. [`Dpss/NonZeno.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/NonZeno.lean) supplies the run-level half
([`pos_sub_eq_of_dirConst`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/NonZeno.lean#L88): while a heading is fixed, position advances exactly
as time does).

### 4.3 A4 — the counting argument

[`nonZeno`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/NonZenoProof.lean#L127), [`Dpss/NonZenoProof.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/NonZenoProof.lean). Every step turns a drone; each drone turns
at most once per `1/n`; there are `n` drones; so `n+1` steps buy `1/n` of
clock, and `m(n+1)` steps buy `m/n`.

**A deliberate departure from the paper.** Avigad–van Doorn prove non-Zeno by a
different route, resting on a claim they call "not hard to show" and do not
show: *if drone `i+1` makes two consecutive left turns, then drone `i` must
turn right in the interim*. It could not be reconstructed here — a right turn
by `i+1` comes either from separating from `i`, at which instant `i` turns
**left**, or from meeting `i` left of their shared boundary, at which instant
`i` does not turn at all. The claim may well be true. But this is a paper whose
entire subject is a convincing-looking proof that stood for a decade and was
false, so formalizing an unverified sketch is the one move this project cannot
afford. The counting route is self-contained, avoids the disputed claim, and
reuses a lemma the convergence proof needed anyway.

**What A does and does not claim.** It proves non-Zeno *for this Lean model* of
Algorithm A. It does not literally discharge the ACL2 hypothesis, which would
require their model rather than this one. `STATUS.md` §5 states this carefully.

---

## 5. Group B — Theorem 2.1

**The claim.** All drones synchronized by `2 − 1/n`. The paper gives the
top-level induction in three lines; **B** is the work of making its three
inputs true.

> Since drone 1 is always left synchronized and all the drones have met by time
> 1, by induction on `i < n` we have that drones `1, …, i` are left synchronized
> at time `1 + (i−1)/n`. Taking `i = n` yields the theorem.

### 5.1 The quantity that replaces the paper's figure

Lemma 3.2's published proof is a timing argument with a picture. Here it is one
number — [`Dpss/PairBalance.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/PairBalance.lean):

```lean
pairBalance i = (pos i − commonEnd i) + (pos (i+1) − commonEnd i)
```

Two facts make it the right quantity. At a separation the pair sits exactly on
the boundary, so the balance is **zero**. And it evolves at `sign i + sign
(i+1)`, so it is *constant* whenever the two head opposite ways — which is
exactly what they do after separating and again while approaching.

And its sign says precisely what the induction needs:
[`leftEnd_le_pos_of_pairBalance`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/PairBalance.lean#L119) — **balance ≥ 0 keeps the right-hand drone
inside its own interval**.

> **Gap and balance are the difference and the sum.** The gap moves at the
> *difference* of the two velocities, the balance at their *sum*. That is why a
> pair heading apart has a growing gap and a constant balance.

### 5.2 B1 — Lemma 3.2

[`leftSync_of_separation`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/BalanceInvariant.lean#L286), [`Dpss/BalanceInvariant.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/BalanceInvariant.lean), **unconditional**.

The balance can only fall when both drones head left, and when they do so while
*co-located* they are escorting, so the scheduler stops them at the separation —
exactly where the balance reaches zero. That leaves one configuration class,
[`BothLeftApart`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/PairBalance.lean#L140), and B1 is the story of closing it.

Two of its three routes closed early: a drone that reverses to leftward is
co-located with its neighbour (so it cannot be the left member of an *apart*
pair), and a leftward pair that was not already apart stays together. The third
— the left drone holding its heading while the right one reverses — is where
drone `j`'s left synchronization has to do its work.

**The paper's timing argument is really positional.** *"Drone `j+1` must have
taken at least as long to turn around as drone `j`"* becomes arithmetic on
interval endpoints once the balance is in hand: with the balance at zero the
two drones are displaced from their shared boundary by *equal* amounts; left
synchronization caps the left drone's displacement at `1/n`, hence the right
drone's too; and Lemma 3.1 permits the right drone to reverse only at or
*beyond* that very point. The two constraints meet exactly and pin both drones
([`pinned_of_balance_zero`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/PairBalance.lean#L400)).

The invariant that finally carried it — [`PairPhase`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/BalanceInvariant.lean#L85) — has three clauses:
balance nonnegative; **heading apart ⟹ balance exactly zero**; and
`BothLeftApart ⟹ the left drone is on its own left endpoint`.

> **Clause 2 is the one that matters**, and it is why clause 1 alone is not an
> invariant: the pinning argument needs the balance *exactly* zero, not merely
> nonnegative.
>
> **Deriving beat guessing.** Three invariant shapes were tried and two were
> wrong; the derived one worked essentially first time. The derivation is
> `STATUS.md` §8a. Several days of commits went to the guessing.
>
> **A pair that is apart cannot change phase.** The whole difficulty collapses
> once you notice this: every event that could deliver `left` to one drone and
> `right` to the other requires *this pair* to be co-located. So an apart pair
> carries its balance across untouched, and only the co-located case needs work.

### 5.3 B2 — Lemmas 3.3 and 3.4

[`leftSync_of_escorting`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/BalanceInvariant.lean#L295) and [`leftSync_of_reached_boundary`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/BalanceInvariant.lean#L311),
[`Dpss/BalanceInvariant.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/BalanceInvariant.lean).

Both reduce to one question: does the starting configuration give a nonnegative
balance? For 3.3 it does for free — an escorting pair's balance is exactly
*twice its separation deadline*, and escort coherence says that deadline is
never in the past, so **the balance is nonnegative because the scheduler makes
it so**.

> **3.4 does not get the invariant from its own hypothesis.** Reaching the
> shared boundary gives a *nonnegative* balance, not a zero one, so a pair
> heading apart from there may carry a strictly positive balance and clause 2
> fails. 3.4 therefore takes [`PairPhase`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/BalanceInvariant.lean#L85) as a hypothesis — which a caller inside
> a run can always supply, since it is proved preserved. An asymmetry with 3.2
> and 3.3 that was not anticipated.

### 5.4 B3 — Lemma 3.5

[`exists_coLocated_within_one`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Meeting.lean#L340), [`Dpss/Meeting.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Meeting.lean). Every adjacent pair becomes
co-located within **one unit of time** — uniformly in `n`, which is what makes
the final bound `n`-independent. Kingston et al.'s original argument gave only
a bound linear in `n`.

The accounting, in the paper's notation: with `x ≤ y` the starting positions,
`w` where the left drone first heads right and `z` where the right one first
heads left, the gap grows until the **first** of the two turns and is constant
until the **second**, after which the pair approaches. The elapsed times add
and the bound collapses to `(z − w) + (x − y)/2 ≤ 1`, using only that positions
lie in `[0,1]` and `x ≤ y`.

> **The paper's distance computation survived intact** — but it needed the
> *exact* elapsed time to each drone's first turn, not a bound on it. The result
> comes out at exactly 1, so a chain of inequalities would not have closed.
> Hence [`exists_firstRight`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Meeting.lean#L202)/[`exists_firstLeft`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Meeting.lean#L236), which give the first turn **and
> when it happens**.
>
> **Which drone turns first does not matter.** The two orderings give the same
> total, so no case split on that is needed — only on which index is larger, to
> name the phases. That halved the work.
>
> **Lemma 3.2's by-product carried it.** *A drone heading right can only reverse
> by becoming co-located with its right-hand neighbour* is what makes an
> approaching pair's gap close at a steady rate: neither drone can turn while
> they are apart.

[`Dpss/EventuallyTurns.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/EventuallyTurns.lean) supplies the step the paper takes for granted —
every drone eventually turns — and it is **only provable once the clock cannot
stall**. This is where **A** pays for itself inside **B**.

### 5.5 B4 — Lemma 3.6

[`dir_left_since_of_never_coLocated`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/TurnPersistence.lean#L89), [`Dpss/TurnPersistence.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/TurnPersistence.lean),
**unconditional**.

A drone found heading left at the end of a stretch in which its pair was never
together has been heading left throughout it: it cannot have turned left
(that would put it on its neighbour), and had it turned right it would still be
heading right.

> **It came almost free.** Its load-bearing step had already been proved to
> close one branch of Lemma 3.2's obstruction.

### 5.6 B5 — Lemma 3.7, and the real-time layer

[`leftSyncAt_next`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/InductionStep.lean#L141), [`Dpss/InductionStep.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/InductionStep.lean), on [`Dpss/RealTime.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/RealTime.lean).

**The obstacle, which the plan flagged in advance.** Every predicate in the
development is indexed by **step number**, and that carried ~500 theorems
without complaint. Lemma 3.7's conclusion is a deadline in **real time**, and
its proof reads a drone's heading and position at an instant that in general
lies strictly inside a step. The step-indexed reading is genuinely weaker
there — a drone heading right can sit left of its endpoint mid-step and be back
inside its interval by the next event — so a step-indexed Lemma 3.7 does not
merely look inelegant. It looks false.

[`Dpss/RealTime.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/RealTime.lean) adds the missing layer, with no choice and no partial
function:

```lean
posIn p i s = pos_p i + sign (dir_p i) * (s − time_p)   -- drone i at time s
InStep p s  = time_p ≤ s ∧ s ≤ time_{p+1}                -- s is inside step p
```

and [`exists_lastBefore`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/RealTime.lean#L183) — non-Zeno again — supplies a step for any instant.

Two facts carry the layer. **A linear function nonnegative at both ends of an
interval is nonnegative throughout it** ([`nonneg_of_endpoints`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/RealTime.lean#L63), three lines):
within a step every quantity of interest is affine in time, so every "true at
the events, therefore true in between" argument is that one lemma with
different names substituted. And **if the clock does not move between two
indices, no drone moves either** ([`pos_eq_of_time_le`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/RealTime.lean#L206)): zero-length steps are
routine, so `time_m ≤ time_k` does *not* give `m ≤ k` — but it does give equal
positions, and that is what every such argument actually wanted.

**The lemma itself** splits on what drone `i` is doing at the instant `T`:

* **heading right** — within `1/n` it is at or beyond the boundary it shares
  with `i+1`, and ordering carries `i+1` past its own left endpoint. When it
  finally does turn, it turns *onto* its neighbour, and the pivot below takes
  over;
* **heading left** — take the **last index at or before `T` at which the pair
  was co-located**, which exists precisely because they have met. Lemma 3.6 says
  `i` has been heading left ever since, so it was at least as far right then as
  it is now, hence already left synchronized there.

> **The paper's two leftward cases are one case.** It splits on whether the pair
> is together *now*; taking the last co-located index covers both, with an empty
> range when they are. That halved the case analysis.

Both branches end at the same configuration — the pair co-located with the left
drone heading left — and [`leftSync_next_of_coLocated_left`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/InductionStep.lean#L123) discharges it as
Lemma 3.3 (escorting) or Lemma 3.2 (separating).

> **Should the time-indexed predicate have been primary from the start?** The
> plan asked for the answer to be recorded. It is **no**: the target statement
> is index-shaped, every earlier lemma is index-shaped, and real time is needed
> only inside one proof. Making it primary would have taxed 500 theorems to pay
> for one.

### 5.7 B6 — the assembly

[`convergesBy`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean#L199), [`Dpss/Convergence.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean).

1. **Base** — drone 0's left endpoint is the perimeter's left border, which
   [`onPerimeter_run`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Coherence.lean#L361) says nobody crosses ([`leftSyncAt_zero`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/RealTime.lean#L332)).
2. **Meeting** — every pair has met by time 1 (B3).
3. **Step** — `+1/n` per drone (B5).
4. **Other half** — right synchronization by reflection (B7).

**The bound is exact.** Drone `i` is left synchronized at `1 + i/n`, and
`i = n−1` gives `1 + (n−1)/n = 2 − 1/n`. Nothing is rounded and no `ε` is lost
anywhere, which is load-bearing rather than aesthetic — see §6.4.

> **Stating the goal as a `Prop`-valued definition from day one paid off.** The
> repository was never `sorry`-ful, the target was always precisely visible, and
> discharging it was a one-line theorem at the end rather than a renegotiation
> of what had been aimed at.

### 5.8 B7 — the symmetric half

[`Dpss/Mirror.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Mirror.lean), 737 lines. Avigad–van Doorn dispose of this in four words —
*"by symmetry it suffices to show all the drones are left synchronized"* — and
on paper that is honest.

In Lean it needs a reflection map (`pos ↦ 1 − pos`, headings flipped, indices
reversed) proved to commute with [`advance`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Dynamics.lean#L41), [`step`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L151) and [`run`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L219); reflection laws
for every local quantity and every event; invariance of the global deadline;
and then the transfer principle [`rightSync_iff_leftSync_mirror`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Mirror.lean#L706). A real-time
version ([`rightSyncAt_iff_leftSyncAt_mirror`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean#L79)) and a reflection of
[`ApartOnBoundaries`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/InductionStep.lean#L89) were needed later for B6.

> **It was not on the work list until someone went looking**, which is the real
> lesson: a step the source treats as a triviality about the *mathematics* may
> be substantial work about the *formalization*.
>
> **The priority orders do not correspond.** [`newDir`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L105) checks the left border
> first; its reflection checks the right border first. Harmless only because
> paired branches are mutually exclusive — which had to be proved.
>
> **The tie-break flips.** [`escortDir`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Events.lean#L123) and [`escortDirLeft`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L97) reflect into each
> other *except exactly on the shared boundary*, where one reads `pos <
> boundary` and the other `boundary < pos`. The mathematics is symmetric; a
> strict inequality is not.

---

## 6. Group C — fidelity

Where the model and the paper could still differ, and what closing each gap
showed.

### 6.1 C1 — measuring the nondeterminism

[`Dpss/Priority.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Priority.lean). [`newDir`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L105) resolves competing events in the order
`border > separation > meet > unchanged`, and three documents had recorded that
order for months as "one resolution" of a choice the paper leaves open. That
description was written when the order was chosen, and never checked.

Checking it means: for every pair of events that can be due at one drone at one
instant, compute both answers and compare.

| Both due | Separation says | Meet says | |
|---|---|---|---|
| right border + [`MeetRight`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L86) | `left` | `left` | agree |
| left border + [`MeetLeft`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L90) | `right` | `right` | agree |
| left border + [`SepLeft`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L82) | — | — | **impossible** |
| right border + [`SepRight`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L77) | — | — | **impossible** |
| [`SepRight`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L77) + [`MeetRight`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L86) | `left` | `left` | agree |
| [`SepRight`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L77) + [`MeetLeft`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L90) | `left` | `left` | agree |
| [`SepLeft`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L82) + [`MeetRight`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L86) | `right` | `right` | agree |
| [`SepLeft`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L82) + [`MeetLeft`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L90) | `right` | `left` | **differ** |

The agreements have one reason: a separating drone is standing on a boundary,
and from a boundary the escort heading is forced. The single disagreement is
the paper's **bounce**, and [`newDirMeetFirst_leaves_interval`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Priority.lean#L262) shows the
alternative walks a drone off its own left endpoint — the very failure §3's
trace caught.

> **A caveat is a claim.** The standing description was seven-eighths wrong, and
> worse, it named the wrong thing: the real question is what a *meet* is, not
> what order the events fire in. Getting the name right also re-sized the
> remaining work.

### 6.2 C1′ — the step as a relation, and its collapse

[`Dpss/Nondeterminism.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean). The paper says exactly what it leaves open:

> it does not specify what happens when a group of three or more drones come
> together and determine that three of them are within the middle drone's
> interval; in that case, **the middle drone can escort either neighbor to their
> common border**.

`PLAN.md` sized this as: make [`step`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L151) a relation and re-prove the development
over an arbitrary trajectory — ~30 primitive lemmas re-derived from a
specification, and every statement in 33 files gaining a parameter. **That is
not what the file does**, because the same passage says why it is unnecessary:

> Neither of these issues bears on the results reported below, since our upper
> bound only concerns **phase 2, where these issues do not arise**.

That is a claim about reachable states, and it is provable.

* `LegitDir c d` specifies **every** heading assignment the protocol permits,
  with the middle drone's choice genuinely open;
* [`StepRel`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean#L302) is one step of the relation and [`IsRun`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean#L310) a trajectory;
* [`not_strictly_inside_of_grouped`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean#L170) is **the collapse**. The two escort headings
  differ exactly when the meeting point lies strictly inside the middle drone's
  interval — word for word the paper's own description. Suppose it does. The
  pair `(i, i+1)` is together at `p < commonEnd i`: heading apart puts them *on*
  `commonEnd i` by [`ApartOnBoundary`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Reachable.lean#L47), and escorting points them at `commonEnd
  i`, to the right — so drone `i` heads right. Then `(i−1, i)` is together at
  `p > commonEnd (i−1)`: heading apart puts them on `commonEnd (i−1)`,
  escorting points them left, and the remaining case needs `i` heading left.
  Every case closes;
* so [`legitDir_unique`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean#L265) — the specification has exactly one solution — and
  [`isRun_eq_run`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean#L365): every trajectory of the relation **is** the run of the
  function. [`convergesBy_of_isRun`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean#L384) and [`nonZeno_of_isRun`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean#L392) follow.

> **Keep the width honest.** A specification that quietly admits only one value
> makes uniqueness vacuous. `ExamplesThree.triple` exhibits a configuration
> where the open clause genuinely admits two headings, so the collapse theorem
> has content; [`triple_not_reachable`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean#L453) then says what the collapse implies about
> it.

### 6.3 C2 — a three-drone run that starts out of position

[`Dpss/ThreeConverge.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/ThreeConverge.lean). [`ExamplesThree.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/ExamplesThree.lean) builds the three-drone steady
state and proves it cycles with period `2/n`, but every trace there starts
synchronized and stays so — nothing showed the system ever *reaches* that
state.

[`cfgS`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/ThreeConverge.lean#L61) is the configuration anyone writes down first: each drone on its own
left endpoint, all heading right. It is **not** synchronized.

```
t = 0     0 →     1/3 →    2/3 →
t = 1/3   1/3 →   2/3 →    1 ←      the right drone bounces
t = 1/2   1/2 →   5/6 ←    5/6 ←    middle and right meet, escort back
t = 2/3   2/3     2/3      2/3      all three at one point
t = 1     1/3 ←   1/3 →    1 ←      the steady state
```

Drone 0 is carried out of `[0, 1/3]` almost at once and reaches `2/3` before
anything turns it round; the team settles at time 1 against a bound of `5/3`.
Step 3 is the **three-way meeting** the package asked for by name, and where
the model's priority order is visible: drone 1 is at once co-located with drone
0, which is still heading right, and standing on the boundary it shares with
drone 2.

> **The three-way meeting cost nothing extra** — it arrived on its own in the
> first converging trace attempted. Configurations that exercise the hard
> machinery are not rare; two-drone traces simply cannot express them.
>
> **Generalizing a trace over its start time is free if the step lemmas already
> are.** [`step_cfgB`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/ExamplesThree.lean#L190) and [`step_cfgC`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/ExamplesThree.lean#L232) were stated for an arbitrary clock from the
> beginning, so [`run_cfgB_at`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/ThreeConverge.lean#L493) was the same induction with `t` carried through.

### 6.4 C3 — the bound is attained at `n = 2`

[`Dpss/Sharpness.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Sharpness.lean). `2 − 1/n` is an *upper* bound; a proof that lost an `ε`
would still be a correct theorem, about `2 − 1/n + ε`, and nobody would notice.
One configuration cannot settle it — [`spread`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Examples.lean#L484) converges at `5/4` against `3/2`.
A family can:

| step | time | state |
|---|---|---|
| 0 | `0` | `0 →`, `ε →` |
| 1 | `1 − ε` | `1−ε →`, `1 ←` |
| 2 | `1 − ε/2` | both at `1 − ε/2 ←` |
| 3 | `3/2 − ε` | both at `1/2`, separating |

Drone 0 is outside `[0, 1/2]` for the whole return leg, so at `3/2 − 2ε` it
sits at `1/2 + ε`. [`bound_sharp`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Sharpness.lean#L341) follows.

> **The witness is a *right*-synchronization failure.** The natural guess is
> that the straggler is a drone still left of its interval. It is not: drone 0
> overshoots to the right. Sharpness of a bound stated as "left and right
> synchronized" can be witnessed by either half, and the other half was the one
> to look at.
>
> **A family is not much harder than an instance, if the instance was done
> right.** The `ε`-trace is the [`spread`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Examples.lean#L484) trace with `1/4` replaced by a
> variable; what it cost was replacing `norm_num` with `linarith` and naming the
> two hypotheses the arithmetic needs.

### 6.5 C3′ — the bound is attained at every `n`

[`Dpss/SharpnessGeneral.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/SharpnessGeneral.lean). The plan sized this as the paper's `n`-drone
cascade: `2(n−1)` phases, each a configuration given by a formula in the phase
index, each needing a minimum over `Fin n` computed by hand.

**The trace is never computed.** Start the drones on a **ladder** — drone `i`
at `i·d`, all heading right. No pair is co-located, so while all head right
every gap stays exactly `d`. Now suppose some drone turns left:
[`coLocated_of_turnsLeft`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/PairBalance.lean#L209) says it is co-located with its right-hand neighbour,
so its gap is zero, and the gap is `d`. Contradiction — *unless the drone has
no right-hand neighbour*. So the first drone to turn is `n−1`, and Lemma 3.1
puts its turn at `rightEnd (n−1) = 1`. Positions track time exactly while
headings are fixed, so **nothing turns before `1 − (n−1)d`** ([`ladder_state`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/SharpnessGeneral.lean#L132)).

Drone 0 therefore heads right past `1/n` until at least then, and Lemma 3.1's
other half sends it all the way back to `0` without stopping. It re-enters
`[0, 1/n]` only at `2w − 1/n ≥ 2 − 2(n−1)d − 1/n`, which tends to `2 − 1/n`.

At `n = 1` the statement is false and must be: a single drone's interval is the
whole perimeter, so `2 − 1/1 = 1` is not attained.

> **A lower bound needs less than a trace.** The trace says where every drone is
> at every moment; the theorem needs only that *one* drone be outside its
> interval at *one* late instant. Sizing the item from the construction rather
> than from the statement is what made it look like a session's work.

---

## 7. Group D — cleanup

### 7.1 D1 — two superseded definitions removed

`Config.Together` was superseded by [`CoLocated`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Events.lean#L88) (stated on an *adjacent* pair
via the gap, which is what every later result quotes) and `Config.Valid` by
`Config.Invariant` (which adds escort coherence and is what is proved
preserved). Neither had a use left.

> A dead predicate in a development like this is not neutral: it invites a
> reader to prove something about the wrong one.

### 7.2 D2 — resolved by not doing it

The ACL2 team reported that `have-met` phrased over execution *history* "drew
heavily on human intuition about system behaviour and was difficult to work
with in a mechanized proof", and that recasting it as a **locally checkable**
predicate was what made their development tractable. [`HaveMetBy`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/LeftSyncLemmas.lean#L195) here is the
history-shaped one, and D2 was a contingency in case Lemma 3.5 or 3.7 became
unwieldy.

Neither did. Lemma 3.5 produces the meeting index directly, and Lemma 3.7
consumes it by taking the last co-located index at or before the deadline —
which is a search over history, and a two-line one.

> Worth recording precisely because the ACL2 experience predicted otherwise:
> what made history painful for them was presumably ACL2's untyped first-order
> setting, not the shape of the predicate. An experience report from one prover
> is evidence about that prover, not a law.

---

## 8. The hypotheses, and what they cost

Both headline theorems are conditional. There are exactly two conditions.

**`c.Invariant`** — on the perimeter, in order, escorts coherent. Proved
preserved by every step and proved satisfiable. This is well-formedness, not an
assumption doing mathematical work.

**`c.ApartOnBoundaries`** — *a co-located pair heading apart sits on the
boundary it shares* — on the **starting** configuration only;
[`apartOnBoundaries_run`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/InductionStep.lean#L93) propagates it, and two lemmas discharge it for anything
realistic ([`apartOnBoundaries_of_not_coLocated`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/InductionStep.lean#L101),
[`apartOnBoundaries_of_dir_const`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/InductionStep.lean#L107)).

Why is it needed? Because it is **false as a pointwise fact about arbitrary
configurations**. [`Dpss/Counterexample.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Counterexample.lean) builds the refutation: four drones
stacked at one point, the two middle ones each escorting the *outward*
neighbour, leaves the middle pair heading apart nowhere near their shared
boundary. So it is an invariant, proved preserved in [`Dpss/Reachable.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Reachable.lean), and
a genuine condition on the start.

> **The parts of a paper proof that a formalization has to *add* are usually not
> the hard steps. They are the sentences the author did not write.** This is the
> second instance in the project; "by symmetry" (§5.8) was the first.
>
> **When a case analysis stubbornly refuses to close, suspect the goal.**
> Building the counterexample took less time than the failed proof, and unlike
> the attempt it produced something permanent.

---

## 9. What is outside the package

`STATUS.md` §4 is authoritative. Nothing in the package is open; what follows
never was in it.

**Algorithm B** — wrong estimates, a changing perimeter, drones joining or
leaving. That is where the original 2008 proof broke and where the open problem
lives.

**The phase-1 refutation** the original plan listed is *unreachable* here
rather than unfinished. `PLAN-original.md` §5.2 proposed refuting the false
`3T` bound; that bound is about estimate propagation, which is Algorithm B.
Recorded as a planning error, not a gap.

**A backlog item, which is new work:** `PLAN.md` **E1** proposes a Rust
implementation of Algorithm A verified against this specification in
[Verus](https://github.com/verus-lang/verus). The interesting difficulty is
named there — Lean's model is over `ℝ`, Verus reasons about executable code, so
a faithful port must either carry rationals explicitly or prove the
discretization sound against the real-valued spec. Proving the *invariant*
alone (drones stay on the perimeter, never overtake) would already be worth
having: it is a real safety property of real code.

---

## 10. Reading paths

**To believe Theorem 2.1** (≈ 1 hour): [`Synchronization.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Synchronization.lean) → §5.7 and
[`Convergence.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean) → §5.6 and [`InductionStep.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/InductionStep.lean) → `STATUS.md` §4.

**To believe non-Zeno** (≈ 30 minutes): §3's Lemma 3.1 and [`Turning.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Turning.lean) →
§4.2 and [`TurnSpacing.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/TurnSpacing.lean) → §4.3 and [`NonZenoProof.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/NonZenoProof.lean).

**To extend it**: add `PLAN.md`, [`RealTime.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/RealTime.lean) (§5.6) if your work reasons
between events, [`PairBalance.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/PairBalance.lean) and [`BalanceInvariant.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/BalanceInvariant.lean) (§5.1–5.2) if it
touches the convergence chain, and `INSIGHTS.md` §11 for Lean mechanics that
each cost a debugging round.

**To audit it**: add `STATUS.md` §6 (the axiom audit, machine output verbatim),
[`Counterexample.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Counterexample.lean) (§8), [`Priority.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Priority.lean) and [`Nondeterminism.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean) (§6.1–6.2),
and the three non-vacuity instances in §2.

---

## 11. Lessons that outlived their items

Collected from `INSIGHTS.md`, which has the long forms.

1. **A wrong definition supporting a flawless proof is the real danger**, and
   only a concrete case will find it (§3).
2. **The escort is emergent, not primitive.** Uniform speed means a co-located
   pair pointing the same way *stays* co-located. That deleted a planned layer.
3. **Invariants enforced by construction beat invariants inherited** — six
   hypotheses deleted, six stronger theorems (§3).
4. **When a source hand-waves, find your own route before reconstructing
   theirs** (§4.3).
5. **Derive the invariant; do not guess its shape** (§5.2).
6. **The index that is right for 500 theorems can be wrong for one.** Add a
   second, thin index with an explicit bridge — do not migrate (§5.6).
7. **Before writing the third interpolation argument, write the interpolation
   lemma** (§5.6).
8. **Measure a gap before restating it** (§6.1).
9. **Size an item from the statement, not from the construction** (§6.5).
10. **Re-read the source before executing a plan item** (§6.2).
11. **Every uniqueness theorem about a specification needs a non-vacuity
    witness** (§6.2).
12. **An audit document must audit itself.** Scripted prose edits failed
    silently three times while the commit proceeded; section-boundary edits
    never have. `scripts/refresh_status.py` now self-checks what it writes, and
    `scripts/audit.py` had a bug of its own.

---

## 12. The commits

| commit | what landed |
|---|---|
| *earlier* | the model, the invariants, the traces, **A** (non-Zeno), **B1–B4**, **B7** |
| `20c9295` | [`RealTime.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/RealTime.lean) — reading the system between events |
| `5816c6a` | [`InductionStep.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/InductionStep.lean) — **B5**, Lemma 3.7 |
| `7753781` | [`Convergence.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean) — **B6**, Theorem 2.1 |
| `9c2214d` | **D1** — `Config.Together` and `Config.Valid` removed |
| `b48f409` | [`Sharpness.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Sharpness.lean) — **C3**, the bound attained at `n = 2` |
| `8fe6e93` | [`ThreeConverge.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/ThreeConverge.lean) — **C2**, three drones that settle |
| `e969f31` | [`Priority.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Priority.lean) — **C1**, measuring the nondeterminism |
| `e97593b` | [`SharpnessGeneral.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/SharpnessGeneral.lean) — **C3′**, attained at every `n` |
| `ff6a26c` | [`Nondeterminism.lean`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean) — **C1′**, the relation and its collapse |

Documentation commits are interleaved; `CHANGELOG.md` has the narrative.

---

## 13. If you only remember five things

1. **[`nonZeno`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/NonZenoProof.lean#L127) and [`convergesBy`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean#L199) are the theorems.** The first is what the ACL2
   mechanization had to assume; the second is the paper's Theorem 2.1, with the
   constant exactly `2 − 1/n`.
2. **The constant is exact and attained** — [`bound_sharp_general`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/SharpnessGeneral.lean#L330), for every
   `n ≥ 2`. No sharper analysis exists, which is why B6's induction had to lose
   nothing.
3. **It holds for every resolution of the nondeterminism**, because on every
   reachable state there is only one ([`convergesBy_of_isRun`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean#L384)).
4. **Two hypotheses**, both on the starting configuration, both discharged by
   one-line lemmas for anything realistic (§8).
5. **`STATUS.md` §4 is the honest part.** Read it before quoting anything from
   §3.

---

## 14. Symbol index

Every declaration named in this guide, with a deep link to the line that
declares it. Regenerate with `python3 scripts/refresh_guide_links.py` after any
edit that moves declarations — it rewrites every link in this file and fails if
a line anchor has gone stale.

<!-- BEGIN:INDEX -->
| Declaration | File | Line |
|---|---|---|
| [`AllSync`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Synchronization.lean#L84) | `Synchronization.lean` | 84 |
| [`ApartOnBoundaries`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/InductionStep.lean#L89) | `InductionStep.lean` | 89 |
| [`ApartOnBoundary`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Reachable.lean#L47) | `Reachable.lean` | 47 |
| [`AtSeparation`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Events.lean#L113) | `Events.lean` | 113 |
| [`BothLeftApart`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/PairBalance.lean#L140) | `PairBalance.lean` | 140 |
| [`CoLocated`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Events.lean#L88) | `Events.lean` | 88 |
| [`HaveMetBy`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/LeftSyncLemmas.lean#L195) | `LeftSyncLemmas.lean` | 195 |
| [`Invariant`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Coherence.lean#L341) | `Coherence.lean` | 341 |
| [`IsRun`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean#L310) | `Nondeterminism.lean` | 310 |
| [`MeetLeft`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L90) | `Step.lean` | 90 |
| [`MeetRight`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L86) | `Step.lean` | 86 |
| [`PairPhase`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/BalanceInvariant.lean#L85) | `BalanceInvariant.lean` | 85 |
| [`SepLeft`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L82) | `Step.lean` | 82 |
| [`SepRight`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L77) | `Step.lean` | 77 |
| [`StepRel`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean#L302) | `Nondeterminism.lean` | 302 |
| [`advance`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Dynamics.lean#L41) | `Dynamics.lean` | 41 |
| [`allSync_of_time`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean#L207) | `Convergence.lean` | 207 |
| [`apartOnBoundaries_of_dir_const`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/InductionStep.lean#L107) | `InductionStep.lean` | 107 |
| [`apartOnBoundaries_of_not_coLocated`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/InductionStep.lean#L101) | `InductionStep.lean` | 101 |
| [`apartOnBoundaries_run`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/InductionStep.lean#L93) | `InductionStep.lean` | 93 |
| [`approach_converges_general`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean#L256) | `Convergence.lean` | 256 |
| [`borderTime`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/NextEvent.lean#L55) | `NextEvent.lean` | 55 |
| [`bound_sharp`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Sharpness.lean#L341) | `Sharpness.lean` | 341 |
| [`bound_sharp_general`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/SharpnessGeneral.lean#L330) | `SharpnessGeneral.lean` | 330 |
| [`cfgB_converges_general`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean#L309) | `Convergence.lean` | 309 |
| [`cfgS`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/ThreeConverge.lean#L61) | `ThreeConverge.lean` | 61 |
| [`coLocated_of_turnsLeft`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/PairBalance.lean#L209) | `PairBalance.lean` | 209 |
| [`convergesBy`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean#L199) | `Convergence.lean` | 199 |
| [`convergesBy_of_isRun`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean#L384) | `Nondeterminism.lean` | 384 |
| [`dir_left_since_of_never_coLocated`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/TurnPersistence.lean#L89) | `TurnPersistence.lean` | 89 |
| [`escortDir`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Events.lean#L123) | `Events.lean` | 123 |
| [`escortDirLeft`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L97) | `Step.lean` | 97 |
| [`escortsCoherent_step`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Coherence.lean#L236) | `Coherence.lean` | 236 |
| [`exists_coLocated_within_one`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Meeting.lean#L340) | `Meeting.lean` | 340 |
| [`exists_firstLeft`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Meeting.lean#L236) | `Meeting.lean` | 236 |
| [`exists_firstRight`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Meeting.lean#L202) | `Meeting.lean` | 202 |
| [`exists_lastBefore`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/RealTime.lean#L183) | `RealTime.lean` | 183 |
| [`gap_advance`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Dynamics.lean#L93) | `Dynamics.lean` | 93 |
| [`invariant_run`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Coherence.lean#L354) | `Coherence.lean` | 354 |
| [`invariant_step`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Coherence.lean#L347) | `Coherence.lean` | 347 |
| [`isRun_eq_run`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean#L365) | `Nondeterminism.lean` | 365 |
| [`ladder_state`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/SharpnessGeneral.lean#L132) | `SharpnessGeneral.lean` | 132 |
| [`leftEnd_le_pos_of_pairBalance`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/PairBalance.lean#L119) | `PairBalance.lean` | 119 |
| [`leftSyncAt_next`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/InductionStep.lean#L141) | `InductionStep.lean` | 141 |
| [`leftSyncAt_zero`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/RealTime.lean#L332) | `RealTime.lean` | 332 |
| [`leftSync_next_of_coLocated_left`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/InductionStep.lean#L123) | `InductionStep.lean` | 123 |
| [`leftSync_of_escorting`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/BalanceInvariant.lean#L295) | `BalanceInvariant.lean` | 295 |
| [`leftSync_of_reached_boundary`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/BalanceInvariant.lean#L311) | `BalanceInvariant.lean` | 311 |
| [`leftSync_of_separation`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/BalanceInvariant.lean#L286) | `BalanceInvariant.lean` | 286 |
| [`legitDir_unique`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean#L265) | `Nondeterminism.lean` | 265 |
| [`meetTime`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Dynamics.lean#L127) | `Dynamics.lean` | 127 |
| [`newDir`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L105) | `Step.lean` | 105 |
| [`newDirMeetFirst_leaves_interval`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Priority.lean#L262) | `Priority.lean` | 262 |
| [`nonZeno`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/NonZenoProof.lean#L127) | `NonZenoProof.lean` | 127 |
| [`nonZeno_of_isRun`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean#L392) | `Nondeterminism.lean` | 392 |
| [`nonneg_of_endpoints`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/RealTime.lean#L63) | `RealTime.lean` | 63 |
| [`not_strictly_inside_of_grouped`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean#L170) | `Nondeterminism.lean` | 170 |
| [`onPerimeter_run`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Coherence.lean#L361) | `Coherence.lean` | 361 |
| [`pinned_of_balance_zero`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/PairBalance.lean#L400) | `PairBalance.lean` | 400 |
| [`pos_eq_of_time_le`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/RealTime.lean#L206) | `RealTime.lean` | 206 |
| [`pos_sub_eq_of_dirConst`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/NonZeno.lean#L88) | `NonZeno.lean` | 88 |
| [`rightSyncAt_iff_leftSyncAt_mirror`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean#L79) | `Convergence.lean` | 79 |
| [`rightSync_iff_leftSync_mirror`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Mirror.lean#L706) | `Mirror.lean` | 706 |
| [`run`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L219) | `Step.lean` | 219 |
| [`run_cfgB_at`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/ThreeConverge.lean#L493) | `ThreeConverge.lean` | 493 |
| [`separationTime`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Schedule.lean#L87) | `Schedule.lean` | 87 |
| [`someDroneTurns_step`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/EventsTurn.lean#L282) | `EventsTurn.lean` | 282 |
| [`spread`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Examples.lean#L484) | `Examples.lean` | 484 |
| [`spread_converges_general`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean#L282) | `Convergence.lean` | 282 |
| [`step`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Step.lean#L151) | `Step.lean` | 151 |
| [`step_cfgB`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/ExamplesThree.lean#L190) | `ExamplesThree.lean` | 190 |
| [`step_cfgC`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/ExamplesThree.lean#L232) | `ExamplesThree.lean` | 232 |
| [`sync_at_of_time`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Convergence.lean#L191) | `Convergence.lean` | 191 |
| [`timeToNextEvent`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/NextEvent.lean#L274) | `NextEvent.lean` | 274 |
| [`time_gap_of_consecutive_turns`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/TurnSpacing.lean#L63) | `TurnSpacing.lean` | 63 |
| [`triple_not_reachable`](https://github.com/lgwagner/dpss_lean/blob/main/Dpss/Nondeterminism.lean#L453) | `Nondeterminism.lean` | 453 |
<!-- END:INDEX -->
