# PLAN — work yet to be done

The forward-looking roadmap. `STATUS.md` records what **is** proved;
`INSIGHTS.md` records what was **learned**; this file records what to do
**next** and in what order.

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

**416 theorems, all `sorry`-free.** Non-Zeno is proved. Theorem 2.1 is stated
and proved at `n = 1` and for specific `n = 2`, `n = 3` configurations.

| Done | Open |
|---|---|
| A (non-Zeno), B2 (L 3.3, 3.4), B4 (L 3.6), B7 (symmetry) | **B1**, **B3**, B5, B6, C, D |

---

## Critical path

### 1 — B1. Lemma 3.2: `BalanceNonneg`  ⟨**L**⟩

**Target.** `BalanceNonneg c hn i h k` for a pair that has just separated. This
single result completes Lemmas **3.2, 3.3 and 3.4** together, since §3.17 has
all three waiting on it.

**Approach.** Derived in `STATUS.md` §8a — read that first. A three-clause
invariant:

1. `0 ≤ balance`
2. pair heading `(left, right)` ⟹ `balance = 0`
3. `BothLeftApart` ⟹ `pos i = leftEnd i`

Clause 2 is the engine: the balance rate is the **sum** of the two headings
(unlike the gap, which uses the difference), so a pair heading apart holds its
balance *constant*. Entering that state therefore only needs to happen at zero.

**Ingredients — all present.** `pairBalance_advance`,
`pairBalance_eq_zero_of_atSeparation`, `pairBalance_eq_two_mul_separationTime`,
`pairBalance_nonneg_step`, `pinned_of_balance_zero`,
`timeToNextEvent_eq_zero_of_pinned`, `apart_transfer`,
`coLocated_of_turnsLeft`/`_turnsRight`, `newDir_left_cases`/`_right_cases`,
`dir_left_of_newDir_apart` and partner.

**Steps.**
1. State the three-clause invariant as a structure, say `PairPhase`.
2. Preservation, clause 2: split on co-located / apart. Apart is the easy half
   — every event that could deliver `(left, right)` needs this pair co-located,
   so the pair was already in that state. Co-located is §3.21's enumeration.
3. Preservation, clause 3: from clause 2 plus `pinned_of_balance_zero`.
4. Preservation, clause 1: from clause 3 plus
   `timeToNextEvent_eq_zero_of_pinned` (apart) and `pairBalance_nonneg_step`
   (co-located).
5. Chain along a run; feed `leftSync_of_balanceNonneg`.

**Done when.** `leftSync_of_atSeparation` and the Lemma 3.3 / 3.4 statements in
`LeftSyncLemmas.lean` lose their `hnever`/`BothLeftApart` hypotheses.

**Hazard.** Two attempts have already failed by guessing the invariant's shape.
Do not start proving before the three clauses are written down and each one's
*purpose* is clear.

**On completion, record:** which clause turned out to be load-bearing, and
whether the three-clause shape was right or itself needed revising.

---

### 2 — B3. Lemma 3.5: every pair has met by time 1  ⟨**L**⟩

**Target.** `HaveMetBy c hn i h (c.time + 1)` for every adjacent pair.

Independent of B1 — can be done in either order. This is the result that makes
the bound `n`-independent; without it the argument degrades to linear in `n`,
which is what Kingston et al.'s original proof gave.

**Approach (the paper's).** Let `w` be where drone `j` sits when it first heads
right, `z` where `j+1` sits when it first heads left. Total distance covered
before they meet is `2(z − w) − (y − x)`, so they meet by `z − w ≤ 1`.

**Ingredients.** `exists_dir_right_of_dir_left` and its mirror (every drone
eventually turns — this is where non-Zeno pays for itself);
`time_bound_of_dir_left`/`_right` (the quantitative `w` and `z` bounds);
`pos_sub_eq_of_dirConst`; `onPerimeter_run`.

**Steps.**
1. Define the first-turn indices via `Nat.find`, as `exists_first_turn_after`
   already does for a different purpose.
2. Show the pair is approaching once both have turned.
3. Bound the meeting time; conclude `HaveMetBy`.

**Done when.** The statement holds for all `i`, `h`, with no hypothesis beyond
`Invariant`.

**Hazard.** Watch the index-versus-time friction (see item 3 below). The
conclusion is a bound on *time*, so state it that way and let indices follow.

**On completion, record:** whether the paper's distance computation survived
formalization intact, and whether `HaveMetBy` needed to become locally
checkable (D2).

---

### 3 — B5. Lemma 3.7: the `+1/n` inductive step  ⟨M⟩

**Depends on:** B1 (for 3.2/3.3/3.4 unconditional), B3 (for `have met`).

**Target.** Drones `1..j` left synchronized and the pair `(j, j+1)` having met
⟹ `j+1` left synchronized by `t + 1/n`.

**Approach.** Three cases, all of whose tools now exist:
- `j` heading right ⟹ within `1/n` it is at or beyond its right endpoint ⟹
  Lemma 3.4;
- `j` heading left and together with `j+1` ⟹ Lemma 3.3;
- `j` heading left and apart ⟹ Lemma 3.6 reaches back to the last co-location,
  then Lemma 3.2.

**Hazard — resolve before starting.** `LeftSync` is indexed by **step**, but
`+1/n` bounds **time**. A drone can cross its right endpoint mid-step, so the
natural index arrives too late. Add a time-indexed
`LeftSyncFrom (T : ℝ) := ∀ j, T ≤ (run j).time → leftEnd i ≤ (run j).pos i`
alongside the existing predicate, and relate the two, *before* attempting the
lemma.

**On completion, record:** whether the time-indexed predicate should have been
the primary one from the start.

---

### 4 — B6. Assemble Theorem 2.1  ⟨S⟩

**Depends on:** B5, and B7 (done).

**Steps.**
1. Base case: drone `0` is always left synchronized — `leftEnd_zero` plus
   `onPerimeter_run`. Not yet stated; it is two lines.
2. Induct with B5: drones `1..i` left synchronized by `1 + (i−1)/n`.
3. At `i = n`: left synchronization by `2 − 1/n`.
4. Right synchronization via `rightSync_iff_leftSync_mirror` (B7).
5. Discharge `ConvergesBy`, which needs both halves.

**Done when.** `theorem convergesBy (hi : c.Invariant) : ConvergesBy c hn`
exists and `scripts/audit.py` passes.

**On completion, record:** the final shape of the induction, and how far the
assembled bound is from the paper's `2 − 1/n` — it should be exact.

---

## Off the critical path

Worth doing, in no particular order, and none of it blocks Theorem 2.1.

| | Item | Size |
|---|---|---|
| **C1** | Model the nondeterminism as a *relation*. §3.20 shows it biting — `newDir` currently picks one resolution of the choice the paper leaves open, and every result here inherits that restriction. | M |
| **C2** | A converging `n = 3` trace, and one with a genuine three-way meeting. | M |
| **C3** | An `ε`-family showing the `2 − 1/n` bound is *attained*. The paper asserts it; nothing here checks it. | M |
| **D1** | Remove `Config.Together` (unused) and `Config.Valid` (superseded by `Config.Invariant`). | S |
| **D2** | Consider making `HaveMetBy` locally checkable rather than history-shaped, if B3 or B5 turns unwieldy — the ACL2 team reported this was what made their proof tractable. | M |

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

### B1 — partial

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

## Standing hazards

- **Two attempts at B1 failed by guessing an invariant's shape.** Derive, write
  down, then prove.
- **When a case analysis will not close, suspect the goal.** Building the §3.20
  counterexample took less time than the failed proof did, and produced
  something permanent.
- **`sorry` is never acceptable here** — CI enforces it, and the whole value of
  the artefact is that its claims are checkable.
- **Run `scripts/audit.py` before quoting a theorem count.** It has been wrong
  in commit messages three times.
- **Edit `STATUS.md` by section boundary, not by prose matching.** Four silent
  edit failures so far, each behind a commit message claiming otherwise.
