# PLAN — work yet to be done

The forward-looking roadmap. `STATUS.md` records what **is** proved;
`INSIGHTS.md` records what was **learned**; this file records what to do
**next** and in what order.

> The original scoping document — the decisions taken at the start, and the one
> planning error they contained — is `PLAN-original.md`.

**How to use this.** Work the critical path top to bottom. Each item states the
target, the ingredients that already exist, the approach, and a **done-when**
that is checkable. Do not start an item whose dependencies are open.

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

**Hazard.** Watch the index-versus-time friction (see §4 below). The conclusion
is a bound on *time*, so state it that way and let indices follow.

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
