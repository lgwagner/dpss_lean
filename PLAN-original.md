# Formalizing DPSS in Lean 4 — plan of work

**Status:** Stage 0 in progress. **Scope agreed 2026-09-12:** Stages 0–3 committed,
Stage 4 (the proof itself) as a stretch goal. Algorithm A only. Continuous real
time. Teaching-grade commentary throughout.

This document is written to be readable without prior Lean or hybrid-systems
background. If something here is opaque, that is a defect in this document —
say so and I will fix it.

---

## 0. What we are actually trying to do

The DPSS algorithm coordinates a team of drones patrolling a perimeter. Its 2008
convergence proof was published, cited for a decade, and was **wrong**. A model
checker found the error in 2019; a corrected hand proof appeared in 2020–21; part
of it was mechanized in ACL2 in 2022.

We are going to rebuild the corrected proof in Lean 4 — a proof assistant that
checks every inference mechanically, so that a gap like the 2008 one cannot hide.

The headline target is **Theorem 2.1** of Avigad–van Doorn:

> Assuming all the drones have the correct estimates, they are all synchronized
> at time `2 − 1/n`.

---

## 1. The model, precisely

From arXiv:2008.04262 §2, read in full on 2026-09-12. Normalization: the
perimeter is the **unit interval `[0,1]`**, drones move at **one unit per unit
time**.

- `n` drones numbered `1..n` left to right. Drone `i`'s interval is
  `[(i−1)/n, i/n]`. The **common endpoint** of drones `i` and `i+1` is `i/n`.
- Each drone has a direction `d = ±1` and an estimate `((a,ℓ),(b,m))`:
  estimated left endpoint, drones to the left, estimated right endpoint, drones
  to the right. Note `a` and `b` need **not** lie in `[0,1]` — estimates can be
  wrong in the general algorithm.
- Derived quantities: interval size `I = (b−a)/(ℓ+m+1)`, left endpoint
  `L = a + ℓI`, right endpoint `R = a + (ℓ+1)I`.

### 1.1 The three events — note the terminology carefully

A drone continues in its current direction until one of these occurs:

| Event | Meaning |
|---|---|
| **Border event** | The drone reaches the true left (or right) border of `[0,1]`. It corrects that endpoint estimate, sets the drone count on that side to 0, and turns around. |
| **Meet event** | Two drones occupy the same position. Each adopts the other's far-side estimate, incrementing the drone count by 1. They now agree on their intervals, and both set direction toward their **common endpoint**. |
| **Separation event** | Two drones travelling together (with consistent estimates) reach their common endpoint. One reverses so each stays in its own interval. |

A **bounce event** is the special case where a meet and a separation coincide —
i.e. two drones meet *exactly at* their common endpoint.

> ⚠️ The original brief (§3.4) used "bounce" for what the paper calls a **border
> event**. That is a terminology collision that would have corrupted the Lean
> model. This plan uses the paper's vocabulary throughout.

Drones starting together share estimates at time 0.

### 1.2 Two places the algorithm is genuinely underspecified

The paper flags both (§2, final paragraph):

1. Whether a drone's estimate must be consistent with its own position (e.g. can
   a drone at `0.9` believe the right border is at `0.8`?).
2. When **three or more** drones come together and three are inside the middle
   drone's interval, the middle drone may escort *either* neighbour.

Point 2 means the true dynamics are **nondeterministic**. The strongest possible
upper bound quantifies over all resolutions of that choice. **Design consequence:**
the Lean step relation should be a `Prop`-valued *relation*, not a function.
Neither issue arises in phase 2, so Algorithm A can be modelled deterministically
if the relational version proves painful — but relational is the better target.

---

## 2. Why "Algorithm A only" is the right first scope

Algorithm A is the case where every drone already holds correct estimates. The
estimate machinery `(a,ℓ,b,m)` then collapses: every drone already knows its true
interval, and the dynamics reduce to (quoting §3):

> when two drones meet, they escort each other to their common endpoint and then
> separate.

That is a dramatic simplification — no estimate propagation at all. It is also
the case with a known-true, known-**sharp**, already-mechanized target.

Algorithm B (wrong estimates, changing perimeter, drones joining/leaving) is
where the 2008 proof broke and where the open problem lives. Out of scope here.

---

## 3. The proof skeleton to reproduce

From §3 of the paper. By symmetry it suffices to prove **left** synchronization.

- **Lemma 3.1** — if drone `j` is moving right, then the next time it changes
  direction it is at or to the right of its right endpoint. (Symmetric for left.)
- **Lemma 3.2** — if drone `j` is left synchronized and `j`, `j+1` separate at
  their common endpoint, then `j+1` is left synchronized. *This is the 2008
  argument, stated correctly.*
- **Lemma 3.3** — `j`, `j+1` together moving left and `j` left synchronized ⟹
  `j+1` left synchronized.
- **Lemma 3.4** — `j < n` at or right of its right endpoint, moving right, left
  synchronized ⟹ `j+1` left synchronized.
- **Lemma 3.5** — for every `j < n`, drones `j` and `j+1` **have met by time 1**.
  The uniform timing result that makes the bound `n`-independent.
- **Lemma 3.6** — a "no direction change since the last separation" persistence
  result, used to reach back to an earlier separation time.
- **Lemma 3.7** — **the key inductive step.** If `1..j` are left synchronized and
  `j`, `j+1` have met, then `j+1` is left synchronized by time `t + 1/n`.

Drone 1 is always left synchronized; all pairs have met by time 1; induction
gives drones `1..i` left synchronized at `1 + (i−1)/n`. At `i = n` this is
`2 − 1/n`. ∎

**`have met by time t`** is the load-bearing definition: drones `j` and `j+1`
have met by time `t` if either they started together moving in the same
direction, or they have been involved in a meet or bounce event.

### 3.1 Theorem 2.2 — missing from the original brief

> If all drones start with **incorrect** estimates, and all have correct
> estimates at time `t`, then all are synchronized by time `t + 1 − 1/n`.

Proved via **Lemma 3.8**. The "incorrect" hypothesis is necessary: Theorem 2.1
being sharp means 2.2 fails if drones start correct. This is what turns the
`4 − 1/n` phase-1 lower bound into the `5 − 3/n` total.

---

## 4. Non-Zeno: the most valuable thing in this project

**This section was upgraded on 2026-09-12 after reading the ACL2 paper in full.**

Non-Zeno — no infinitely many events in finite time — looked like tedious
well-definedness plumbing. It is in fact the part where a Lean development has
something genuinely new to offer.

The ACL2 mechanization **does not prove it**. Their event-stepping function
`step-time` was admitted as a partial function via `def::ung`, and the
assumption `(step-time-always-terminates)` appears as an explicit hypothesis in
their top-level convergence theorem. They are candid about it and invite exactly
this improvement: *"given sufficient interest and resources, a proper measure
for step-time could be developed and used to dispatch this assumption, further
strengthening our results."*

Avigad–van Doorn, meanwhile, **do** supply the argument (§2) but do not
mechanize it. The two artifacts are complementary, and the gap between them is
precisely what Stage 1 produces.

So the target is sharper than "reproduce a known result":

> Formalize the AvD non-Zeno argument in Lean and thereby discharge the
> hypothesis that the only existing mechanization has to assume.

That stands on its own even if Stage 4 never closes.

The paper's argument, which we get to reuse rather than invent:

1. Suppose infinitely many events with least upper bound `T`.
2. Some drone changes direction infinitely often in `(T−ε, T)`.
3. **Key step:** if drone `j+1` makes two consecutive left turns, drone `j` must
   turn right in between. So infinite turning propagates to all drones.
4. Take `ε < 1/2n`. At `T−ε` either some adjacent pair is more than `2ε` apart,
   or an end drone is more than `ε` from its border. In each case the relevant
   drone turns at most once in `(T−ε, T)`. Contradiction.

Step 3 is a clean standalone lemma and a good early Lean target.

---

## 5. Staged deliverables

| Stage | Deliverable | Status |
|---|---|---|
| 0 | Toolchain, Mathlib project, papers read, `[verify]` items resolved | in progress |
| 1 | Definitional layer: state, events, trajectory, order invariant, non-Zeno — **now carries independent novelty, see §4** | |
| 2 | `Synchronized` defined; Theorem 2.1 **stated** (with `sorry`) | |
| 3 | Sanity tests at `n = 2, 3`; refute the false phase-1 bound | |
| 4 | Close the `2 − 1/n` proof | stretch |
| 5 | Phase-1 upper bound — **open problem, not in scope** | — |

Useful small cases from §2: `n = 1` is trivial; `n = 2` gives correct estimates
by time 2 and synchronization by `2.5`, both sharp; **`n = 3` is the first
interesting case**.

---

## 6. Risks

- **Sharpness leaves no slack.** `2 − 1/n` is attained. Any analysis that loses
  an `ε` will not close.
- **Rationals vs reals.** ACL2 has no reals, so their model is rational-valued.
  Our `ℝ` model is strictly more faithful, but it also means their termination
  intuitions do not transfer for free.
- **Localize, don't globalize.** The ACL2 team reported that predicates defined
  over execution *history* or extrapolated futures "tended to draw heavily on
  human intuition" and resisted mechanization; locally checkable invariants over
  a drone and its neighbour worked. `have met` is exactly such a predicate.
  A Lean development that reasons globally risks stalling the way bounded model
  checking did.
- **The escort is not a point event.** A meet begins joint motion of indefinite
  duration, and escorts cascade. Modelling a co-moving group as first-class is
  likely better than N coincidentally-equal positions.
- **Definitions can be vacuous.** Hence Stage 3 before Stage 4: if the model
  cannot refute the known-false phase-1 bound, the model is wrong.
