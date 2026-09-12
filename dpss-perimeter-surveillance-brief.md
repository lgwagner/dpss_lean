# DPSS — Decentralized Perimeter Surveillance System

**A literature and algorithm brief, oriented toward a Lean formalization.**

Compiled 2026-09-12 from public sources. Every claim below is sourced in §7. Sourcing
caveat: this brief was assembled from abstracts, HTML renderings and talk slides rather
than from careful reading of every primary PDF. Items marked **[verify]** are the ones
worth checking against the primary text before any of them is turned into a Lean
`theorem` statement.

---

## 1. TL;DR

DPSS is a multi-UAV perimeter-patrol coordination protocol published by Kingston, Beard
and Holt in 2008. Its selling point is that agents communicate *only when they physically
meet* — no radio network, no central planner — and yet the team provably converges in
finite time to an evenly-spaced sweeping pattern.

The reason it is interesting as a formalization target is that **the published
convergence proof was wrong**, and the correction took three separate efforts across
three communities:

| Year | Who | What |
|---|---|---|
| 2008 | Kingston, Beard, Holt (BYU → AFRL) | Algorithm + hand proof, claimed total convergence bound 5T |
| 2019 | Davis, Humphrey, Kingston (Collins Aerospace + AFRL) | AGREE model checker finds Lemma 1 false |
| 2020–21 | Avigad, van Doorn (CMU / Bonn) | Corrected hand proof; sharp phase-2 bound `2 − 1/n`; phase-1 lower bounds |
| 2022 | Greve, Davis, Humphrey (Collins + AFRL) | Mechanized proof of the phase-2 result in ACL2 |

So there is a known-good target (the phase-2 theorem, already mechanized once), a
known-bad historical artifact (the 2008 Lemma 1) that makes a nice regression test, and a
genuinely **open problem** (an n-independent phase-1 upper bound) sitting at the end of
the road.

---

## 2. Provenance and the AFRL connection

The canonical citation is:

> D. B. Kingston, R. W. Beard, R. M. Holt. *Decentralized Perimeter Surveillance Using a
> Team of UAVs.* IEEE Transactions on Robotics **24**(6):1394–1404, 2008.

The work originated at BYU's MAGICC lab. An earlier conference version — with Casbeer and
McLain added as authors — appeared as AIAA 2005-5831 at AIAA GNC 2005, and that version
already covers the harder case (perimeter that grows or shrinks, agents joining or
leaving). The preprint was cleared through AFRL as **AFRL-RB-WP-TP-2007-324** (DTIC
accession **ADA474905**), Air Vehicles / Aerospace Systems Directorate, Wright-Patterson
AFB.

Derek Kingston subsequently moved to AFRL, which is why the algorithm is routinely
described as "the AFRL perimeter surveillance algorithm" even though the original journal
paper credits NASA and AFOSR sponsorship rather than AFRL. **[verify]** the exact
sponsorship line if attribution matters. Laura Humphrey (AFRL) is the through-line on all
the later verification work.

---

## 3. The algorithm

### 3.1 Physical setup

- A perimeter, modeled as a line segment with a *left* and a *right* endpoint. (The
  closed-loop case is handled by cutting the loop; the segment is the case everything is
  proved about.)
- `N ≥ 1` agents, indexed `0 … N−1` left to right. The ordering is an invariant: agents
  never pass each other.
- All agents move at identical constant speed. Each agent has a position and a direction
  `d = ±1`.
- Segment length `S = P / N` where `P` is perimeter length. Agent `i`'s assigned segment
  is `[i·S, (i+1)·S]`.
- **Communication happens if and only if two agents are co-located.** The model reduces
  "within radio range" to the extreme case of coincidence. This is the whole point of the
  algorithm and the source of all the difficulty.

### 3.2 Two normalizations in the literature — do not mix them

| | Avigad–van Doorn | Greve–Davis–Humphrey (ACL2) |
|---|---|---|
| Perimeter | unit interval `[0,1]` | length `P`, traversal time `T` |
| Speed | 1 unit / unit time | normalized so *one segment* takes 1 time unit |
| Full traversal | time 1 | time `T = N` |
| Steady-state period | `2/n` | 2 |
| Convergence bound | `2 − 1/n` | `2N − 1` |

These agree: `(2N − 1)` segment-times = `2 − 1/N` perimeter-times. Pick one at the top of
the Lean development and never switch. The AvD normalization is cleaner for stating
theorems; the ACL2 one is cleaner for stating the steady-state period.

### 3.3 Coordination variables

Each agent carries an estimate

```
((a, ℓ), (b, m))
```

- `a` — believed position of the left perimeter endpoint
- `ℓ` — believed number of agents to its left
- `b` — believed position of the right perimeter endpoint
- `m` — believed number of agents to its right

From `(a, ℓ, b, m)` an agent computes its own assigned subsegment. Note that `ℓ + m + 1`
is its estimate of `N`; agents do not separately know the team size.

### 3.4 Events

Three event types change an agent's state:

1. **Bounce.** The agent reaches a perimeter endpoint. It reverses direction and updates
   the corresponding endpoint estimate to ground truth.
2. **Meet.** Two agents become co-located. They exchange coordination variables: *the
   left one adopts the right-hand estimate `(b, m)` of the drone to its right, with `m`
   incremented by 1; the right one symmetrically adopts the left-hand estimate `(a, ℓ)`,
   with `ℓ` incremented by 1.* This is the only information transfer in the system.
3. **Escort / split.** After a meet, the pair computes the shared border between their
   two assigned segments. If they are not already there, they travel *together* to it —
   the "escort" — and only then separate, each turning back into its own segment.

The escort step is what makes the protocol work and what makes the proof awkward: a
"meeting" is not an instantaneous event but the start of a joint motion of indefinite
duration, and escorts can cascade (a pair mid-escort can meet a third agent).

### 3.5 Algorithm A

**Algorithm A is the case where all agents already hold correct coordination variables.**
The perimeter is fixed and known; the team roster is fixed and known. Only the *positions
and directions* are arbitrary.

The claim is that from any initial configuration of positions and directions, the team
converges to the steady state.

In the ACL2 mechanization the coordination variables are **omitted from the model
entirely**, precisely because A assumes they are already correct. That is a significant
simplification and a good reason to make A the first Lean target.

### 3.6 Algorithm B

**Algorithm B is the general case.** Initial estimates may be wrong, the perimeter length
may change (grow or shrink), and agents may be added to or lost from the team. Agents
discover the endpoints by bouncing off them and discover the team size by meeting
neighbors and propagating counts.

Algorithm B is what makes the system practically interesting — it is the reason the AIAA
2005 abstract emphasizes "perimeter growth (expanding or contracting) and
insertion/deletion of team members" — and it is where the proof broke.

Under B, convergence decomposes into two phases (Avigad–van Doorn's framing):

- **Phase 1** — from start until *every* agent holds correct estimates. This is an
  information-propagation problem: endpoint truth enters the system only at bounces and
  spreads only through meetings.
- **Phase 2** — from "everyone correct" until synchronized. Once estimates are correct,
  this is exactly Algorithm A.

### 3.7 What "converged" means

Two equivalent-ish formulations appear:

- **Synchronization (AvD).** An agent is *left synchronized* at time `t` if from `t`
  onward it never goes left of its assigned left endpoint; *right synchronized*
  symmetrically; *synchronized* = both. The team is synchronized when all agents are.
- **Periodicity (ACL2).** Each agent forever returns to the same location every 2 time
  increments (in the segment-normalized units).

Synchronization is the more useful one to formalize — it is a safety property with a
"from now on" quantifier, whereas periodicity is an exact-orbit statement. **[verify]**
whether the two are actually equivalent in the papers or whether periodicity is derived
from synchronization plus an argument about phase.

---

## 4. The proof history

### 4.1 The 2008 claim

KBH proved, or believed they proved:

> **Phase 1.** Within 3 time units (i.e. `3T`, three full perimeter traversals), all
> agents have correct information.
> **Phase 2.** Once all agents have correct information, all are synchronized within 2
> more time units.
> **Total.** Convergence within `5T`, independent of `n`.

The paper carried a convincing-looking proof and was supported by high-fidelity
simulation (four UAVs, 3.1 km perimeter, 6-DOF nonlinear dynamics, 50 m turn radius,
~370 m comms range) and, per the later literature, hardware flight testing. It has been
cited heavily for two decades and spawned a substantial follow-on literature on perimeter
surveillance under communication constraints (Acevedo, Maza, Arrue, Ollero et al.).

### 4.2 2019 — the model checker says no

> J. A. Davis, L. R. Humphrey, D. B. Kingston. *When Human Intuition Fails: Using Formal
> Methods to Find an Error in the "Proof" of a Multi-agent Protocol.* CAV 2019, 366–375.

They encoded DPSS in **AGREE** (the Collins Aerospace / Loonwerks compositional
contract-based model checker for AADL) and found that **Lemma 1 of the 2008 paper is
false**. The argument had not fully accounted for initial conditions and for interaction
effects at *both* ends of the perimeter simultaneously.

Reported numbers: the lemma's claimed `3T` phase-1 bound does not hold; the CAV write-up
cites a true figure of roughly `3.67T`, while Avigad's slides describe the Davis et al.
`n = 3` counterexample as reaching about `3.5`. **[verify]** — these are probably
different configurations (one a specific counterexample, one a bound), but the
discrepancy should be resolved before either number is quoted in a Lean docstring.

Cost of the check: bounded model checking only. Parameters had to be fixed (drone-count
estimates capped at 20), and `n = 6` took roughly **20 days on 40 cores**. This is the
single best argument in the whole story for wanting a theorem prover instead.

### 4.3 2020–21 — the corrected hand proof

> J. Avigad, F. van Doorn. *Progress on a Perimeter Surveillance Problem.* arXiv:2008.04262;
> IEEE, 2021.

Results:

- **Theorem 2.1 (phase 2, sharp).** Assuming all drones have correct estimates, they are
  all synchronized at time `2 − 1/n`. This *vindicates* the phase-2 half of the KBH
  conjecture and sharpens it.
- **Theorem 2.3 (phase 1 and total, lower bounds).** For every `n ≥ 3` and `ε > 0` there
  is a start configuration in which the drones do not have correct estimates before time
  `4 − 1/n − ε`, and are not fully synchronized before time `5 − 3/n − ε`. This beats the
  Davis et al. counterexample and definitively kills the `3` of the original phase-1
  claim.
- Some partial progress toward a phase-1 *upper* bound.

Note the shape of the final result: total convergence is bounded **below** by roughly
`5 − 3/n`, which is tantalizingly close to the originally claimed `5`. The original number
may well be right; the original *proof* is not.

### 4.4 2022 — mechanization in ACL2

> D. Greve, J. Davis, L. Humphrey. *A Mechanized Proof of Bounded Convergence Time for the
> Distributed Perimeter Surveillance System (DPSS) Algorithm A.* arXiv:2205.11697; ACL2
> Workshop 2022.

Mechanizes the Avigad–van Doorn phase-2 argument for **Algorithm A only**, in ACL2, with
bound `2N − 1` segment-times. Two invariants carry the proof:

- **`have-met`** — two UAVs have met by time `t` if either they started co-located moving
  in the same direction, or they have been involved in a meet or bounce event. Defined as
  a locally checkable predicate (`have-met-Left-p` and its mirror) over an agent and its
  immediate neighbor, rather than as a global relation — this is what made the
  mechanization tractable.
- **`synchronized`** — an agent is left/right synchronized at `t` if beyond that point it
  never goes left/right of its left/right segment endpoint.

The paper also discusses three general-purpose ACL2 utilities developed for expressing
and reasoning about the model. Worth reading for the modeling patterns even though ACL2's
untyped first-order setting is quite unlike Lean's.

### 4.5 What is still open

**A rigorous, `n`-independent upper bound for phase 1.** Nobody has one. The lower bound
is `4 − 1/n`; the original claim was `3`; the truth is somewhere at or above `4 − 1/n`
with no proved ceiling. Equivalently: **Algorithm B has no settled convergence bound** —
only Algorithm A / phase 2 does.

This means a Lean project has a natural two-tier structure: reproduce the settled result,
then have an actual open problem to attack with the formal machinery already in place.

---

## 5. Notes toward a Lean formalization

### 5.1 What kind of object this is

DPSS is a **hybrid system**: continuous piecewise-linear motion punctuated by discrete
events (bounce, meet, escort-split). The usual traps apply.

- **Time.** Real-valued. Everything is piecewise linear with breakpoints at events, so
  `ℝ` with explicit event lists is plausible, but Zeno behavior has to be ruled out or
  designed away. The ACL2 model appears to sidestep this by working in normalized units
  where events land on a tractable lattice — **[verify]** how, because that decision is
  the single biggest fork in the design.
- **State.** `Fin N → (position : ℝ) × (dir : Bool) × (estimate : ℝ × ℕ × ℝ × ℕ)`. For
  Algorithm A the estimate component drops out entirely.
- **Order invariant.** Agents never swap; `i < j → pos i ≤ pos j` for all time. This
  should be one of the first lemmas and it makes `Fin N` indexing meaningful throughout.
- **The escort.** The awkward part. A meeting is not a point event — it initiates joint
  motion until a computed border is reached, and escorts compose. Modeling a "group of
  co-located agents moving together" as a first-class notion rather than as N separate
  agents that happen to coincide is probably the right call, and is roughly what the
  `have-met` invariant is doing.

### 5.2 Suggested targets, in order

1. **Definitional layer + order invariant.** Get the model down, prove agents stay
   ordered and that the state evolution is well-defined (total, deterministic, non-Zeno).
   This is most of the work and none of the glory.
2. **Theorem 2.1 / DPSS-A.** Correct estimates ⇒ synchronized by `2 − 1/n`. Known to be
   true, known to be sharp, and already mechanized once in ACL2, so a failure to close it
   is a signal about the Lean development rather than about the mathematics.
3. **The 2008 Lemma 1 as a negative test.** Formalize the Davis et al. counterexample and
   show the `3T` phase-1 bound is refutable. Cheap, high-value: it exercises the
   definitions against a known-false statement, which is the standard way to catch a
   model that is vacuously satisfiable.
4. **Theorem 2.3 lower bounds.** Construct the bad families and prove `4 − 1/n` and
   `5 − 3/n`. These are explicit constructions — likely more computation than insight,
   and a good stress test for whether the model is usable.
5. **Phase 1 upper bound.** Open. Do not start here.

### 5.3 Hazards

- The two normalizations (§3.2) differ by a factor of `N`. Mixing them silently produces
  statements that look right and are off by `N`.
- "Correct estimates" is a *global* predicate but the useful invariants are *local*. The
  ACL2 proof's localization trick is the load-bearing idea; a Lean development that
  reasons globally will probably stall the same way bounded model checking did.
- The synchronization property is `∃ t, ∀ t' ≥ t, P t'`. Both quantifier alternations
  matter; the bound is on the `t`, and sloppiness here is how the original proof went
  wrong in the first place.
- Sharpness of `2 − 1/n` means there is no slack to give away in the analysis. An
  argument that loses even an `ε` will not close.

---

## 6. Why this is a good Lean target

- The statement is elementary — real numbers, finitely many agents, piecewise linear
  motion — so Mathlib coverage is not the bottleneck.
- There is a **known error in the published proof**, which makes it a genuine test of
  whether the formalization catches what human review did not.
- There is a **prior mechanization** in a different system (ACL2), so the proof is known
  to be formalizable and there is a reference decomposition to borrow or deliberately
  depart from.
- There is an **open problem** at the end of it that formal machinery might plausibly help
  with, rather than a purely retrospective exercise.
- Avigad — one of the two authors of the corrected proof — is a Lean person, and the
  arXiv paper notes that Greve "has recently formalized the proof presented here
  (personal communication)". It is worth checking whether a Lean formalization already
  exists or was attempted before duplicating effort. **[verify]**

---

## 7. Bibliography

**Primary algorithm**

- D. B. Kingston, R. W. Beard, R. M. Holt. *Decentralized Perimeter Surveillance Using a
  Team of UAVs.* IEEE Trans. Robotics 24(6):1394–1404, 2008.
  <https://ieeexplore.ieee.org/document/4682728/>
  BYU open copy: <https://scholarsarchive.byu.edu/facpub/1224/>
- T. McLain, R. W. Beard, D. Kingston, R. S. Holt, D. W. Casbeer. *Decentralized Perimeter
  Surveillance Using a Team of UAVs.* AIAA GNC 2005, AIAA 2005-5831.
  <https://scholarsarchive.byu.edu/facpub/1911>
- AFRL-RB-WP-TP-2007-324 / DTIC ADA474905 (preprint).
  <https://apps.dtic.mil/sti/tr/pdf/ADA474905.pdf>
  (403s to automated fetchers; mirror at <https://archive.org/details/DTIC_ADA474905>)

**Verification thread**

- J. A. Davis, L. R. Humphrey, D. B. Kingston. *When Human Intuition Fails: Using Formal
  Methods to Find an Error in the "Proof" of a Multi-agent Protocol.* CAV 2019, 366–375.
  <https://link.springer.com/chapter/10.1007/978-3-030-25540-4_20>
- J. Avigad, F. van Doorn. *Progress on a Perimeter Surveillance Problem.* arXiv:2008.04262.
  <https://arxiv.org/abs/2008.04262> · HTML: <https://ar5iv.labs.arxiv.org/html/2008.04262>
- J. Avigad, talk slides.
  <https://www.andrew.cmu.edu/user/avigad/Talks/perimeter_surveillance.pdf>
- D. Greve, J. Davis, L. Humphrey. *A Mechanized Proof of Bounded Convergence Time for the
  DPSS Algorithm A.* arXiv:2205.11697; ACL2 Workshop 2022.
  <https://arxiv.org/abs/2205.11697>

**Background cited by the above**

- D. D. Cofer et al. *Compositional Verification of Architectural Models.* NASA Formal
  Methods 2012, 126–140. (This is the AGREE reference.)
- R. S. Boyer, J S. Moore. *A Computational Logic Handbook*, 2nd ed. (ACL2.)

---

## 8. To do before writing Lean

- [ ] Read the 2008 T-RO paper in full; extract the exact statements of Algorithm A and
      Algorithm B and of Lemma 1 as published.
- [ ] Read the CAV 2019 paper; pin down the counterexample configuration and reconcile the
      `3.5` vs `3.67` figures.
- [ ] Read arXiv:2008.04262 in full; transcribe Theorem 2.1, Theorem 2.3 and all
      supporting lemmas with their proofs.
- [ ] Read arXiv:2205.11697 in full; extract the ACL2 model's treatment of time and
      events, and the exact form of `have-met` and the synchronization predicates.
- [ ] Search for an existing Lean formalization (Greve's, or anything in a Mathlib-adjacent
      archive) before starting.
