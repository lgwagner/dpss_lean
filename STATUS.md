# DPSS formalization — status

<!-- BEGIN:META -->
**Generated:** 2026-09-12  
**Commit at time of writing:** `d9e7f2fde864`  
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
| 1 | Definitional layer: state, events, trajectory, order invariant, non-Zeno | **in progress** — see below |
| 2 | `Synchronized` defined; Theorem 2.1 stated | not started |
| 3 | Sanity tests at `n = 2, 3`; refute the false phase-1 bound | not started |
| 4 | Close the `2 − 1/n` proof | stretch, not started |
| 5 | Phase-1 upper bound (open problem) | explicitly out of scope |

Stage 1 broken down:

| Piece | State |
|---|---|
| Geometry: assigned intervals, endpoints | done |
| `Config` (time, positions, directions) | done |
| Motion between events (`advance`) | done |
| Ordering invariant under motion | **done — main result so far** |
| The three events as state transformations | done |
| Per-event scheduling (when each event comes due) | done |
| Combining them into `timeToNextEvent` (a minimum) | done |
| `timeToNextEvent` strictly positive (local non-Zeno) | done |
| `step` and runs | **not started** |
| Non-Zeno proper (uniform lower bound on steps) | **not started** |
| Runs / event sequences | **not started** |
| Non-Zeno | **not started** |

---

## 3. What is actually proved

<!-- BEGIN:COUNTS -->
**86 theorems**, all `sorry`-free, across 5 files (`Basic.lean` 199 lines, `Dynamics.lean` 228 lines, `Events.lean` 232 lines, `NextEvent.lean` 315 lines, `Schedule.lean` 215 lines).
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

---

## 4. What is **not** proved — read this part

This is the honest gap list. Nothing below is done.

1. **There is still no running system.** `timeToNextEvent` now exists and is
   proved strictly positive, but **nothing iterates it**. There is no `step`
   function and no notion of a run, so every result so far still concerns *one*
   flight or *one* event in isolation. This is the immediate next target.

2. **Non-Zeno is not proved, and `timeToNextEvent_pos` is not it.** Strictly
   positive steps can still sum to a finite time — that is exactly how Zeno
   behaviour works. What is missing is a uniform lower bound on step size. This
   is the headline opportunity (§5) and it remains open.

3. **A modelling claim, now half proved.** `NextEvent.lean` computes
   `borderTime` for *every* drone, including interior ones for which no border
   event is reachable — a neighbour is in the way. The worry is that such a
   number becomes the minimum, making `timeToNextEvent` report a deadline with
   no event behind it.

   The **local** steps are now proved:
   `droneNextTime_le_borderTime_of_next_left` (a leftward drone's border
   deadline is at least its left neighbour's deadline),
   `droneNextTime_le_borderTime_of_self_right` (the mirror image, when the
   right neighbour also heads right), and
   `meetTime_le_borderTime_of_approaching` (when a pair is closing, the left
   drone's deadline is realised by the meet — a genuine event). Chaining these
   anchors every spurious border deadline at an end drone, whose border event
   *is* genuine.

   **The chaining itself is not formalized.** The statement that wants proving
   is "`timeToNextEvent` is attained by a genuine event", and it needs argmin
   machinery that does not exist here yet. So the argument is no longer bare
   prose, but it is not finished either.

   Worth recording how this went: my first attempt at the rightward lemma was
   simply **false**, and Lean caught it. I had forgotten that `droneNextTime j`
   only ever consults the pair `(j, j+1)`, so a meet with the *left* neighbour
   is accounted for at `j-1` and never at `j`. The asymmetry between the two
   lemmas is real, not an oversight.

4. **`Synchronized` is not defined**, so Theorem 2.1 is not even *stated* yet.
   That is Stage 2.

5. **No sanity tests.** Nothing has been instantiated at `n = 2` or `n = 3`.
   The model has not been run even once. Until Stage 3 there is no evidence the
   definitions are non-vacuous *as a system* — only the local checks in §3.2
   and §3.4.

6. **None of Lemmas 3.1–3.8 are formalized.** The proof skeleton is recorded in
   `PLAN.md` §3 but not touched in Lean.

7. **The nondeterminism is not modelled.** When three or more drones converge,
   the paper leaves open which neighbour the middle drone escorts. My events
   are currently deterministic per-pair. This does not bite in phase 2, but a
   fully faithful model needs a relation, not a function.

8. **Unused definitions.** `Config.Together` and `Config.Valid` are defined but
   no theorem uses them.

9. **Algorithm B is entirely out of scope** — wrong estimates, changing
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
'DPSS.leftEnd_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.rightEnd_last' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.together_refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.together_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
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
```

**86/86 clean — `sorryAx` appears zero times.**
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

1. ~~Constrain the border predicates.~~ **Done** — `Schedule.lean`.
2. ~~`timeToNextEvent`, proved strictly positive.~~ **Done** — `NextEvent.lean`.
3. Finish gap 3: chain the local domination lemmas into "`timeToNextEvent` is
   attained by a genuine event".
4. `step` and runs: iterate event-to-event.
5. Non-Zeno proper, following AvD §2. The load-bearing step is: *if drone `i+1`
   makes two consecutive left turns, drone `i` must turn right in between.*
6. Then Stage 2: define `Synchronized`, state Theorem 2.1.
