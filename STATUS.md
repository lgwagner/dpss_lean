# DPSS formalization — status

**Generated:** 2026-09-12
**Commit at time of writing:** `b5de46913cbd`
**Toolchain:** Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release), Mathlib v4.33.1

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
| Event *scheduling* (`timeToNextEvent`, `step`) | **not started** |
| Runs / event sequences | **not started** |
| Non-Zeno | **not started** |

---

## 3. What is actually proved

51 theorems across 3 files (193 + 228 + 216 lines). All `sorry`-free; see §6.

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

---

## 4. What is **not** proved — read this part

This is the honest gap list. Nothing below is done.

1. **There is no dynamics yet.** The three events exist as individual state
   transformations, and `advance` exists as motion. **Nothing sequences them.**
   There is no `timeToNextEvent`, no `step`, and no notion of a run. Everything
   proved so far is about *one* flight or *one* event in isolation.
2. **Non-Zeno is not started.** This is the headline opportunity (§5) and it
   needs the run machinery from (1) first.
3. **`Synchronized` is not defined**, so Theorem 2.1 is not even *stated* yet.
   That is Stage 2.
4. **No sanity tests.** Nothing has been instantiated at `n = 2` or `n = 3`.
   The model has not been run even once. Until Stage 3 there is no evidence the
   definitions are non-vacuous *as a system* — only the two local checks in §3.2.
5. **None of Lemmas 3.1–3.8 are formalized.** The proof skeleton is recorded in
   `PLAN.md` §3 but not touched in Lean.
6. **The nondeterminism is not modelled.** When three or more drones converge,
   the paper leaves open which neighbour the middle drone escorts. My events are
   currently deterministic per-pair. This does not bite in phase 2, but a fully
   faithful model needs a relation, not a function.
7. **Unused definitions.** `Config.OnPerimeter`, `Config.Valid`,
   `Config.Together`, `Config.escortDir`, `Config.AtSeparation`,
   `AtLeftBorder` / `AtRightBorder` are defined but no theorem constrains them
   yet. In particular **nothing proves that only drone `0` can be at the left
   border** — that needs the ordering invariant plus `OnPerimeter`, and is a
   good next target.
8. **Algorithm B is entirely out of scope** — wrong estimates, changing
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

All 51 theorems:

```
'DPSS.Dir.flip_left' does not depend on any axioms
'DPSS.Dir.flip_right' does not depend on any axioms
'DPSS.Dir.flip_flip' does not depend on any axioms
'DPSS.Dir.sign_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Dir.sign_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Dir.sign_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
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
'DPSS.Config.doSeparate_dir_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.doSeparate_dir_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.not_approaching_doSeparate' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.doBorder_dir_of_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.doBorder_dir_of_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.sepRate_eq_zero_of_escorting' depends on axioms: [propext, Classical.choice, Quot.sound]
'DPSS.Config.coLocated_advance_of_escorting' depends on axioms: [propext, Classical.choice, Quot.sound]
```

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

```
b5de469  2026-09-12  feat: motion between events, and the ordering invariant
fbeab29  2026-09-12  docs: ACL2 convergence proof is conditional on unproved termination
29d8b41  2026-09-12  feat: scaffold Lean 4 + Mathlib project and add the geometry layer
c4b40fd  2026-09-12  docs: verify brief against arXiv:2008.04262, fix one error, add Theorem 2.2
0d789d5  2026-09-12  docs: add Lean formalization plan for DPSS Algorithm A
0dc5ffd  2026-09-11  Add files via upload
bcdb11f  2026-09-11  Create README.md
971617b  2026-09-11  Initial commit
```

---

## 9. Next steps, in order

1. Prove the currently-unused predicates are constrained: only drone `0` can be
   at the left border, only drone `n-1` at the right. Closes gap (7) above.
2. `timeToNextEvent` — the minimum over all pending events — and prove it
   **positive** when no event is currently due. This is the local half of
   non-Zeno and the first thing ACL2 could not do.
3. `step` and runs: iterate event-to-event.
4. Non-Zeno proper, following AvD §2. The load-bearing step is: *if drone `i+1`
   makes two consecutive left turns, drone `i` must turn right in between.*
5. Then Stage 2: define `Synchronized`, state Theorem 2.1.
