# A reader's guide to the convergence proof

*Written for a person picking this up cold, or coming back to it after the
session in which Theorem 2.1 was closed.*

`README.md` says what the project is. `STATUS.md` says what is proved and what
is not, and is written to be audited. `INSIGHTS.md` says what the work taught.
`PLAN.md` says what to do next. **This file says how to follow the convergence
proof** — what it claims, how the pieces fit, what to read in what order, and
how to check that any of it is true.

---

## 1. The claim, in one box

```lean
theorem convergesBy {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) : ConvergesBy c hn
```

where

```lean
def ConvergesBy (c : Config n) (hn : 0 < n) : Prop :=
  ∀ (i : Fin n) (j : ℕ),
    c.time + (2 - 1 / (n : ℝ)) ≤ (c.run hn j).time →
      leftEnd i ≤ (c.run hn j).pos i ∧ (c.run hn j).pos i ≤ rightEnd i
```

Read it as: **from `2 − 1/n` after the start, every drone is inside its own
assigned segment `[i/n, (i+1)/n]`, and stays there.** That is Theorem 2.1 of
Avigad–van Doorn, for Algorithm A, in continuous real time, for every `n`.

There is a stronger version that quantifies over *instants* rather than over
event indices:

```lean
theorem sync_at_of_time (hn) (hi) (hab) (i : Fin n) (p : ℕ) (s : ℝ)
    (hs : c.time + (2 - 1 / (n : ℝ)) ≤ s) (hin : c.InStep hn p s) :
    leftEnd i ≤ c.posIn hn p i s ∧ c.posIn hn p i s ≤ rightEnd i
```

This is the form the paper states. `posIn p i s` is where drone `i` is at real
time `s`, read inside step `p`; `InStep p s` says `s` really is in that step.
See §5.

### What the two hypotheses mean

`hi : c.Invariant` is the standing well-formedness condition used everywhere in
this development: every drone is on the perimeter, the drones are in
left-to-right order, and escorting pairs have a non-negative separation
deadline. It is **proved preserved by every step** (`invariant_run`) and
**proved satisfiable** by concrete configurations, so it is neither an
assumption smuggled through nor a vacuity.

`hab : c.ApartOnBoundaries` is the one condition beyond that: *a co-located
pair heading apart sits on the boundary it shares.* It is a condition on the
**starting** configuration only — `apartOnBoundaries_run` propagates it. Two
lemmas discharge it for anything you would actually start from:

```lean
apartOnBoundaries_of_not_coLocated   -- no two adjacent drones on the same point
apartOnBoundaries_of_dir_const       -- every drone heading the same way
```

Why is it needed at all? Because it is **false as a pointwise fact about
arbitrary configurations** — `Dpss/Counterexample.lean` builds four drones
stacked at one point that refute it — and the proof of Lemma 3.2 needs it. The
paper never states it because, about the states the algorithm reaches, it is
obvious. See §6.

---

## 2. Check it yourself, in four commands

```bash
lake build                        # Lean 4.33.1 + Mathlib v4.33.1; expect exit 0
grep -rn "sorry" Dpss/            # only prose mentions, never a tactic
python3 scripts/audit.py          # every theorem's axiom dependencies
python3 scripts/refresh_status.py # regenerate STATUS.md's generated blocks
```

`scripts/audit.py` fails if any theorem depends on `sorryAx`, and it runs in
CI. The interesting line to look for is

```
'DPSS.Config.convergesBy' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Those three are Lean's standard axioms. `sorryAx` is not there, and it cannot
be hidden.

If you want to confirm the theorem is not vacuous — that its hypotheses are
satisfiable — the development does it for you three times over, at the bottom
of `Dpss/Convergence.lean`:

```lean
Examples.approach_converges_general        -- n = 2, drones apart
Examples.spread_converges_general          -- n = 2, all heading the same way
ExamplesThree.cfgB_converges_general       -- n = 3, a pair co-located and heading apart
```

The third matters most: it satisfies `ApartOnBoundaries` while *exercising* the
case rather than avoiding it. And all three reproduce, from the general
theorem, conclusions that were previously established by tracing the runs by
hand.

---

## 3. The shape of the argument

Avigad–van Doorn give it in three lines:

> Since drone 1 is always left synchronized and all the drones have met by time
> 1, by induction on `i < n` we have that drones `1, …, i` are left synchronized
> at time `1 + (i−1)/n`. Taking `i = n` yields the theorem.

Everything in this development exists to make those three lines' three inputs
true. Here they are, with their homes.

| | Statement | Where |
|---|---|---|
| **Base** | Drone `0` is left synchronized always | `leftSyncAt_zero`, `Dpss/RealTime.lean` |
| **Meeting** | Every adjacent pair is co-located within 1 unit of time — **Lemma 3.5** | `exists_coLocated_within_one`, `Dpss/Meeting.lean` |
| **Step** | Left synchronization passes to the right-hand neighbour at a cost of `1/n` — **Lemma 3.7** | `leftSyncAt_next`, `Dpss/InductionStep.lean` |
| **Other half** | Right synchronization is left synchronization of the reflected run | `rightSyncAt_iff_leftSyncAt_mirror`, `Dpss/Convergence.lean` |

And the supporting chain, which is where the real work is:

| Lemma | Statement | Where | Conditional? |
|---|---|---|---|
| 3.1 | A rightward drone turns only at or beyond its right endpoint | `Dpss/Turning.lean` | no |
| 3.2 | A pair separating at their shared boundary passes left sync on | `leftSync_of_separation`, `Dpss/BalanceInvariant.lean` | no |
| 3.3 | A pair escorting leftward passes left sync on | `leftSync_of_escorting`, same file | no |
| 3.4 | The left drone at the shared boundary passes left sync on | `leftSync_of_reached_boundary`, same file | on the phase invariant, which is proved preserved |
| 3.5 | Every pair meets within time 1 | `Dpss/Meeting.lean` | no |
| 3.6 | A leftward drone has been leftward since the pair last met | `Dpss/TurnPersistence.lean` | no |
| 3.7 | The `+1/n` inductive step | `Dpss/InductionStep.lean` | needs `ApartOnBoundaries` |

Underneath all of it sits **non-Zeno** (`Dpss/NonZenoProof.lean`): the clock
along a run is unbounded. Without it a drone could sit still for ever, never
turning and never leaving the perimeter, and Lemma 3.5 would be false. It is
also the property the published ACL2 mechanization *assumes* — see `STATUS.md`
§5, which is the part of this project that is a contribution rather than a
reproduction.

### The arithmetic

Drone `i` is left synchronized at `1 + i/n` in this development's 0-based
indexing (the paper's `1 + (i−1)/n` under the index shift). At `i = n − 1`:

```
1 + (n−1)/n = 2 − 1/n
```

Exactly. Nothing is rounded and no ε is lost, which is not an aesthetic point —
see §7.

---

## 4. What to read, in order

**If you want to believe the theorem** (about an hour):

1. `Dpss/Synchronization.lean` — what "synchronized" means and why checking
   event times is enough. Short.
2. `Dpss/Convergence.lean` — the assembly. It is ~90 lines of actual proof; the
   rest is the mirror transfer and the concrete checks.
3. `Dpss/InductionStep.lean` — Lemma 3.7, the only genuinely intricate step.
4. `STATUS.md` §4 — the gap list, so you know what you have *not* just read.

**If you want to extend it** (add `PLAN.md` and):

5. `Dpss/RealTime.lean` — you will need it for anything that reasons between
   events, and the design decision it embodies is explained in §5 below.
6. `Dpss/PairBalance.lean` and `Dpss/BalanceInvariant.lean` — the balance is
   this development's replacement for the paper's Figure 2, and Lemmas 3.2–3.4
   all bottom out in it.
7. `INSIGHTS.md` §11 — Lean mechanics, each of which cost a debugging round.

**If you are auditing** (add):

8. `STATUS.md` §6 — the full axiom audit, machine output, verbatim.
9. `Dpss/Counterexample.lean` — a lemma that read as obvious and is false, kept
   because the counterexample is permanent and the failed proof was not.
10. `Dpss/Priority.lean` — how much of the model's event-priority order is a
    real modelling choice. The answer is much less than the documents used to
    claim; see §8.

---

## 5. The one new idea: reading the system between events

This is the design decision worth understanding, because it is the only place
where the formalization needed a structure the paper does not have.

Every predicate in this development is indexed by **step number**. A run is
`run hn 0, run hn 1, …`, and "drone `i` never goes left of its endpoint from
step `k` on" is `LeftSync c hn i k`. That is the natural index for an
event-driven model, and it carried about 500 theorems without complaint.

**Lemma 3.7 is the exception.** Its conclusion is a deadline in *real time*
(`by time t + 1/n`), and its proof reads a drone's heading and position at the
instant `t`, which in general lies strictly inside a step — previous event
before it, next event after it. And the step-indexed reading is genuinely
weaker there: a drone heading right can sit left of its endpoint mid-step and
be back inside its interval by the next event, so a step-indexed Lemma 3.7 does
not merely look inelegant, it looks false.

`Dpss/RealTime.lean` adds the missing layer, with no choice and no partial
function:

```lean
posIn p i s = pos_p i + sign (dir_p i) * (s − time_p)     -- where drone i is at time s
InStep p s  = time_p ≤ s ∧ s ≤ time_{p+1}                  -- s is inside step p
```

`exists_lastBefore` — which is non-Zeno again — supplies a step containing any
given instant, so nothing is lost by never having to name *the* step of `s`.

Two facts carry the whole layer.

**A linear function nonnegative at both ends of an interval is nonnegative
throughout it** (`nonneg_of_endpoints`, three lines). Within a step every
quantity of interest is affine in time — a position moves at `±1`, a gap at
`sepRate`, a balance at the sum of the two headings. So *every* "it is true at
the events, therefore it is true in between" argument in this development is
that one lemma with different names substituted.

**If the clock does not move between two indices, no drone moves either**
(`pos_eq_of_time_le`). Steps of zero length are routine here — an event already
due costs no time — so `time_m ≤ time_k` does **not** give `m ≤ k`. But it does
give equal positions, and in every place a proof wanted the index inequality,
what it actually needed was the position.

The layer is ~340 lines and touches nothing else. Making real time the primary
index instead would have taxed 500 theorems to pay for one proof; `PLAN.md`
records that question and its answer.

---

## 6. `ApartOnBoundaries`, and why a source never has to state it

Lemma 3.2 — a pair separating at their shared boundary hands left
synchronization to the right-hand drone — needs to know, at the moment the pair
is co-located and heading apart, that they are standing **on** the boundary
they share. Otherwise the balance that drives the whole argument can start
negative.

About the states the algorithm reaches, that is obvious: the only way to end up
co-located and heading apart is to have just separated, and separation happens
at the boundary.

About configurations *in general* it is false. `Dpss/Counterexample.lean`
builds it: four drones stacked at one point, the two middle ones each escorting
the *outward* neighbour, leaves the middle pair heading apart nowhere near
their shared boundary. So the statement is an **invariant**, not a pointwise
fact; `Dpss/Reachable.lean` proves it preserved by a step; and
`Dpss/InductionStep.lean` propagates it along a run from a hypothesis on the
start.

This is the second time in the project that something a source treats as
beneath mention turned out to be real formalization work. The first was "by
symmetry", which needed a reflection map proved to commute with `advance`,
`step` and `run`, reflection laws for every local quantity and every event, and
invariance of the global deadline (`Dpss/Mirror.lean`, 737 lines).

> The parts of a paper proof that a formalization has to *add* are usually not
> the hard steps. They are the sentences the author did not write.

---

## 7. Why sharpness matters, and what was checked

`2 − 1/n` is an **upper** bound. A proof that lost an ε somewhere would still be
a correct theorem — about `2 − 1/n + ε` — and you would never notice.

The paper says the bound is attained. `Dpss/Sharpness.lean` checks that at
`n = 2` with a family parameterised by `ε`: the paper's own worst case, drone
`0` at the left border and drone `1` a distance `ε` ahead, both heading out.

| step | time | state |
|---|---|---|
| 0 | `0` | `0 →`, `ε →` |
| 1 | `1 − ε` | `1−ε →`, `1 ←` — the right drone bounces |
| 2 | `1 − ε/2` | both at `1 − ε/2 ←` — met, escorting back |
| 3 | `3/2 − ε` | both at `1/2` — separating, synchronized |

Drone `0` is outside `[0, 1/2]` for the whole return leg, so at the instant
`3/2 − 2ε` it sits at `1/2 + ε`. Shrinking `ε` pushes that instant as close to
`3/2 = 2 − 1/2` as you like:

```lean
theorem bound_sharp (B : ℝ) (hB : B < 2 - 1 / (2 : ℝ)) :
    ∃ c : Config 2, c.Invariant ∧ c.ApartOnBoundaries ∧ c.time = 0 ∧ …
```

— some configuration satisfying both standing conditions still has a drone
outside its own interval at an instant at or after `B`. **No smaller constant
is correct.**

A detail worth knowing if you go looking: the witness is a *right*
synchronization failure. The natural guess is that the straggler is a drone
still left of its interval; it is not. Drone `0` overshoots to the right and
does not come back until `3/2 − ε`.

This is checked at `n = 2`. The general-`n` construction needs an `n`-drone
cascade and is `C3′` in `PLAN.md`.

---

## 8. What is honestly not done

`STATUS.md` §4 is the authoritative list and is deliberately longer than the
list of things that are. **The work package is complete** — every item in it,
including the two that were re-sized along the way. What follows is what sits
outside it.

**Algorithm B is out of scope**, and always was: wrong estimates, a changing
perimeter, drones joining or leaving. That is where the original 2008 proof
broke and where the open problem still lives.

**The phase-1 refutation the original plan listed is unreachable here**, not
merely unfinished. It concerns estimate propagation, which is Algorithm B; this
development models Algorithm A, where estimates are correct by assumption and
absent from `Config`. Recorded as a planning error rather than a gap.

**And a backlog item, not a gap:** `PLAN.md` E1 proposes a Rust implementation
verified against this specification in Verus. The interesting difficulty is
named there — Lean's model is over `ℝ`, Verus reasons about executable code —
and proving the *invariant* alone (drones stay on the perimeter, never overtake)
would already be worth having.

### The nondeterminism, since it was the last thing standing

The paper deliberately leaves open which neighbour a middle drone escorts when
three or more converge. Two files close it.

`Dpss/Priority.lean` measured the event-priority order: for every pair of
events that can be due at one drone at one instant, two combinations are
impossible, five agree, and exactly one differs — the paper's *bounce*, where
the alternative provably walks a drone off its own left endpoint.

`Dpss/Nondeterminism.lean` then models the rest as a **relation**. `LegitDir`
admits every legitimate heading update, with the paper's open case genuinely
open; `StepRel` is one step of the relation and `IsRun` a trajectory. And then:

```lean
theorem isRun_eq_run … : IsRun c hn f → ∀ k, f k = c.run hn k
theorem convergesBy_of_isRun … -- Theorem 2.1, for every trajectory
```

The relation collapses to the function. The two escort headings differ exactly
when the meeting point lies strictly inside the middle drone's interval —
word for word the paper's "three of them are within the middle drone's
interval" — and `not_strictly_inside_of_grouped` shows that configuration
cannot arise: the right-hand pair forces the drone to head right, and then the
left-hand pair contradicts every case.

Which is exactly what the paper asserts and does not prove: *"our upper bound
only concerns phase 2, where these issues do not arise."*

`ExamplesThree.triple` keeps it honest — a configuration where the open clause
really does admit two headings, so the uniqueness theorem is not a theorem
about our own definition.

## 9. The session, commit by commit

Twelve commits took the project from "Theorem 2.1 is stated but proved only at
`n = 1`" to "Theorem 2.1 is proved, sharp at every `n`, and independent of the
resolution of the paper's nondeterminism". Each is self-contained and builds
clean.

| commit | what landed |
|---|---|
| `20c9295` | `Dpss/RealTime.lean` — reading the system between events (§5) |
| `5816c6a` | `Dpss/InductionStep.lean` — **Lemma 3.7** |
| `7753781` | `Dpss/Convergence.lean` — **Theorem 2.1** |
| `9c2214d` | removed `Config.Together` and `Config.Valid`, both superseded |
| `b48f409` | `Dpss/Sharpness.lean` — the bound is attained (§7) |
| `8fe6e93` | `Dpss/ThreeConverge.lean` — three drones that start out of position and settle, via a genuine three-way meeting |
| `e969f31` | `Dpss/Priority.lean` — measuring the nondeterminism (§8) |
| `0ae43be` | `STATUS.md`, `PLAN.md`, `INSIGHTS.md`, `README.md` brought up to date |
| `be1079a` | this guide |
| `e2ad74f` | `CHANGELOG.md` |
| `e97593b` | `Dpss/SharpnessGeneral.lean` — **C3′**, the bound attained at every `n` |
| `ff6a26c` | `Dpss/Nondeterminism.lean` — **C1′**, the step relation and its collapse |

`594 theorems`, all `sorry`-free, across 33 files.

---

## 10. If you only remember four things

1. **`convergesBy` is the theorem**, it holds for every `n`, the constant is
   exactly `2 − 1/n`, and `bound_sharp` shows no smaller constant would do.
2. **Two hypotheses**: the standing `Invariant`, proved preserved and proved
   satisfiable; and `ApartOnBoundaries` on the starting configuration, which
   two one-line lemmas discharge for anything realistic.
3. **The real-time layer exists for exactly one proof.** If you are adding
   something that reasons between events, use `posIn`/`InStep` and
   `nonneg_of_endpoints`; if you are not, ignore them.
4. **`STATUS.md` §4 is the honest part.** Read it before quoting anything from
   §3.
