# Changelog

What changed, when, and what it cost. Newest first.

Each entry is the account you would want after a `git pull`: what landed, the
few things worth knowing that are not obvious from the diff, and — the part
that matters most in a project like this — **what was not finished, and why**.

The long forms live elsewhere: `STATUS.md` for what is proved, `PLAN.md` for
what is next, `INSIGHTS.md` for what the work taught, `GUIDE.md` for how to
follow the convergence proof.

---

## 2026-09-12 (later) — the work package, closed

The two items the Theorem 2.1 entry below left open are done. **Every item in
the work package is complete.** 594 theorems, all `sorry`-free.

### What landed

| | |
|---|---|
| **C3′** Sharpness at every `n` | `bound_sharp_general` — no `B < 2 − 1/n` is correct, for any `n ≥ 2` |
| **C1′** Nondeterminism as a relation | `convergesBy_of_isRun` — Theorem 2.1 for every trajectory of `StepRel` |

### Both were re-sized, and then shrank again

The entry below re-sized C1′ from `M` to `L` and kept C3′ at `M`, in each case
budgeting for the construction the paper describes. Both estimates were wrong,
and wrong the same way.

**C3′** was sized for the paper's `n`-drone cascade — `2(n−1)` phases, each a
configuration given by a formula in the phase index. None of it was needed. The
theorem does not ask where every drone is at every moment; it asks that one
drone be outside its interval at one late instant. On a ladder every gap stays
`d` while all drones head right, so a drone that turned left would have to be
co-located with its right-hand neighbour — impossible unless it has none. That
pins the first turn, and Lemma 3.1 does the rest. No configuration in the
cascade is ever written down.

**C1′** was sized for re-proving the development over an arbitrary trajectory,
reaching all 31 files. Re-reading the paper made that unnecessary: the passage
that flags the ambiguity ends *"Neither of these issues bears on the results
reported below, since our upper bound only concerns phase 2, where these issues
do not arise."* That is a claim about reachable states, and it is provable. The
two escort headings differ exactly when the meeting point lies strictly inside
the middle drone's interval — word for word the paper's own description of the
open case — and that configuration cannot arise. So the relation collapses to
the function, and every theorem in the development is already a theorem about
every resolution.

`ExamplesThree.triple` guards against the obvious failure mode: it exhibits a
configuration where the open clause genuinely admits two headings, so the
uniqueness theorem is not a theorem about our own definition.

### What is left

Nothing from the work package. `PLAN.md` now carries a backlog instead: **E1**,
a Rust implementation of Algorithm A verified against this specification in
Verus, with the discretization problem named up front.

---

## 2026-09-12 — Theorem 2.1

**The `2 − 1/n` bound is proved.** The work package is complete except for two
items that were re-sized rather than finished; see below.

Eight commits, `20c9295`…`be1079a`. 565 theorems, all `sorry`-free, CI-enforced.
A reader's guide to the result is `GUIDE.md`, also published at
<https://claude.ai/code/artifact/a1d8ba23-5932-4596-8f43-92bea56c3ad2>.

### What landed

| | |
|---|---|
| **B5** Lemma 3.7 | `leftSyncAt_next`, on a new real-time layer (`Dpss/RealTime.lean`) |
| **B6** Theorem 2.1 | `convergesBy` — every `n`, constant exactly `2 − 1/n`, plus the stronger real-time form `sync_at_of_time` |
| **C3** Sharpness | `bound_sharp` — no `B < 2 − 1/n` is correct (at `n = 2`, via an `ε`-family) |
| **C2** Three drones | a run that starts out of position, passes through a genuine three-way meeting, and settles |
| **C1** Nondeterminism | measured it instead of assuming it |
| **D1 / D2** Cleanup | two dead definitions removed; D2 closed as unnecessary |

### Three things worth knowing

**The plan's B5 hazard was real.** `LeftSync` is step-indexed; Lemma 3.7's
conclusion is a real-time deadline, and the step-indexed version of the lemma is
not merely inelegant — it looks *false*, because a drone heading right can sit
outside its interval mid-step and be back inside by the next event. The fix was
a thin real-time layer, ~340 lines, touching nothing else. The question `PLAN.md`
asked to record — *should the time-indexed predicate have been primary from the
start?* — has an answer, and it is **no**: it would have taxed 500 theorems to
pay for one proof.

**`convergesBy` carries one hypothesis beyond the standing invariant**:
`ApartOnBoundaries` on the *starting* configuration. That is not slack —
§3.20's counterexample shows the statement is false pointwise — and two one-line
lemmas discharge it. Three concrete configurations, including an `n = 3` one
that *exercises* the case rather than avoiding it, show the theorem is not
vacuous.

**C1 turned out seven-eighths wrong as previously described.** Three documents
had claimed that `newDir`'s priority order was "one resolution" of the paper's
nondeterminism. Checking every pair of simultaneously-due events: two
combinations are impossible, five agree, and the one that differs is the paper's
bounce — where the alternative provably walks a drone off its own endpoint. The
real gap is the *definition of a meet* (ours requires approach, the paper's is
positional).

### What was not finished, and why

- **C1′** — making `step` a relation so the theorem quantifies over all
  resolutions. `PLAN.md` had it at **M**; it is not. Roughly thirty primitive
  lemmas unfold `newDir` and would need re-deriving from a specification, and
  every statement in all 31 files gains a trajectory parameter. Re-sized to
  **L** and left open.
- **C3′** — sharpness for general `n` needs an `n`-drone cascade rather than a
  four-configuration trace. **M**, left open.

Both are recorded in `STATUS.md` §4 and `PLAN.md` at their true sizes.
`STATUS.md`, `PLAN.md`, `INSIGHTS.md` (four new entries) and `README.md` are
current, and `scripts/refresh_status.py`'s self-check passes.
