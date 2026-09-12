# What this project taught us

A durable record of the non-obvious things, separate from `STATUS.md` (which
tracks *what is proved*) and `PLAN.md` (which tracks *what we intended*). If
someone picks this up cold — or if I do, months later — this is the file that
saves the rediscovery.

Ordered roughly by how much time each would have cost to rediscover.

---

## 1. The bounce bug: a concrete case beat 145 theorems

**The single most valuable half-hour in the project.**

`AtSeparation` originally required the pair to be *escorting* — co-located
**and heading the same way**. That reads as obviously right, and it is wrong.

Two drones converging on the boundary they share and meeting **exactly** on it
— the paper's *bounce* — have **opposite** headings right up to the instant
they meet. So no separation fired, the meet branch took over, and the
right-hand drone was sent **left, out of its own interval**, never to be
synchronized again.

The bug silently falsified the very theorem the development exists to prove,
and **145 passing theorems did not notice**, because everything was universally
quantified and nothing forced the definitions to be exercised.

> **Lesson.** A formalization's danger is not a wrong proof — Lean stops those.
> It is a *wrong definition* supporting a flawless proof of something else. The
> only defence is instantiating it. Validate the model before proving the
> headline theorem about it, however much faster the theory feels.

The fix: co-location on the shared boundary is the real condition, however the
pair arrived there. `Dpss/Examples.lean` keeps it as a regression test.

---

## 2. The escort is emergent, not primitive

The literature describes an escort as a pair "travelling together", and the
brief warned that *"a meeting is not an instantaneous event but the start of a
joint motion of indefinite duration"* — implying a co-moving group needs to be
a first-class object.

It does not. **Because all drones move at the same speed, a co-located pair
pointing the same way stays co-located automatically.** The escort falls out of
the ordinary dynamics; no grouping construct, no special case in the stepper.

`sepRate_eq_zero_of_escorting` + `coLocated_advance_of_escorting`.

---

## 3. The pair balance replaces the paper's figure

Avigad–van Doorn prove Lemma 3.2 with a timing argument — *"drone j+1 must have
taken at least as long to turn around as drone j"* — illustrated by a figure.
Timing arguments are painful to formalize.

The whole content compresses into one number:

```
balance(j) = (pos j − commonEnd j) + (pos (j+1) − commonEnd j)
```

* It evolves at `sign j + sign (j+1)`, so it is **constant whenever the pair
  heads opposite ways** — which is what they do right after separating, and
  again while approaching.
* **A separation zeroes it.**
* **Its sign says where the pair can meet**: nonnegative ⟺ any co-location
  happens at or beyond the shared boundary. That is exactly Lemma 3.2's
  induction hypothesis.
* Nonnegative balance ⟹ the right-hand drone is at or beyond its own left
  endpoint ⟹ **left synchronized**.

And an identity that makes the escort machinery click: **an escorting pair's
balance is exactly twice its separation deadline**, so *"the step does not
overshoot the separation"* and *"the step does not drive the balance negative"*
are literally the same statement.

---

## 4. Timing arguments can often be made positional

Following on from §3, and the most transferable idea here.

The remaining case of Lemma 3.2 looked like it needed elapsed-time bookkeeping
for two drones. It does not:

* In the state concerned the pair heads opposite ways, so the balance is
  constant; from a separation it is **zero**, so the two are displaced from the
  boundary by **equal** amounts.
* Left synchronization caps the left drone's displacement at `1/n`, hence caps
  the right drone's at `1/n` — putting it at or **before** `rightEnd (j+1)`.
* Lemma 3.1 permits it to reverse only at or **beyond** that point.
* So the two coincide exactly, both drones are pinned to their endpoints, and
  the left drone must reverse too.

A statement about *who turned first* became arithmetic on interval endpoints.

### 4a. …but zero-length steps complicate it

A wrinkle found while trying to finish the argument, and the reason case 3 held
out as long as it did. (It is closed — `BalanceInvariant.lean` — and the wrinkle
below turned into one of the tools that closed it.)

A step can legitimately take **zero** time: when an event is already due, the
step fires it without advancing the clock. That breaks the tidy story "the
balance falls at rate 2, so bound the step by the remaining budget", because a
zero-length step changes headings without consuming any budget at all.

Concretely, the pinning argument above shows both drones arrive at their
endpoints *simultaneously* — but showing the left drone then **turns**, rather
than merely being entitled to, needs to rule out an unbounded run of
zero-length steps in which it sits at its endpoint heading outward. Non-Zeno
rules that out globally (`nonZeno`), so the ingredients exist; assembling them
is bookkeeping over run indices rather than new mathematics.

> **Lesson.** In an event-driven model, "time advances each step" is an
> assumption worth checking before any argument leans on it. Here it is false,
> and the false version is very natural to assume.

---

## 5. Non-Zeno by counting, not by the paper's propagation claim

The paper's non-Zeno argument rests on:

> *"if drone `i+1` makes two consecutive left turns, then drone `i` must turn
> right in the interim"* — called not hard to show, and not shown.

**I could not reconstruct it.** A right turn by `i+1` comes either from
separating from `i` — at which instant `i` turns **left**, not right — or from
meeting `i` before their shared boundary, at which instant `i` does not turn at
all. No argument is offered for why the surrounding interval must contain one.

It may well be true. But in a project whose entire subject is a
convincing-looking proof that stood for a decade and was false, formalizing an
unverified sketch is the one unforgivable move.

The route taken instead is self-contained and, in hindsight, simpler:

1. **Every step turns at least one drone** — unconditional, cascades included.
2. **Consecutive turns of one drone are `1/n` apart in time** — because between
   them it crosses its whole interval, that being the only place it may turn.
3. So among any `n+1` consecutive steps some drone turns **twice** (there are
   only `n`), costing `1/n` of clock.

`n+1` steps buy `1/n`; the clock is unbounded. The only non-DPSS ingredient is
a pigeonhole.

> **Lesson.** When a source hand-waves, try to find your own route before
> trying to reconstruct theirs. Ours reused a lemma the convergence proof
> needed anyway.

---

## 6. Invariants enforced by construction beat invariants inherited

`escortsCoherent_step` — escorts keep pointing at the boundary they are
escorting to — was written with three hypotheses (`OnPerimeter`, `AdjOrdered`,
the previous coherence). **Lean reported all three unused.**

The reason is structural: `droneNextTime` always includes an escorting pair's
`separationTime` among the candidates it minimises over, so **a step can never
overshoot a separation**. Coherence is enforced by the scheduler, not inherited
from the previous state.

This happened repeatedly. Whenever Lean says a hypothesis is unused, the honest
move is to delete it and keep the stronger theorem — not to silence the
warning. It happened five times here and every time the theorem improved.

---

## 7. Simultaneity: make the update a function of the whole state

Several events can come due at the same instant — routinely, not
exceptionally. Composing individual updates would force an ordering that then
has to be justified.

Instead, each drone's post-event direction is **a function of the entire
configuration** (`newDir`). Simultaneity is automatic and no ordering needs
defending. The price is a priority order inside `newDir` (border > separation >
meet), and that price is visible and documented rather than smeared across
update code.

---

## 8. Things that were *not* problems

Recorded because each cost real effort to worry about.

* **Spurious border deadlines.** `timeToNextEvent` minimises `borderTime` over
  *every* drone, including interior ones where no border event looked
  reachable. I proved domination lemmas to contain it. Unnecessary: flying a
  drone for exactly `borderTime` lands it on `0` or `1` — that is what the
  quantity *is* — so the event genuinely fires. Ordering makes it coherent: if
  an interior drone reaches `0`, everyone to its left is already there.
* **Zeno at zero-length steps.** Feared an infinite stall of `dt = 0` steps
  after a separation. Cannot happen: the scheduler only offers
  `separationTime` to an *escorting* pair, and a just-separated pair heads
  opposite ways.

---

## 8a. A lemma that read as obvious and was false

Attempting the last case of Lemma 3.2, I aimed at: *a co-located pair that ends
a step heading apart is sitting exactly on the boundary they share.* Heading
apart is what a pair does after **separating**, and separations happen on the
boundary. Obvious.

It is false. Four drones stacked at one point, heading alternately outward: the
two middle drones each escort the *outward* neighbour, so the middle pair
splits at a point that is not their boundary. `Dpss/Counterexample.lean` builds
it and proves the refutation.

The statement needs **reachability** — in a state the algorithm can actually
produce, a pair heading apart has just separated. But that must be carried as
an induction hypothesis, not proved pointwise.

> **Lesson.** When a case analysis stubbornly refuses to close, consider that
> the goal may be false rather than that you are proving it badly. Building the
> counterexample took less time than the failed proof attempt, and unlike the
> attempt it produced something permanent.

This is also the nondeterminism the paper flags — three or more drones
converging with a middle drone free to choose — showing up as a concrete
obstruction rather than a footnote.

---

## 9. Two false lemmas Lean caught

Worth recording that the method works, on exactly the class of error the paper
itself fell to.

* **The rightward domination lemma was false.** `droneNextTime j` only ever
  consults the pair `(j, j+1)`, so a meet with the *left* neighbour is
  accounted for at `j-1`, never at `j`. The asymmetry with the leftward version
  is real, not an oversight.
* **"The middle and right drones are not approaching in configuration B."**
  They are. The arithmetic came out the same either way, so a hand check would
  plausibly have missed it.

---

## 10. A planning error worth not repeating

The brief proposed refuting the known-false `3T` bound as a regression test —
"a known-bad historical artifact makes a nice regression test". The first
planning exchange separately settled on **Algorithm A only**.

Those two decisions are **incompatible**, and neither I nor the plan noticed
for a dozen commits. The false bound concerns **phase 1**, the propagation of
*estimates*, which is Algorithm B; Algorithm A assumes estimates correct and
this development drops them from `Config` entirely. The refutation is
unreachable here, not merely unfinished.

> **Lesson.** When a scope decision and a goal are adopted in different
> conversations, check they can coexist. Concrete traces substituted well —
> they caught the bug the refutation was meant to catch.

---

## 11. Lean mechanics that cost real time

* **Real division is noncomputable.** Essentially every definition here needs
  `noncomputable def`, and the error surfaces only at the *use* site.
* **`Finset.Nonempty` written inline as `⟨x, mem_univ _⟩`** elaborates at the
  *unfolded* type `∃ x, x ∈ univ`, and every downstream `inf'` lemma then fails
  to apply with a confusing error. Name it with an explicit type ascription.
* **`rw [Finset.lt_inf'_iff]` fails on `ℝ`** — the lemma is stated via the
  `LinearOrder`-derived `<`, which does not match `Real.instLT` syntactically.
  Term-mode application elaborates up to defeq and works.
* **`rintro ⟨-, h⟩` cannot discard a binder that `h` depends on.** Name it
  `⟨_x, h⟩` instead. This cost four separate debugging rounds.
* **`split_ifs` discharges contradictory branches itself** when the relevant
  hypothesis is in context, so the number of goals is not the number of
  branches. Prefer explicit `rw [dif_pos …, if_pos …]` where the branch is
  known.
* **Dependent rewrites fail** when the index appears in a proof argument
  (`motive is not type correct`). Usually the two terms are *definitionally*
  equal and `exact` works where `rw` does not.
* **The model is `noncomputable` throughout**, so it cannot be `#eval`ed.
  Concrete traces have to be symbolic proofs. Worth it anyway — see §1.

---

## 12. Tooling: an audit document must audit itself

`STATUS.md` is meant to be trusted, so it must not be able to lie.

* Scripted prose edits **failed silently three times** while the commit
  proceeded, leaving commit messages describing changes that had not happened.
  Exact-prose matching is the fragile part; **section-boundary edits have never
  failed**.
* `scripts/refresh_status.py` now self-checks what it writes: the gap list must
  be sequentially numbered, each generated block must appear exactly once, no
  placeholder may survive, the audit block must be non-empty and passing. It
  has caught a mis-numbered list before a commit at least once.
* `scripts/audit.py` had a bug of its own: it scanned a **doc comment** that
  wrapped onto a line starting with the word "theorem", looked up a
  non-existent constant, and wrote "0 theorems, audit FAIL" into the document.
  It now strips Lean comments, tracking nesting, before extracting names.

> **Lesson.** Tooling that certifies correctness needs its own certification.

---

## 13. The index that was right for 500 theorems and wrong for one

Every predicate in this development is indexed by **step number**: a run is
`run hn 0, run hn 1, …` and "drone `i` never goes left of its endpoint" is a
statement about those. That is the natural index for an event-driven model and
it served ~500 theorems without complaint.

Lemma 3.7 is the exception. Its conclusion is a **deadline in real time**
(`by time t + 1/n`) and its proof reads a drone's heading and position at an
instant that is in general *strictly inside a step* — previous event before it,
next event after it. The step-indexed reading of "left synchronized" is
genuinely weaker there: a drone heading right can sit left of its endpoint
mid-step and be back inside its interval by the next event. So the step-indexed
version of the lemma is not merely inelegant. It looks false.

Two things are worth extracting.

**Add the second index, do not replace the first.** The temptation, once you
find the primary index is wrong somewhere, is to switch. Here that would have
taxed 500 theorems to pay for one: the target statement is index-shaped, every
earlier lemma is index-shaped, and the real-time reading is needed only inside
one proof. A thin real-time layer, introduced where the argument demands it and
discharged back into indices immediately, cost about 340 lines and touched
nothing else.

**The bridge between the two indices is not the obvious inequality.** "Time is
monotone along a run" does *not* give `time_m ≤ time_k → m ≤ k` — steps of zero
length are routine here (an event already due costs no time), so several
indices can share an instant. What is true, and what every such argument
actually wanted, is that **if the clock does not move, no drone does either**.
Carry the position across, not the index.

> **Lesson.** When a single proof wants a different notion of "when", the
> cheapest correct move is usually a second, thin index — with an explicit
> bridge — not a migration.

---

## 14. One lemma for every "true at the events, therefore true in between"

The whole real-time layer rests on three lines:

```lean
theorem nonneg_of_endpoints {a r u d : ℝ} (h0 : 0 ≤ a) (h1 : 0 ≤ a + r * d)
    (hu : 0 ≤ u) (hud : u ≤ d) : 0 ≤ a + r * u
```

A linear function nonnegative at both ends of an interval is nonnegative
throughout it. Within a step, *every* quantity of interest is affine in time —
a position (rate `±1`), a gap (rate `sepRate`), a balance (rate `sign i +
sign (i+1)`). So "the drone is inside its interval at both events, hence
throughout the step", "the pair is ordered at both events, hence throughout",
and every variant are all this one lemma with different names substituted.

It was used six times and would have been used more had the layer grown.

> **Lesson.** Before writing the third instance of an interpolation argument,
> write the interpolation lemma.

---

## 15. Measure a gap before restating it

`Step.lean` recorded, for months and in three documents, that `newDir`'s
priority order — `border > separation > meet > unchanged` — was "one
resolution" of the nondeterminism Avigad–van Doorn deliberately leave open.
That description was written when the priority order was chosen, and never
checked.

Checking it took an afternoon. For every pair of events that can be due at one
drone at one instant, compute both answers and compare: **seven of the eight
combinations are not choices at all.** Two are impossible, five agree — and
they agree for one uniform reason, that a separating drone is standing on a
boundary and from a boundary the escort heading is forced. The eighth is the
paper's *bounce*, and there the alternative resolution provably walks a drone
off its own left endpoint, which is the failure a concrete trace had already
caught (§1).

The caveat was seven-eighths wrong. Worse, it named the wrong thing: the real
restriction is not the priority order but the **definition of a meet** — ours
requires the pair to be approaching, the paper's is positional. Getting the
name right also re-sized the remaining work from "a session" to "a refactor
touching every file".

> **Lesson.** A caveat is a claim. Prove it, refute it, or state it as a
> question — but do not let it sit in three documents unchecked, because the
> plan built on top of it inherits its errors.

---

## 16. A hypothesis the source never has to state

Theorem 2.1 here carries one condition beyond the standing invariant:
`ApartOnBoundaries` — a co-located pair heading apart sits on the boundary it
shares. The paper never mentions it, and is right not to: about the states the
algorithm actually reaches, it is obvious.

About *configurations in general* it is false, and `Dpss/Counterexample.lean`
exhibits four drones stacked at one point that refute it. So it is an invariant,
proved preserved by a step — and therefore a genuine condition on the
**starting** configuration, which is where it now sits, with two easy
sufficient conditions supplied.

This is the second time in the project that a step the source treats as beneath
mention turned out to be substantial formalization work; "by symmetry" (§B7)
was the first.

> **Lesson.** The parts of a paper proof that a formalization has to *add* are
> not the hard steps. They are the sentences the author did not write.

---

## 17. Size the item from the statement, not from the construction

Two of the last three items were budgeted for the obvious route and both fell
to a short argument instead.

**C3′ — sharpness for every `n`.** The plan sized it as the paper's `n`-drone
cascade: `2(n−1)` phases, each a configuration given by a formula in the phase
index, each needing a minimum over `Fin n` computed by hand. But the *theorem*
does not ask where every drone is at every moment; it asks that **one** drone be
outside its interval at **one** late instant. That needs a lower bound on when
drone 0 can return, and the bound comes from Lemma 3.1 plus one observation —
on a ladder every gap is `d` and stays `d` while all drones head right, so a
drone that turns left would have to be co-located with its right-hand
neighbour, so the first drone to turn is the one that has none. No
configuration in the cascade is ever written down.

**C1′ — the nondeterminism as a relation.** Sized at `L` for "re-prove the
development over an arbitrary trajectory". The actual proof is one theorem: the
relation has exactly one successor on reachable states.

The error in both cases was estimating from the *construction the source
describes* rather than from the *statement to be proved*. A construction is a
witness; a witness is usually not the cheapest evidence.

> **Lesson.** Before budgeting for the machinery, spend an hour looking for the
> argument. The plan's estimate is a hypothesis about the proof, and like any
> hypothesis it is worth testing before acting on it.

---

## 18. Re-read the source before executing the plan item

C1′'s `L` estimate was written from the Lean side — counting the lemmas that
unfold `newDir`, and the files that would gain a parameter. It was never
checked against the paragraph of Avigad–van Doorn that defines the problem.
That paragraph says:

> Neither of these issues bears on the results reported below, since our upper
> bound only concerns phase 2, **where these issues do not arise**.

The authors are telling you the work is unnecessary, and — more usefully — that
there is a theorem there: the ambiguous configuration is unreachable. Proving
it took a sitting and produced a better result than the refactor would have,
because it explains *why* the nondeterminism never mattered instead of merely
carrying it along.

The same paragraph also characterizes the ambiguity precisely — "three of them
are within the middle drone's interval" — which turns out to be, word for word,
the condition under which the two escort headings differ. The geometric
statement to prove was sitting in the prose.

> **Lesson.** A plan item's estimate ages faster than the source it is about.
> Re-read the twenty lines that define the problem before spending a day on it.

---

## 19. Keep a widened specification honest

`LegitDir` widens the heading update into a relation so that Theorem 2.1 can be
stated for every resolution. A widening like that has an obvious failure mode:
write the specification so tightly that it admits only the original function,
prove uniqueness, and declare victory having proved nothing.

The guard is a witness in the other direction. `ExamplesThree.triple` is a
configuration where the open clause genuinely admits two different headings —
the middle drone is together with both neighbours, and the meeting point sits
strictly inside its own interval, so escorting left and escorting right
disagree. With that in hand, `legitDir_unique` says something: the freedom
exists, and the algorithm never reaches a state that exposes it.

> **Lesson.** Every uniqueness theorem about a specification needs a
> non-vacuity witness, or it is a theorem about your own definition.

---

## 20. State the vehicle contract in the units the proof already uses

The fence (`Dpss/Fence.lean`, `rust/src/fence.rs`) had to remove three
idealizations at once — point mass at unit speed, instantaneous reversal,
perfect sensing. The obvious parameterization is by *speed*, because that is
what "unit speed" idealizes. It is the wrong one, for two separate reasons that
happened to point the same way.

In Verus, a speed bound below one is a rational, and Verus has neither rationals
nor reals. The team model got around that with the scaling argument of
`Dpss/IntModel.lean` — a genuinely clever piece of work that took a sitting to
find and rests on a parity invariant. None of it was needed here, because
`Dmax` — *displacement per sample period* — is a length. Every quantity in the
fence argument is then a length in the same units, there is no division
anywhere, and the integer model is the model rather than a scaled image of it.

In Lean, the same choice removed the continuous-time layer entirely. The motion
between samples enters only as `p k - Dmax ≤ low k`, a hypothesis about a
low-water mark. So a statement that quantifies over all instants —
*the drone never crosses the fence* — is proved by a discrete induction with no
analysis in it at all.

And the third reason, which is the one that matters outside this repository:
displacement per sample is what a flight test produces. Speed is not.

> **Lesson.** When a proof must take a number from the physical world, let the
> physical world choose the units. The interface is what an engineer can
> measure, not what the idealization happened to normalize.

---

## 21. Test the coordinate change before budgeting the rewrite

`adj_ordered` is `0 ≤ gap` — the separation invariant with `d = 0`. Raising it
to `d ≤ gap` reads like a contradiction of the algorithm, because in DPSS a meet
*is* a loss of separation: co-location is how a pair learns to escort. The
plan's estimate for margined separation was accordingly "S if a shear works,
else L", with a day set aside to find out which.

The shear works, exactly. `yᵢ = xᵢ - i·d` turns separation into ordering;
`Config.toPoint_advance` — the one lemma that would have failed had the shear
been an approximation — says the dynamics commute; and the event predicates pull
back one for one, with `CoLocated` becoming *"the pair has closed to the
standoff"*, which is the physically right reading rather than a weakening.

The catch is real and was worth finding early: the assigned segments do **not**
shear. They have to be respaced, and `standoff_tiles` says how — each segment
narrows by the factor `1 - (n-1)d`, with a buffer of exactly `d` between
consecutive segments. `coverage_exact` then says the respacing loses nothing:
when the standoff is two half-footprints, the two neighbouring drones cover the
buffer between them precisely. A day of Lean converted an open question about
the shape of a quarter's work into a change of constants, and produced a
quantitative prediction on the way out — the convergence bound under standoff
should be `(2 - 1/n)·(1 - (n-1)d)`, *better* than the point bound, because the
drones have less ground to cover.

One small dividend worth recording, because it is the kind of thing a hand-wave
gets wrong: `toPoint_onPerimeter` does not need `0 ≤ d`. Containment transfers
from the two outermost drones alone. The hypothesis was written down out of
habit, and the proof did not use it.

> **Lesson.** When a plan item is sized "S if X, else L", the first thing to
> build is X. Not a prototype of the S branch, and certainly not the L one.

---

## 22. Transfer both ways, and sharpness is free

Three items on the safety track — the standoff model, the separation controller,
and the right-hand fence — each looked like "prove the existing theorem again
under weaker hypotheses". None of them was. Each turned out to be a **map
between two structures**, and building the map cost less than one re-proof.

* `Dpss/Standoff.lean`: `toPoint` and `fromPoint` are mutually inverse, so the
  standoff model and the point model are two coordinate systems on one thing.
  The standoff step is the point step read in standoff coordinates, and
  `sConvergesBy` — Theorem 2.1 with the bound `(2 − 1/n)·(1 − (n−1)d)` — is the
  point theorem with the clock rescaled.
* `Dpss/Separation.lean`: `PairTraj.toFence` sends a pair to the fence
  trajectory of its excess separation with the vehicle doubled. `le_low` is
  `Fence.Traj.low_nonneg` composed with that map.
* `Dpss/Fence.lean`: `TrajR.mirror` sends a right-fence trajectory to a
  left-fence one, positions to `L - ·` and low-water marks to high-water marks.

The part worth extracting is what the *second* direction buys. Writing
`Traj.toPair` as well as `PairTraj.toFence` took a dozen lines and made
`pair_margin_sharp` a four-line corollary of `margin_sharp` — a sharpness
theorem for the separation margin, obtained without constructing a single
witness. A transfer proved in one direction gives you the guarantee; proved in
both, it gives you the guarantee *and* the proof that it cannot be improved.

The failure mode this avoids is the one the plan had budgeted for: restating
every theorem with `d ≤ gap` in place of `0 ≤ gap` and repairing the proofs. That
would have been a quarter's work and would have produced two parallel
developments to keep in step. Note also what the map makes *visible* — S0's real
finding was not that the shear works but that **the segments do not shear, they
respace**, which a hypothesis-weakening rewrite would have quietly hidden inside
a hundred adjusted arithmetic steps.

> **Lesson.** Before weakening a hypothesis throughout a development, look for a
> map to the development you already have. If you find one, build its inverse
> too — the round trip is where sharpness comes from.

---

## 23. Which idealizations are coordinate changes, and which are not

The safety track set out to remove five idealizations from the team model: point
drones, unit speed, instantaneous reversal, perfect sensing, and a global event
scheduler. The plan sized them by how much of the development each one touched.
That was the wrong axis. The right one turned out to be:

> **Does the idealization act uniformly across the system, or does it hold a
> symmetry between components in place?**

Uniform ones are changes of coordinates and cost a file:

| Idealization | The coordinate change | Cost |
|---|---|---|
| point drones | shear `yᵢ = xᵢ − i·d` | `Dpss/Standoff.lean` |
| unit speed | change of clock `τ(t) = ∫₀ᵗ v` | `Dpss/Kinematics.lean` |
| separation vs. fencing | shift by the standoff, double the vehicle | `Dpss/Separation.lean` |

Each removes a real idealization, each transfers *every* theorem including
sharpness, and each took a sitting rather than the sitting-to-quarter the plan
had budgeted.

The ones that are not uniform are rewrites, and no amount of cleverness changes
that:

* **Speeds that differ between drones.** Uniform speed is what makes a
  co-located pair stay co-located, so `Escorting` is an invariant with no
  representation of its own. Drop uniformity and that is gone, taking
  `EscortsCoherent`, `Dpss/Coherence.lean` and Lemmas 3.2–3.4 with it.
* **Control authority** — the turn allowance, and that a reversal completes
  within a sample period. `Dpss/Continuous.lean` derives `Dmax = V·Δt` from a
  speed bound, but *cannot* derive these, and the reason is not technical: a
  fast drone with strong actuators has a small turn allowance and a slow one
  with weak actuators a large one, so no speed bound distinguishes them. They
  are separate physical facts and belong in the hypotheses where an engineer can
  see them.

The diagnostic is cheap to apply and would have re-sized four plan items before
any of them were started. Ask it first.

> **Lesson.** Size an idealization by whether it is uniform across the system,
> not by how many files mention it. A uniform one is a change of coordinates —
> find the map. A non-uniform one is a rewrite, and the honest move is to say so
> and leave it as a hypothesis.

---

## 24. The fallback was already in the development

S5's open design question was: *what should a drone do when coordination is lost
for good?* It looked like the item that would need new mechanism — a hold mode,
a timeout, a re-join protocol, all of it to be specified and then proved safe.

It needed none. The answer was a theorem that had been proved for an entirely
different reason.

`sConvergesBy` says every drone ends up confined to its own respaced segment.
`standoff_tiles` says consecutive segments are exactly `d` apart. Compose them
and *confinement is separation* — `separated_of_segments`, whose proof is one
`linarith`. So a drone that has lost contact permanently is safe provided it
stays in its own segment, which is precisely what the algorithm has already
converged to doing. The fallback is the steady state.

That turns the whole communications budget inside out. `CommsPair` prices
staleness at one `Dmax` of margin per sample of age, and the natural reading is
that a team needs a network of a certain quality *for ever*. It does not. The
inflated margin buys coordination during phase 1; afterwards the invariant is
maintained by geometry, and the network can fall away entirely. **The
communication requirement is transient.**

This is not luck, and the reason generalizes. The algorithm converges to a
*partition* of the perimeter, and a partition is exactly the structure that
makes a global property (separation) checkable locally (stay in your own piece).
Any protocol whose steady state is a partition has a free degraded mode, and the
proof of convergence is also the proof that the degraded mode is safe.

> **Lesson.** Before designing a degraded mode, look at what the system already
> converges to. If the steady state is safe without the resource that was lost,
> the fallback is "hold the steady state" — and the convergence proof you
> already have is the safety proof you were about to write.

---

## 25. A correspondence gap can be deleted rather than tested

The safety half of this repository ships two proofs of the same theorem: one in
Lean over `ℝ`, one in Verus over `int`. Between them sat a gap nobody had
written down as an obligation, because it is not one — real numbers and
mathematical integers are different objects, so the two theorems were, strictly,
about different systems, and a reader had to satisfy themselves that nothing
lived in the difference.

The plan's answer was to *test* across it: drive the verified binary and check
its trace against numbers Lean had proved. That is worth doing and is what S6c
does. But the first step was cheaper and stronger than any test, and it started
from a question about the proof rather than about the artifacts:

> **which of these hypotheses does the argument actually use?**

The fence argument uses addition, subtraction and comparison. No division, no
completeness, no limits, no Archimedean property. `ℝ` was never the subject; it
was a default. Stated over an ordered ring, the theorem holds at `ℤ` as an
instance, and at `ℤ` the Lean statement and the Verus statement quantify over
the same integers. The gap is not narrowed, or tested, or bounded. It is gone,
and the generalization is a *weakening of hypotheses* — nothing was reproved and
no proof grew.

Two dividends came with it that were not part of the reasoning.

**The shape of the file turned out to matter as much as the type.** Verus states
the per-leg content as predicates (`leg_ok`, `obs_ok`) consumed by pointwise
`proof fn`s, and iterates them at the end. Lean had the same content as *fields
of a structure*, consumed inside the induction. Same mathematics, but a reader
comparing them was comparing a structure against a predicate, clause by clause,
by hand. Splitting the Lean into the same two layers cost nothing — three proofs
got *shorter* — and turned the comparison into a list of statements with the
same names, the same argument order and the same arity. A correspondence that
has to be checked by a human should be arranged so the human is comparing like
with like; that is a property of the presentation, and it is free.

**The definitions became computable.** Real division is what forces
`noncomputable` through this development (§11), and there is none in the fence —
so over an ordered ring the controller, the trajectory and the sharpness witness
all compute. An integer counterexample that had to be a symbolic construction is
now three `decide`s. The step taken for correspondence paid for the step after
it, which is the one that needs to evaluate things.

> **Lesson.** Before building machinery to test across a gap between two
> formalizations, check whether the gap is load-bearing. Strip each proof to the
> hypotheses it uses; if what is left is common to both settings, instantiate
> one at the other and the correspondence problem disappears instead of becoming
> a test suite. And when two proofs must be compared by eye, spend the small
> amount it costs to give them the same shape.

---

## 26. The transfers show up in the traces

S6c set out to replace six recorded trace blocks — a drone against a wall, a
pair closing on each other, a pair across a degraded link, each twice for a
sufficient and a deficient margin — with traces derived from Lean. The plan
sized it as "define the worst-case simulator, `decide` its trace", and the
implicit expectation was three simulators in three vocabularies.

There is one. The six blocks are the *same trajectory*: fly at the fence, spend
the whole displacement allowance every leg, read the sensor high by the whole
sensing allowance, ask to keep going, and reverse without gaining ground. What
differs between the blocks is not the adversary but the **vehicle** — doubled
for a pair, and doubled with `age · dmax` in its sensing term for a stale link.

That is not a coincidence and it is not cleverness. It is `INSIGHTS.md` §22 —
*transfer both ways* — arriving somewhere nobody was looking for it.
`PairTraj.toFence` and `CommsPair.toFence` were built to avoid re-proving the
separation guarantee, and their content is precisely that a pair under a doubled
vehicle **is** a drone at a fence. A worst case for one is therefore a worst case
for the other, in the coordinates the map supplies. The test artifacts collapse
for the same reason the proofs did.

Two things follow that are worth carrying elsewhere.

**A transfer predicts what the tests should look like.** If two results are
related by a map, their worst cases are related by the same map, and building
them separately is duplicating work the map already did. The six-blocks-to-one
collapse was visible in `Dpss/Separation.lean` from the day it was written; it
took until the traces needed generating to be noticed. Worth asking, whenever a
transfer is proved: *what else in the repository is now redundant?*

**Prove the contract in general; evaluate only the numbers.** `Sim.trajOk` says
the adversary satisfies the vehicle contract for every well-formed vehicle and
every margin. It mentions no recorded number, so no change to the traces can
quietly make it vacuous, and the three blocks with a sufficient margin come out
clear of the fence by the fence theorem rather than by evaluating anything. Only
the printed rows are `decide`. A generated test suite is only as good as the
general statement standing behind it, and that statement is usually cheaper to
prove than the instances are to check.

> **Lesson.** When two parts of a development are connected by a transfer, their
> *tests* are connected by it too. Look for the collapse before writing the
> second test harness — and prove the contract the harness is supposed to
> exercise as a general theorem, so that evaluation is left with nothing to
> decide but the digits.

---

## 27. A translator earns its keep at the point where it says no

`scripts/lean_to_verus.py` exists so that the Verus specification is *the* Lean
specification rather than a second one somebody typed in. Its doc comment has
said from the first day that anything outside its grammar is refused with an
error naming the definition and the token, never guessed at, because a
translator that quietly does its best is worse than no translator: the Rust then
verifies beautifully against the wrong specification.

Extending it to the safety predicates (S6d) produced the first refusal that was
*tempting*, and it is worth recording what it looked like.

`link_ok` says a held report is not too old:

```
src k ≤ k    ∧    k - src k ≤ a
```

In Lean those are natural numbers, where subtraction truncates at zero. In Verus
they are `int`, where it does not. `k - src k ≤ a` is therefore a different
proposition in the two systems — and yet, in the presence of the first clause,
the same one. A translator could be given that reasoning. It would be correct
here, and it would be the end of the guarantee: from then on the generated file
would be right *because someone had checked an argument*, which is the thing
generation exists to avoid.

So the two clauses are not generated. They stay hand-written, with the Lean
statement named beside them, and the file that would have generated them says
why in its header.

Two things generalize.

**The valuable part of a translator is its refusal set, and refusals should be
written down where the reader is.** Not in the translator's source, where only
the next maintainer will see it — in the generated file's header and in the
hand-written code that took over. A reader of `rust/src/comms.rs` needs to know
that these two clauses are the ones nothing mechanical checks.

**Type systems disagree quietly at exactly the interesting places.** ℕ vs `int`
subtraction is the whole of this instance, and it is invisible: both sides read
`k - src k ≤ a`, both are true of the intended system, and the difference only
shows on inputs the surrounding hypothesis excludes. A syntactic translator has
no way to see the difference and no business assuming it away. When two
formalizations of the same thing are being connected, the arithmetic that looks
identical is where to look first.

> **Lesson.** Judge a mechanical translator by what it declines, not by what it
> covers, and publish the declined list where the code is — a refusal recorded
> only in the tool is a refusal nobody reads.

## 28. A predicate that never executes is checked by nothing, and the gap hides
between two tools that each look complete

`scripts/lean_to_verus.py` generates the arithmetic and boolean specification
from Lean and CI fails on drift, so nothing arithmetic can be mistranslated.
Verus proves every executable function equals its specification, up to
`view_of(*final(e)) == spec_step(view_of(*old(e)))` for all `repr_ok` inputs, so
nothing executable can drift from what it is verified against. Both statements
are true, both were true before S7b, and between them sat four definitions that
neither covered.

`OnPerimeter`, `AdjOrdered`, `EscortsCoherent` and `OnLattice` quantify over
`Fin n` with a dependent proof argument. The generator **refuses** them — §27 is
about why that refusal is the right behaviour — so they are hand-written on the
Rust side. And a Verus `spec fn` never runs, so no trace could reach them
either. Each tool's guarantee was intact and the definitions fell through the
join. The lesson generalizes past this repo: when two mechanisms each cover
"their part", the thing to audit is the part *neither* claims.

**The fix has to be evaluable on states that violate the predicate.** This is
the part that is easy to get wrong. The obvious move — evaluate the standing
conditions along a recorded run — proves nothing at all, because `repr_ok`
*asserts* `inv`, so on any state reached by `step_ex` a wrong transcription and
a right one both answer `true`. What distinguishes them is which states they
**reject**. So none of the new `*_ex` functions may require `repr_ok`;
`repr_bounded` says only what the arithmetic needs, and six of the ten rows in
the standing-conditions block violate something on purpose.

**Both sides needed the same trick, in their own idiom.** Lean has no
`Decidable` instance for `∀ (i : Fin n) (h : i.val + 1 < n), …` either — the
dependent binder defeats `Fintype.decidableForallFintype`, which is the same
shape that defeats the translator. A `List.all` over `List.finRange n` with the
body a `dite` on `h` carries it, and an `_iff` theorem makes the `Bool` twin the
condition rather than a second copy of it.

## 29. The invariant proofs really are the tighter net — measured, not assumed

The changelog for E1 recorded that a corrupted `escort_dir_left` was caught by
escort coherence rather than by the traces, and that no corruption could be
found that passed every proof and still changed a trace. S7b was a chance to
test that claim against a predicate the proofs constrain directly, and it
survived twice:

| corruption of `adj_ordered`, spec and exec together | result |
|---|---|
| `0 <= gap` weakened to `-2 <= gap` | 7 Verus errors |
| range `0 <= i` slipped to `1 <= i` | 6 Verus errors |

The reason is structural, and worth stating because it says when *not* to reach
for a differential test. `inv` is used in both directions: preservation lemmas
must **prove** it of the stepped configuration, and everything else **assumes**
it of the current one. A strengthening breaks the proofs; a weakening breaks the
uses. A predicate pinned from both sides has very little room to be wrong and
still verify, and adding test rows will not find what is not there.

So the standing-conditions block is defence in depth, not the primary net, and
the honest claim for it is narrower than "it catches mistranslations": it is
that the four predicates are now checked by something *other than* the proof
structure that also depends on them, and that a systematic mistranslation
coherent across every Rust proof — the failure mode a self-consistent
verification cannot detect from the inside — now has to survive comparison with
Lean on ten states as well.

The second corruption did earn its keep, though, in a way that had nothing to do
with catching it: a range slip at `0 <= i` is invisible to every row whose only
bad gap is at a later index, and the block had no row violating at index `0`.
`unordered-at-0` exists because the experiment exposed that hole, not because
anything failed.

