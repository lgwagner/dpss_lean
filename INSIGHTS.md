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

A wrinkle found while trying to finish the argument, and the reason case 3 is
still open.

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
