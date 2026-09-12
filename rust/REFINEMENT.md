# What a verified *controller* would additionally require

**Scoped, not built.** This file states the obligation precisely so that the
follow-on is a known quantity rather than a guess, and says what new Lean it would
need. Nothing here is proved.

## What exists, and what it is not

`rust/src/exec.rs` is a **global event-stepper**: it holds the whole ensemble,
computes the time to the next event across all drones, advances everyone, and
applies every due event at once. Verus proves it computes exactly the specified
step and preserves the standing conditions.

That is a faithful implementation of *the Lean specification*, which is itself a
centralized model of the algorithm. It is **not** what you would fly. DPSS is
decentralized: each drone holds local state, senses only its immediate
neighbours, and decides its own heading. A verified controller is a different
artefact, and the gap between them is a refinement theorem that does not yet
exist in any form.

## The good news first

Three things that might have been obstacles are not.

**Every event is already local.** A border event is a drone at `0` or at the
perimeter. A meet is co-location with an immediate neighbour. A separation is
co-location with an immediate neighbour *at the boundary they share*. None of the
three consults a drone more than one index away. `Dpss/Step.lean`'s `SepRight`,
`SepLeft`, `MeetRight`, `MeetLeft` are already written as predicates over a drone
and its two neighbours.

**Every quantity a drone needs is local.** Under Algorithm A the estimates are
correct by assumption, so `left_end i` and `right_end i` are constants the drone
knows. `gap`, `sep_rate`, `border_time`, `meet_time` and `separation_time` all read
only the drone and one neighbour.

**The heading update is already a function of position, not of history.**
`new_dir` reads the configuration and nothing else, so a controller has nothing to
remember. (`HaveMetBy` is history-shaped, but it appears only in the *convergence
proof*, never in the model — see `STATUS.md` §9's note on D2.)

## The three obligations that remain

### 1. The step length is global; a drone cannot compute it

`time_to_next_event` is a minimum over **all** drones. A controller does not know
the far end of the perimeter's deadline, and must not need to.

Physically this is not a real difficulty: a drone flies at unit speed and reacts
when something happens *to it*. The refinement is therefore

> continuous motion, plus local event detection, realizes the global event
> sequence

and the content is that the earliest event anywhere is the earliest event
somewhere, so a drone that reacts to its own events and is otherwise undisturbed
follows the same trajectory. Stated in Lean, roughly:

```lean
theorem local_realizes_global
    (f : ℕ → Config n) (hrun : IsRun c hn f) :
    ∀ i k, (f (k+1)).pos i = (f k).pos i + ((f k).dir i).sign * localDt (f k) i
```
— where `localDt` is the drone's *own* deadline, and the theorem says the global
minimum never cuts a drone's motion short of it. **This is the load-bearing one.**

### 2. Simultaneity has to become independence

The global model fires every due event at one instant, which is why `new_dir` is a
function of the whole configuration rather than a composition of per-drone
updates — `Dpss/Step.lean` says so explicitly, and it was a deliberate choice.

Distributed, the events fire independently and in no particular order. The
obligation is that the order does not matter: applying the due updates in any
sequence gives the configuration `new_dir` gives. Note this is *not* the
nondeterminism `Dpss/Nondeterminism.lean` closes — that one is about which
neighbour a drone escorts, and is proved not to arise. This is about the order of
independent updates, and is new.

### 3. Zero-time cascades

A drone turning can put a neighbour in a state where it must turn too, at the same
instant. In the global model that is one application of `new_dir`. Distributed, it
is a chain of reactions with no clock between them.

`Dpss/Examples.lean` and `Dpss/ThreeConverge.lean` both exercise this — the
three-way meeting at `t = 2/3` is exactly such a cascade — and the model handles it
because `new_dir` sees the whole state. A controller would need the cascade proved
to terminate and to reach the same fixed point. The finiteness is not in doubt
(there are `n` drones); the fixed point is the obligation.

## What it would cost

| | |
|---|---|
| New Lean | a controller model, `localDt`, and the three theorems above |
| New Verus | the controller itself — small, once the specification exists |
| Size | **L**, and the Lean is most of it |

The honest summary: the Rust side of a verified controller is the easy half. The
hard half is that the specification it would be verified against does not exist
yet, and writing it is a Lean problem, not a Rust one.

## Why it was not done here

`PLAN.md` E1 asked for an implementation verified against *this* specification.
Building a controller instead would have meant inventing a second specification and
verifying against that — which is exactly the failure mode this project is set up
to avoid, and which `GUIDE.md` §3 records the one instance of: a wrong definition
supporting a flawless proof.
