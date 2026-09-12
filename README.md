# DPSS in Lean 4

A formalization of the **Decentralized Perimeter Surveillance System** —
Kingston, Beard & Holt's multi-UAV patrol protocol (IEEE T-RO, 2008), whose
published convergence proof was found false by model checking in 2019 and
corrected by Avigad & van Doorn in 2020–21.

**Scope:** Algorithm A (drones already hold correct coordination estimates),
continuous real time, `n` drones on the unit interval.

## Branches

You are on **`safety`**, which is building a drone-level controller on top of
the finished mathematics. The baseline is elsewhere and is not disturbed:

| | |
|---|---|
| tag **`v1.0-lean-baseline`** | the Lean formalization of Avigad–van Doorn with extensions, and nothing else. **Start here** if you want the mathematics without the engineering. |
| branch `main` | that baseline, as it continues |
| branch `rust-verus` | **E1**, complete: an executable implementation in Rust with Verus proving key equivalence to the Lean specification — `100 verified, 0 errors` |
| branch **`safety`** (here) | **Track A**: fencing and separation guarantees for a real vehicle. `rust-verus` plus `Dpss/Fence.lean`, `Dpss/Standoff.lean`, `Dpss/Separation.lean`, `Dpss/Kinematics.lean`, `Dpss/Continuous.lean`, `Dpss/Comms.lean` and the matching Verus modules |

## Status

**Theorem 2.1 is proved.** For every `n`, from any legitimate starting
configuration, all drones are confined to their own segments by time `2 − 1/n`:

```lean
theorem convergesBy (hn : 0 < n) (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) : ConvergesBy c hn
```

and in the stronger real-time form — at every *instant* from `2 − 1/n` on, not
merely at the event times (`sync_at_of_time`). The bound is **exact**, and
`bound_sharp` shows it is attained: no smaller constant is correct.

**Non-Zeno is proved** too — the system cannot pack infinitely many events into
a finite stretch of time:

```lean
theorem nonZeno : NonZeno c hn        -- ∀ T : ℝ, ∃ k, T < (c.run hn k).time
```

This is the property the existing ACL2 mechanization carries as an *unproved
hypothesis* (`step-time-always-terminates`), and which Avigad–van Doorn argue
for but never mechanize.

Also proved: the model's invariants along any run (drones stay on the
perimeter, never overtake, escorts stay coherent), **Lemmas 3.1 through 3.7**,
complete traces at `n = 2` and `n = 3` checked against the paper's own numbers
— steady, converging, and one with a genuine three-way meeting — and a
measurement of exactly how much of the model's event-priority order is a real
choice (seven of eight competing cases: none).

Everything is `sorry`-free and CI enforces it.

The bound is also shown **attained for every `n`** (`bound_sharp_general`), and
Theorem 2.1 is proved for **every resolution** of the nondeterminism the paper
leaves open — `step` is modelled as a relation, and the relation is proved to
collapse to a function on every state the algorithm can reach
(`convergesBy_of_isRun`), which is what the paper asserts and does not prove.

### On this branch: the drone-level guarantees

**Track A is complete.** A drone-level controller with fencing and separation
guarantees, in Lean and in Verus, against a vehicle described by numbers an
airframe report contains and a network described by a bound on message age.

**The fence is proved, and proved sharp.** A single drone under a sampled
controller, with three idealizations of the team model removed at once — point
mass at unit speed, instantaneous reversal, perfect sensing:

```lean
theorem Traj.low_nonneg (hM : V.Dmax + V.turn + V.eps ≤ M) (h0 : T.Safe 0) (k : ℕ) :
    0 ≤ T.low k                       -- the drone never crosses the fence
```

`low k` is the lowest position reached on a whole leg, so this covers the time
*between* samples — yet the proof is a discrete induction with no analysis in
it. `margin_sharp` proves the converse: for **every** smaller margin there is a
conforming trajectory that crosses. Both fences; the right one by an explicit
reflection. The same theorem is in Verus (`rust/src/fence.rs`), and the verified
controller drives a trace that breaches exactly when the margin is short.

**Margined separation is proved, at the model and at the controller.** The shear
`yᵢ = xᵢ − i·d` turns the separation requirement into the ordering invariant the
whole development already rests on, and `toPoint`/`fromPoint` are mutually
inverse — so the standoff model *is* the point model in other coordinates, with
the segments respaced (each narrowing by `1 − (n−1)d`, with a buffer of exactly
`d` that two neighbouring drones cover precisely when the standoff is two
half-footprints). Hence Theorem 2.1 under standoff:

```lean
theorem sConvergesBy (hL : 0 < usable n d) (hsi : c.SInvariant d hn)
    (hab : c.SApartOnBoundaries d) : c.SConvergesBy d hn
```

— every drone inside its own respaced segment from `(2 − 1/n)·(1 − (n−1)d)` on,
*sooner* than the point bound, because the team has less ground to cover. And at
the controller, a pair under sampled sensing holds `d ≤ gap` at every instant,
which is the fence theorem applied to the excess separation with the vehicle
doubled.

**Bounded speed is a change of clock.** If every drone has the same speed at the
same instant, `τ(t) = ∫₀ᵗ v` reparameterizes the bounded-speed system into the
unit-speed one — so Theorem 2.1 holds by real time `(2 − 1/n) / vmin`
(`Dpss/Kinematics.lean`). Convergence uses only the *lower* speed bound; and
`vmin_zero_stalls` proves a positive one is required, not merely convenient.

**And `Dmax` is derived, not assumed.** `Dpss/Continuous.lean` sets
`Dmax = V · Δt` from a speed bound and a sample period, converts a derivative
bound into it by the mean value theorem, and concludes the fence holds at every
real instant with no sampling in the statement. What it deliberately does *not*
derive is the turn allowance: that is control authority, not kinematics, and no
speed bound determines it.

**And the network can degrade.** A report `a` samples old localizes a neighbour
to `eps + a·Dmax`, so the separation margin inflates by exactly `A·Dmax` and
delay and loss become one hypothesis (`Dpss/Comms.lean`). More useful still: the
requirement is **transient**. Once the team has converged, every drone is in its
own respaced segment and consecutive segments are exactly `d` apart, so

```lean
theorem separated_of_segments (hx : x ≤ standoffRightEnd d i)
    (hy : standoffLeftEnd d (nextIdx i h) ≤ y) : d ≤ y - x
```

— confinement *is* separation, with no observation, no message and no
controller. That makes the degraded-mode fallback the algorithm's own steady
state: hold to your own segment. It is inside the fence, separated, and
`hold_covers` shows it starves nobody.

**What is not done** is in `STATUS.md` §4, which is written to be read. The
work package is complete; what remains outside it is Algorithm B, and a
phase-1 result that this scope cannot reach by construction.

## Where to look

| File | What it is |
|---|---|
| **`GUIDE.md`** | **Start here.** A guide to the whole work package — every item, what it claimed, how it was proved, and what it cost — with deep links into the source for each declaration named. |
| **`STATUS.md`** | What is proved, what is **not**, and a full axiom audit. Written to be audited, not just read. §4 is the honest gap list. |
| **`INSIGHTS.md`** | The non-obvious things learned. Read this before extending the work. |
| **`PLAN.md`** | The roadmap. The work package is complete, so this now holds the **backlog** — new directions, sized and scoped. |
| `CHANGELOG.md` | What changed and when, newest first — including what each session did **not** finish. |
| `rust/README.md` | **E1** — the executable Rust implementation verified with Verus. `rust/PLAN.md` is its build plan, `rust/REFINEMENT.md` the obligations it does *not* discharge. |
| `Dpss/Fence.lean` | **S2** — the margined fence: the one guarantee that needs no coordination. Stated over an ordered ring, so `ℤ` is an instance. |
| `Dpss/FenceInt.lean` | **S6a** — that fence at `ℤ`, in the shape `rust/src/fence.rs` has. Read the two side by side. |
| `Dpss/Standoff.lean` | **S0/S3** — the standoff change of coordinates, the scheduler correspondence, and Theorem 2.1 under standoff. |
| `Dpss/Separation.lean` | **S3** — margined separation at the controller: the fence theorem, instantiated. |
| `Dpss/Kinematics.lean` | **S1** — bounded speed as a change of clock, and why `vmin > 0` is required. |
| `Dpss/Continuous.lean` | **S4** — where `Dmax` comes from: `V · Δt`, and the fence at every real instant. |
| `Dpss/Comms.lean` | **S5** — staleness as sensing error, and why the communication requirement is transient. |
| `PLAN-original.md` | The original scoping plan, including one recorded planning error. |
| `dpss-perimeter-surveillance-brief.md` | Literature brief, with corrections from the primary sources. |
| `Dpss/` | The development. Each file opens with prose explaining the mathematics. |

## Building

```bash
lake build                        # Lean 4.33.1 + Mathlib v4.33.1
python3 scripts/audit.py          # every theorem's axiom dependencies
python3 scripts/refresh_status.py # regenerate STATUS.md's generated blocks
python3 scripts/refresh_guide_links.py  # re-point GUIDE.md's deep links at the source
```

`scripts/audit.py` fails if any theorem depends on `sorryAx`; it runs in CI.

The Rust half needs the pinned Verus toolchain (`scripts/setup_verus.sh`):

```bash
./rust/verify.sh                  # expect "0 errors"
./rust/traces.sh                  # expect "traces agree with Lean"
python3 scripts/no_proof_holes.py # no assume/admit/external_body
```

## Sources

- Kingston, Beard, Holt. *Decentralized Perimeter Surveillance Using a Team of
  UAVs.* IEEE T-RO 24(6), 2008.
- Davis, Humphrey, Kingston. *When Human Intuition Fails.* CAV 2019.
- Avigad, van Doorn. *Progress on a Perimeter Surveillance Problem.*
  arXiv:2008.04262.
- Greve, Davis, Humphrey. *A Mechanized Proof of Bounded Convergence Time for
  DPSS Algorithm A.* arXiv:2205.11697.
