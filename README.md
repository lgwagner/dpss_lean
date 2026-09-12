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
| branch `rust-verus` | **E1**, complete: an executable implementation in Rust with Verus proving key equivalence to the Lean specification — `87 verified, 0 errors` |
| branch **`safety`** (here) | **Track A**: fencing and separation guarantees for a real vehicle. `rust-verus` plus `Dpss/Fence.lean`, `Dpss/Standoff.lean` and `rust/src/fence.rs` |

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

**Margined separation is a change of constants, not a rewrite.**
`Dpss/Standoff.lean` proves the shear `yᵢ = xᵢ − i·d` turns the separation
requirement into the ordering invariant the whole development already rests on,
that the dynamics commute under it (`toPoint_advance`), and that the assigned
segments respace consistently — each narrowing by `1 − (n−1)d`, with a buffer of
exactly `d` that two neighbouring drones cover precisely when the standoff is
two half-footprints.

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
| `Dpss/Fence.lean` | **S2** — the margined fence: the one guarantee that needs no coordination. |
| `Dpss/Standoff.lean` | **S0** — the standoff shear, and the verdict that margined separation is a change of constants. |
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
