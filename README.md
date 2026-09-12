# DPSS in Lean 4

A formalization of the **Decentralized Perimeter Surveillance System** —
Kingston, Beard & Holt's multi-UAV patrol protocol (IEEE T-RO, 2008), whose
published convergence proof was found false by model checking in 2019 and
corrected by Avigad & van Doorn in 2020–21.

**Scope:** Algorithm A (drones already hold correct coordination estimates),
continuous real time, `n` drones on the unit interval.

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

**What is not done** is in `STATUS.md` §4, which is written to be read. The
work package is complete; what remains outside it is Algorithm B, and a
phase-1 result that this scope cannot reach by construction.

## Where to look

| File | What it is |
|---|---|
| **`GUIDE.md`** | **Start here.** A reader's guide to the convergence proof: what it claims, how the pieces fit, what to read in what order, and how to check it. |
| **`STATUS.md`** | What is proved, what is **not**, and a full axiom audit. Written to be audited, not just read. §4 is the honest gap list. |
| **`INSIGHTS.md`** | The non-obvious things learned. Read this before extending the work. |
| **`PLAN.md`** | **Work yet to be done** — the roadmap. Start here to pick up the work. |
| `CHANGELOG.md` | What changed and when, newest first — including what each session did **not** finish. |
| `PLAN-original.md` | The original scoping plan, including one recorded planning error. |
| `dpss-perimeter-surveillance-brief.md` | Literature brief, with corrections from the primary sources. |
| `Dpss/` | The development. Each file opens with prose explaining the mathematics. |

## Building

```bash
lake build                        # Lean 4.33.1 + Mathlib v4.33.1
python3 scripts/audit.py          # every theorem's axiom dependencies
python3 scripts/refresh_status.py # regenerate STATUS.md's generated blocks
```

`scripts/audit.py` fails if any theorem depends on `sorryAx`; it runs in CI.

## Sources

- Kingston, Beard, Holt. *Decentralized Perimeter Surveillance Using a Team of
  UAVs.* IEEE T-RO 24(6), 2008.
- Davis, Humphrey, Kingston. *When Human Intuition Fails.* CAV 2019.
- Avigad, van Doorn. *Progress on a Perimeter Surveillance Problem.*
  arXiv:2008.04262.
- Greve, Davis, Humphrey. *A Mechanized Proof of Bounded Convergence Time for
  DPSS Algorithm A.* arXiv:2205.11697.
