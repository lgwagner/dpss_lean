# DPSS in Lean 4

A formalization of the **Decentralized Perimeter Surveillance System** —
Kingston, Beard & Holt's multi-UAV patrol protocol (IEEE T-RO, 2008), whose
published convergence proof was found false by model checking in 2019 and
corrected by Avigad & van Doorn in 2020–21.

**Scope:** Algorithm A (drones already hold correct coordination estimates),
continuous real time, `n` drones on the unit interval.

## Status

**Non-Zeno is proved** — the system cannot pack infinitely many events into a
finite stretch of time:

```lean
theorem nonZeno : NonZeno c hn        -- ∀ T : ℝ, ∃ k, T < (c.run hn k).time
```

This is the property the existing ACL2 mechanization carries as an *unproved
hypothesis* (`step-time-always-terminates`), and which Avigad–van Doorn argue
for but never mechanize.

Also proved: the model's invariants along any run (drones stay on the
perimeter, never overtake, escorts stay coherent), **Lemma 3.1** of the paper,
complete traces at `n = 2` and `n = 3` checked against the paper's own numbers,
and Theorem 2.1 at `n = 1`.

**Theorem 2.1 (`2 − 1/n`) is stated but not proved in general.** Lemma 3.2 is
most of the way; Lemmas 3.3–3.8 are untouched.

Everything is `sorry`-free and CI enforces it.

## Where to look

| File | What it is |
|---|---|
| **`STATUS.md`** | What is proved, what is **not**, and a full axiom audit. Written to be audited, not just read. §4 is the honest gap list. |
| **`INSIGHTS.md`** | The non-obvious things learned. Read this before extending the work. |
| `PLAN.md` | The original plan, including one recorded planning error. |
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
