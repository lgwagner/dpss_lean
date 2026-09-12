/-
# DPSS — the time to the next event

`Schedule.lean` gave each event kind its own due time. This file takes the
**minimum** over all of them, and proves the fact that matters:

> if no event is due right now, the time to the next one is **strictly
> positive**.

That is what rules out zero-length steps, and it is the local half of non-Zeno.

## Why this is the interesting theorem

ACL2 requires a termination proof for every recursive function. The existing
DPSS mechanization could not supply one for its event-stepper, so it admitted
the function as *partial* and carried `(step-time-always-terminates)` as an
unproved hypothesis into its top-level convergence theorem. This file is the
first half of discharging that obligation.

Strict positivity alone is not yet non-Zeno: infinitely many strictly positive
steps can still sum to a finite time. The second half — a uniform lower bound
that stops the steps shrinking to nothing — follows Avigad–van Doorn §2 and
comes next.

## A modelling decision, recorded

`borderTime` is computed for **every** drone, not only the two on the ends. For
an interior drone that number does not correspond to a reachable border event —
a neighbour is in the way. Including it is nonetheless harmless, because under
`OnPerimeter` and ordering a spurious border time can never be strictly smaller
than the genuine event that preempts it. Keeping it total avoids a case split
in every downstream proof, and guarantees each drone always contributes at
least one candidate, which is what makes the minimum well defined.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §2; Greve–Davis–Humphrey, arXiv:2205.11697 §4.1.
-/

import Dpss.Schedule

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## Time to the border a drone is actually heading for -/

/-- How long until this drone would reach the border it is heading towards.
Total: every drone is heading one way or the other, so every drone always has
at least one candidate event time. -/
noncomputable def borderTime (c : Config n) (i : Fin n) : ℝ :=
  if c.dir i = Dir.left then c.pos i else 1 - c.pos i

theorem borderTime_nonneg {c : Config n} (hp : c.OnPerimeter) (i : Fin n) :
    0 ≤ c.borderTime i := by
  unfold borderTime
  split_ifs with hd
  · exact (hp i).1
  · have := (hp i).2; linarith

/-- **A drone not currently at a border has strictly positive time to reach
one.** The first of the three positivity facts the main theorem needs. -/
theorem borderTime_pos {c : Config n} (hp : c.OnPerimeter) {i : Fin n}
    (hl : ¬ c.AtLeftBorder i) (hr : ¬ c.AtRightBorder i) :
    0 < c.borderTime i := by
  unfold borderTime
  split_ifs with hd
  · have hne : c.pos i ≠ 0 := fun h0 => hl ⟨h0, hd⟩
    have h0 := (hp i).1
    exact lt_of_le_of_ne h0 (Ne.symm hne)
  · have hdr : c.dir i = Dir.right := by
      rcases Dir.eq_left_or_right (c.dir i) with h | h
      · exact absurd h hd
      · exact h
    have hne : c.pos i ≠ 1 := fun h1 => hr ⟨h1, hdr⟩
    have h1 := (hp i).2
    have : c.pos i < 1 := lt_of_le_of_ne h1 hne
    linarith

/-! ## When a separation is exactly due -/

/-- A separation is due precisely when the pair sits on its shared boundary.
The direction factor cannot vanish, so it never interferes. -/
theorem separationTime_eq_zero_iff (c : Config n) (i : Fin n) :
    c.separationTime i = 0 ↔ c.pos i = commonEnd i := by
  unfold separationTime
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · linarith [sub_eq_zero.mp h]
    · exact absurd h (Dir.sign_ne_zero _)
  · intro h
    left
    rw [h]
    ring

/-! ## "No event is due right now"

A meet is due when a pair is co-located *and closing* — that is the instant they
cross. A co-located pair moving apart is a pair that has just separated, and no
meet is due for it. Getting this distinction right matters: were it merely
`CoLocated`, the predicate would exclude every mid-escort configuration, which
is a perfectly ordinary state. -/

/-- Escorts point at the boundary they are escorting to. Guaranteed by a meet
event (`separationTime_nonneg_doMeet`); assumed of a start configuration. An
escort heading *away* from its boundary is a state the algorithm never builds. -/
def EscortsCoherent (c : Config n) : Prop :=
  ∀ (i : Fin n) (h : i.val + 1 < n), c.Escorting i h → 0 ≤ c.separationTime i

/-- No event of any kind is due at this instant. -/
structure NoEventDue (c : Config n) : Prop where
  notLeftBorder : ∀ i : Fin n, ¬ c.AtLeftBorder i
  notRightBorder : ∀ i : Fin n, ¬ c.AtRightBorder i
  notMeet : ∀ (i : Fin n) (h : i.val + 1 < n),
    ¬ (c.CoLocated i h ∧ c.Approaching i h)
  notSeparation : ∀ (i : Fin n) (h : i.val + 1 < n), ¬ c.AtSeparation i h

/-- An escorting pair that is not yet at its boundary has strictly positive time
left to run. -/
theorem separationTime_pos_of_escorting {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (hec : c.EscortsCoherent) (he : c.Escorting i h)
    (hns : ¬ c.AtSeparation i h) : 0 < c.separationTime i := by
  have hge : 0 ≤ c.separationTime i := hec i h he
  have hne : c.separationTime i ≠ 0 := by
    intro h0
    exact hns ⟨he, (separationTime_eq_zero_iff c i).mp h0⟩
  exact lt_of_le_of_ne hge (Ne.symm hne)

/-- An approaching pair that is not yet co-located has strictly positive time
left before it meets. -/
theorem meetTime_pos_of_approaching {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (ha : c.AdjOrdered) (hA : c.Approaching i h)
    (hnm : ¬ (c.CoLocated i h ∧ c.Approaching i h)) : 0 < c.meetTime i h := by
  have hge : 0 ≤ c.gap i h := ha i h
  have hne : c.gap i h ≠ 0 := fun h0 => hnm ⟨h0, hA⟩
  exact meetTime_pos (lt_of_le_of_ne hge (Ne.symm hne))

/-! ## The minimum -/

open Classical in
/-- The earliest event involving drone `i`: whichever of its own border
deadline and its pair deadline comes first. Always defined — the border term
guarantees a candidate even when no pair event is pending. -/
noncomputable def droneNextTime (c : Config n) (i : Fin n) : ℝ :=
  if h : i.val + 1 < n then
    if c.Approaching i h then min (c.borderTime i) (c.meetTime i h)
    else if c.Escorting i h then min (c.borderTime i) (c.separationTime i)
    else c.borderTime i
  else c.borderTime i

/-- **Every drone's next event is strictly in the future**, given that none is
due right now. -/
theorem droneNextTime_pos {c : Config n} (hp : c.OnPerimeter)
    (ha : c.AdjOrdered) (hec : c.EscortsCoherent) (hnd : c.NoEventDue)
    (i : Fin n) : 0 < c.droneNextTime i := by
  have hb : 0 < c.borderTime i :=
    borderTime_pos hp (hnd.notLeftBorder i) (hnd.notRightBorder i)
  unfold droneNextTime
  split_ifs with h hA hE
  · exact lt_min hb (meetTime_pos_of_approaching ha hA (hnd.notMeet i h))
  · exact lt_min hb (separationTime_pos_of_escorting hec hE (hnd.notSeparation i h))
  · exact hb
  · exact hb

/-- With at least one drone, the index type is inhabited, so the minimum below
is taken over a nonempty set.

Stated as a named lemma rather than written inline: given inline, the anonymous
constructor elaborates at the *unfolded* type `∃ x, x ∈ univ` rather than
`Finset.Nonempty`, and downstream lemmas about `inf'` then fail to apply. -/
theorem univ_fin_nonempty (hn : 0 < n) :
    (Finset.univ : Finset (Fin n)).Nonempty :=
  ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/-- The time until *something* happens: the earliest deadline across the team. -/
noncomputable def timeToNextEvent (c : Config n) (hn : 0 < n) : ℝ :=
  Finset.univ.inf' (univ_fin_nonempty hn) c.droneNextTime

/-- **The main result of this file: steps make progress.**

If no event is due at this instant, the team can fly for a strictly positive
stretch of time before anything happens. No zero-length steps, so an event
sequence cannot stall.

This is the local half of non-Zeno. It is *not* yet non-Zeno: infinitely many
strictly positive steps can still sum to something finite. Ruling that out needs
a uniform lower bound on the steps, which is the next target. -/
theorem timeToNextEvent_pos {c : Config n} (hn : 0 < n) (hp : c.OnPerimeter)
    (ha : c.AdjOrdered) (hec : c.EscortsCoherent) (hnd : c.NoEventDue) :
    0 < c.timeToNextEvent hn := by
  unfold timeToNextEvent
  exact (Finset.lt_inf'_iff _).mpr
    (fun i _ => droneNextTime_pos hp ha hec hnd i)

/-- The time to the next event never runs backwards. -/
theorem timeToNextEvent_nonneg {c : Config n} (hn : 0 < n) (hp : c.OnPerimeter)
    (ha : c.AdjOrdered) (hec : c.EscortsCoherent) :
    0 ≤ c.timeToNextEvent hn := by
  unfold timeToNextEvent
  refine Finset.le_inf' _ _ (fun i _ => ?_)
  unfold droneNextTime
  have hb : 0 ≤ c.borderTime i := borderTime_nonneg hp i
  split_ifs with h hA hE
  · exact le_min hb (meetTime_nonneg (ha i h))
  · exact le_min hb (hec i h hE)
  · exact hb
  · exact hb

/-- The team-wide deadline is no later than any individual drone's. Lets a
proof about one drone bound the global step. -/
theorem timeToNextEvent_le {c : Config n} (hn : 0 < n) (i : Fin n) :
    c.timeToNextEvent hn ≤ c.droneNextTime i :=
  Finset.inf'_le _ (Finset.mem_univ i)

end Config

end DPSS
