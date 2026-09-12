/-
# DPSS — the events

`Dynamics.lean` handled flight with nobody turning. This file supplies the only
three things that make a drone turn.

Quoting the ACL2 paper's statement of the protocol, which is the crispest one:

> the only conditions under which a UAV is allowed to change direction are
> those previously mentioned: when it reaches a perimeter endpoint, when it
> starts escorting another UAV to their shared segment boundary, or when it
> separates from its neighbour at a shared segment boundary.

That exhaustiveness is what Avigad–van Doorn's Lemma 3.1 rests on, so it is
worth stating carefully rather than leaving implicit.

## Events move nobody

Every event in this file changes *directions only*. Positions are untouched —
an event is instantaneous, and the flying happens in `advance`. A pleasant
consequence is that events trivially preserve the ordering invariant, which we
record below as `adjOrdered_*`. Splitting "turn" from "fly" this way is what
keeps the two obligations independent.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §2; Greve–Davis–Humphrey, arXiv:2205.11697 §2.
-/

import Dpss.Dynamics

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## Setting one drone's direction

All three events are built from this. Positions and time are untouched. -/

/-- Override the direction of a single drone. -/
def setDir (c : Config n) (j : Fin n) (d : Dir) : Config n :=
  { c with dir := Function.update c.dir j d }

@[simp] theorem setDir_time (c : Config n) (j : Fin n) (d : Dir) :
    (c.setDir j d).time = c.time := rfl

@[simp] theorem setDir_pos (c : Config n) (j : Fin n) (d : Dir) (k : Fin n) :
    (c.setDir j d).pos k = c.pos k := rfl

@[simp] theorem setDir_dir_self (c : Config n) (j : Fin n) (d : Dir) :
    (c.setDir j d).dir j = d := by simp [setDir]

@[simp] theorem setDir_dir_ne (c : Config n) {j k : Fin n} (d : Dir) (hk : k ≠ j) :
    (c.setDir j d).dir k = c.dir k := by simp [setDir, hk]

/-- Since events do not move anyone, gaps survive them untouched. -/
@[simp] theorem gap_setDir (c : Config n) (j : Fin n) (d : Dir) (i : Fin n)
    (h : i.val + 1 < n) : (c.setDir j d).gap i h = c.gap i h := rfl

/-- A drone is distinct from its right-hand neighbour. Needed constantly, since
the meet and separation events write to both of them. -/
theorem nextIdx_ne (i : Fin n) (h : i.val + 1 < n) : nextIdx i h ≠ i := by
  intro hEq
  have : (nextIdx i h).val = i.val := by rw [hEq]
  simp [nextIdx_val] at this

/-! ## When each event fires -/

/-- Drone `i` has reached the left border of the perimeter heading into it.

Note this does *not* require `i` to be the leftmost drone. It would be wrong to
build that in: several drones can sit on the border at once, and the algorithm
turns any drone that reaches it. What *is* true is that everyone to `i`'s left
must be there too, which is `pos_eq_zero_of_le` below — a consequence of the
ordering invariant rather than a definitional stipulation. -/
def AtLeftBorder (c : Config n) (i : Fin n) : Prop :=
  c.pos i = 0 ∧ c.dir i = Dir.left

/-- Drone `i` has reached the right border heading into it. -/
def AtRightBorder (c : Config n) (i : Fin n) : Prop :=
  c.pos i = 1 ∧ c.dir i = Dir.right

/-- Drones `i` and `i+1` occupy the same point. -/
def CoLocated (c : Config n) (i : Fin n) (h : i.val + 1 < n) : Prop :=
  c.gap i h = 0

/-- An *escort*: a co-located pair travelling as a unit. Because all drones move
at the same speed, a co-located pair pointing the same way stays co-located —
the escort needs no special representation, it is an emergent consequence of
uniform speed. -/
def Escorting (c : Config n) (i : Fin n) (h : i.val + 1 < n) : Prop :=
  c.CoLocated i h ∧ c.dir i = c.dir (nextIdx i h)

/-- A separation is due: the pair sits on the boundary between their intervals
and must split, each returning to its own side.

**This deliberately does not require the pair to be escorting.** An earlier
version did, and it was wrong. Consider two drones approaching each other and
meeting *exactly* on their shared boundary — the paper's **bounce**, a meet and
a separation coinciding. Right up to the instant they meet their headings are
*opposite*, so they are not escorting, so a separation predicate demanding
`Escorting` is false and no separation fires. The meet branch then takes over
and sends the right-hand drone the wrong way, out of its own interval.

Co-location on the shared boundary is the real condition, however the pair got
there — escorting and arrived, or met head-on. For a pair that has just
separated and is still on the boundary this fires again and reinstates the
headings they already have, which is harmless. -/
def AtSeparation (c : Config n) (i : Fin n) (h : i.val + 1 < n) : Prop :=
  c.CoLocated i h ∧ c.pos i = commonEnd i

/-! ## What each event does -/

open Classical in
/-- The heading an escorting pair adopts: whichever way points at their common
endpoint. If they met exactly *on* the common endpoint the meet and the
separation coincide — that is the paper's *bounce* — and `AtSeparation` takes
priority, sending each drone back into its own interval. -/
noncomputable def escortDir (c : Config n) (i : Fin n) : Dir :=
  if c.pos i < commonEnd i then Dir.right else Dir.left

/-- **Meet event.** Two drones become co-located and head off together toward
their shared boundary. -/
noncomputable def doMeet (c : Config n) (i : Fin n) (h : i.val + 1 < n) : Config n :=
  (c.setDir i (c.escortDir i)).setDir (nextIdx i h) (c.escortDir i)

/-- **Separation event.** An escorting pair at their shared boundary splits, each
turning back into its own interval: the left drone heads left, the right drone
heads right. -/
def doSeparate (c : Config n) (i : Fin n) (h : i.val + 1 < n) : Config n :=
  (c.setDir i Dir.left).setDir (nextIdx i h) Dir.right

/-- **Border event.** A drone at a perimeter endpoint reverses. -/
def doBorder (c : Config n) (i : Fin n) : Config n :=
  c.setDir i (c.dir i).flip

/-! ## Events do not disturb positions

Immediate, but worth having as named lemmas: it is precisely why the ordering
obligation lives entirely in `Dynamics.lean` and not here. -/

@[simp] theorem doMeet_pos (c : Config n) (i : Fin n) (h : i.val + 1 < n) (k : Fin n) :
    (c.doMeet i h).pos k = c.pos k := rfl

@[simp] theorem doSeparate_pos (c : Config n) (i : Fin n) (h : i.val + 1 < n) (k : Fin n) :
    (c.doSeparate i h).pos k = c.pos k := rfl

@[simp] theorem doBorder_pos (c : Config n) (i : Fin n) (k : Fin n) :
    (c.doBorder i).pos k = c.pos k := rfl

theorem adjOrdered_doMeet {c : Config n} (i : Fin n) (h : i.val + 1 < n)
    (hc : c.AdjOrdered) : (c.doMeet i h).AdjOrdered := hc

theorem adjOrdered_doSeparate {c : Config n} (i : Fin n) (h : i.val + 1 < n)
    (hc : c.AdjOrdered) : (c.doSeparate i h).AdjOrdered := hc

theorem adjOrdered_doBorder {c : Config n} (i : Fin n) (hc : c.AdjOrdered) :
    (c.doBorder i).AdjOrdered := hc

/-! ## What the events establish

These are the facts the convergence proof quotes by name. -/

/-- After a meet, the pair is escorting: both point the same way. This is what
makes the escort work — and, because speeds are uniform, what makes it persist. -/
theorem escorting_doMeet {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (hco : c.CoLocated i h) : (c.doMeet i h).Escorting i h := by
  refine ⟨hco, ?_⟩
  unfold doMeet
  rw [setDir_dir_self]
  rw [setDir_dir_ne _ _ (nextIdx_ne i h).symm, setDir_dir_self]

/-- The heading a meet installs on the left drone of the pair. -/
@[simp] theorem doMeet_dir_self (c : Config n) (i : Fin n) (h : i.val + 1 < n) :
    (c.doMeet i h).dir i = c.escortDir i := by
  unfold doMeet
  rw [setDir_dir_ne _ _ (nextIdx_ne i h).symm, setDir_dir_self]

/-- And on the right drone — the same one, which is what makes it an escort. -/
@[simp] theorem doMeet_dir_next (c : Config n) (i : Fin n) (h : i.val + 1 < n) :
    (c.doMeet i h).dir (nextIdx i h) = c.escortDir i := by
  unfold doMeet
  rw [setDir_dir_self]

/-- After a separation the left drone heads left. Lemma 3.2 of the paper opens
with exactly this observation. -/
@[simp] theorem doSeparate_dir_left (c : Config n) (i : Fin n) (h : i.val + 1 < n) :
    (c.doSeparate i h).dir i = Dir.left := by
  unfold doSeparate
  rw [setDir_dir_ne _ _ (nextIdx_ne i h).symm, setDir_dir_self]

/-- After a separation the right drone heads right. -/
@[simp] theorem doSeparate_dir_right (c : Config n) (i : Fin n) (h : i.val + 1 < n) :
    (c.doSeparate i h).dir (nextIdx i h) = Dir.right := by
  unfold doSeparate
  rw [setDir_dir_self]

/-- A separating pair is *not* approaching: the left one goes left and the right
one goes right, so their gap immediately grows. They therefore cannot re-collide
without first turning around, which is what lets Lemma 3.2's induction get
going. -/
theorem not_approaching_doSeparate (c : Config n) (i : Fin n) (h : i.val + 1 < n) :
    ¬ (c.doSeparate i h).Approaching i h := by
  intro hA
  have hl : (c.doSeparate i h).dir i = Dir.left := doSeparate_dir_left c i h
  rw [hA.1] at hl
  exact Dir.noConfusion hl

/-- A drone at the left border turns around and heads right. -/
theorem doBorder_dir_of_left {c : Config n} {i : Fin n} (hb : c.AtLeftBorder i) :
    (c.doBorder i).dir i = Dir.right := by
  unfold doBorder
  rw [setDir_dir_self, hb.2]
  rfl

/-- A drone at the right border turns around and heads left. -/
theorem doBorder_dir_of_right {c : Config n} {i : Fin n} (hb : c.AtRightBorder i) :
    (c.doBorder i).dir i = Dir.left := by
  unfold doBorder
  rw [setDir_dir_self, hb.2]
  rfl

/-- An escort really does stay together: a co-located pair pointing the same way
has zero separation rate, so flying forward keeps them co-located. No special
"grouped" representation is needed. -/
theorem sepRate_eq_zero_of_escorting {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (he : c.Escorting i h) : c.sepRate i h = 0 := by
  unfold sepRate
  rw [he.2]
  ring

theorem coLocated_advance_of_escorting {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (he : c.Escorting i h) (dt : ℝ) : (c.advance dt).CoLocated i h := by
  unfold CoLocated
  rw [gap_advance, sepRate_eq_zero_of_escorting he]
  have : c.gap i h = 0 := he.1
  rw [this]
  ring

end Config

end DPSS
