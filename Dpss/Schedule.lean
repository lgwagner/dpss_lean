/-
# DPSS — when the next event happens

`Events.lean` said *what* each event does. This file says *when* each becomes
due: given a configuration, how long must the team fly before a particular
event fires?

Each event kind gets a time, and each time gets a **correctness theorem**
saying that flying for exactly that long really does establish the event's
precondition. That pairing is the point. A scheduling function that returns
plausible-looking numbers unrelated to the events it claims to schedule would
sail through a proof of convergence and mean nothing.

## Why this file is the interesting one

The eventual goal here is **non-Zeno**: that the team cannot pack infinitely
many events into a finite stretch of time. The existing ACL2 mechanization of
DPSS could not prove this. Its event-stepper was admitted as a partial function
and `(step-time-always-terminates)` is carried as an unproved hypothesis all
the way into its top-level convergence theorem. Avigad–van Doorn give an
argument for it (§2) but never mechanize it.

So this file, and not the headline convergence bound, is where a Lean
development has something new to say. See `STATUS.md` §5.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §2.
-/

import Dpss.Events

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## Who can be at a border

The border predicates in `Events.lean` deliberately do not stipulate which
drone is involved. These two lemmas recover the expected structure from the
ordering invariant instead, which is the honest way round: it is a theorem
about the configuration, not a definitional convenience. -/

/-- If a drone sits on the left border, so does everyone to its left. They are
pinned between that drone's position and the edge of the perimeter. -/
theorem pos_eq_zero_of_le {c : Config n} (ho : c.Ordered) (hp : c.OnPerimeter)
    {i j : Fin n} (hij : j ≤ i) (hi : c.pos i = 0) : c.pos j = 0 := by
  have h1 : c.pos j ≤ c.pos i := ho j i hij
  have h2 : 0 ≤ c.pos j := (hp j).1
  rw [hi] at h1
  linarith

/-- Symmetrically on the right. -/
theorem pos_eq_one_of_ge {c : Config n} (ho : c.Ordered) (hp : c.OnPerimeter)
    {i j : Fin n} (hij : i ≤ j) (hi : c.pos i = 1) : c.pos j = 1 := by
  have h1 : c.pos i ≤ c.pos j := ho i j hij
  have h2 : c.pos j ≤ 1 := (hp j).2
  rw [hi] at h1
  linarith

/-- A drone on the left border is co-located with every drone to its left, so
those pairs have a meet event due immediately. -/
theorem coLocated_of_atLeftBorder {c : Config n} (ho : c.Ordered)
    (hp : c.OnPerimeter) {i : Fin n} (h : i.val + 1 < n)
    (hb : c.pos (nextIdx i h) = 0) : c.CoLocated i h := by
  unfold CoLocated gap
  have hle : i ≤ nextIdx i h := by
    rw [Fin.le_def, nextIdx_val]; omega
  rw [hb, pos_eq_zero_of_le ho hp hle hb]
  ring

/-! ## Time until each event

All three follow the same shape: a signed distance divided by unit speed. The
sign convention is chosen so the time is **nonnegative exactly when the event
is actually ahead of the drone** rather than behind it. -/

/-- Time until an escorting pair reaches its common endpoint and separates.

Written as a signed distance times the direction, so that it is nonnegative
precisely when the pair is heading *towards* the endpoint. If they are heading
away, this is negative, which is the correct answer: no separation is due. -/
noncomputable def separationTime (c : Config n) (i : Fin n) : ℝ :=
  (commonEnd i - c.pos i) * (c.dir i).sign

/-- Time until a drone heading left reaches the left border. -/
noncomputable def leftBorderTime (c : Config n) (i : Fin n) : ℝ := c.pos i

/-- Time until a drone heading right reaches the right border. -/
noncomputable def rightBorderTime (c : Config n) (i : Fin n) : ℝ := 1 - c.pos i

/-! ## Correctness of the schedule

Each theorem below says: fly for exactly this long, and the corresponding event
is genuinely due. These are the anti-vacuity guards for this file. -/

/-- **Flying for `separationTime` lands the drone exactly on its common
endpoint.** The two direction factors cancel, which is `Dir.sign_mul_self`. -/
theorem pos_eq_commonEnd_at_separationTime (c : Config n) (i : Fin n) :
    (c.advance (c.separationTime i)).pos i = commonEnd i := by
  simp only [advance_pos, separationTime]
  have hs : (c.dir i).sign * (c.dir i).sign = 1 := Dir.sign_mul_self _
  have key : (c.dir i).sign * ((commonEnd i - c.pos i) * (c.dir i).sign)
      = (commonEnd i - c.pos i) * ((c.dir i).sign * (c.dir i).sign) := by ring
  rw [key, hs, mul_one]
  ring

/-- An escorting pair stays escorting while it flies, so the separation really
does become due for *both* drones at once. -/
theorem atSeparation_at_separationTime {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (he : c.Escorting i h) :
    (c.advance (c.separationTime i)).AtSeparation i h := by
  refine ⟨⟨coLocated_advance_of_escorting he _, ?_⟩, ?_⟩
  · simpa using he.2
  · exact pos_eq_commonEnd_at_separationTime c i

/-- **Flying for `leftBorderTime` lands a leftward drone exactly on the border.** -/
theorem atLeftBorder_at_leftBorderTime {c : Config n} {i : Fin n}
    (hd : c.dir i = Dir.left) :
    (c.advance (c.leftBorderTime i)).AtLeftBorder i := by
  constructor
  · simp only [advance_pos, leftBorderTime, hd, Dir.sign_left]
    ring
  · simpa using hd

/-- **Flying for `rightBorderTime` lands a rightward drone exactly on the border.** -/
theorem atRightBorder_at_rightBorderTime {c : Config n} {i : Fin n}
    (hd : c.dir i = Dir.right) :
    (c.advance (c.rightBorderTime i)).AtRightBorder i := by
  constructor
  · simp only [advance_pos, rightBorderTime, hd, Dir.sign_right]
    ring
  · simpa using hd

/-- And the meet time really does produce a co-location. Restates
`gap_eq_zero_at_meetTime` in the event vocabulary. -/
theorem coLocated_at_meetTime {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (hA : c.Approaching i h) : (c.advance (c.meetTime i h)).CoLocated i h :=
  gap_eq_zero_at_meetTime hA

/-! ## The times are nonnegative when the event is genuinely ahead

Non-Zeno will need to know that steps do not run backwards. These are the
sign facts. -/

theorem leftBorderTime_nonneg {c : Config n} (hp : c.OnPerimeter) (i : Fin n) :
    0 ≤ c.leftBorderTime i := (hp i).1

theorem rightBorderTime_nonneg {c : Config n} (hp : c.OnPerimeter) (i : Fin n) :
    0 ≤ c.rightBorderTime i := by
  unfold rightBorderTime
  have := (hp i).2
  linarith

/-- A drone strictly inside the perimeter has strictly positive time to either
border. This is the shape of fact that rules out zero-length steps, and hence
the shape non-Zeno is built from. -/
theorem leftBorderTime_pos {c : Config n} {i : Fin n} (h : 0 < c.pos i) :
    0 < c.leftBorderTime i := h

theorem rightBorderTime_pos {c : Config n} {i : Fin n} (h : c.pos i < 1) :
    0 < c.rightBorderTime i := by
  unfold rightBorderTime; linarith

/-- Likewise a strictly separated approaching pair takes strictly positive time
to meet. -/
theorem meetTime_pos {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (hgap : 0 < c.gap i h) : 0 < c.meetTime i h := by
  unfold meetTime; linarith

/-! ### A meet points the pair the right way

This is the real content of `escortDir`, and the reason the schedule hangs
together: after a meet event, the separation that the meet creates is genuinely
*ahead* of the pair rather than behind it. Without this, `separationTime` could
come out negative after a meet and the schedule would be incoherent. -/

/-- **After a meet, the separation is never in the past.** -/
theorem separationTime_nonneg_doMeet (c : Config n) (i : Fin n)
    (h : i.val + 1 < n) : 0 ≤ (c.doMeet i h).separationTime i := by
  unfold separationTime
  rw [doMeet_dir_self, doMeet_pos, escortDir]
  split_ifs with hlt
  · rw [Dir.sign_right, mul_one]; linarith
  · rw [Dir.sign_left]
    rw [not_lt] at hlt
    have hr : (commonEnd i - c.pos i) * (-1) = c.pos i - commonEnd i := by ring
    rw [hr]; linarith

/-- **And strictly in the future, unless they met exactly on the boundary.**

That exceptional case is the paper's *bounce*: a meet and a separation
coinciding. Everywhere else a meet buys strictly positive time before the next
event involving this pair, which is precisely the kind of fact non-Zeno is
assembled from. -/
theorem separationTime_pos_doMeet (c : Config n) (i : Fin n)
    (h : i.val + 1 < n) (hne : c.pos i ≠ commonEnd i) :
    0 < (c.doMeet i h).separationTime i := by
  unfold separationTime
  rw [doMeet_dir_self, doMeet_pos, escortDir]
  split_ifs with hlt
  · rw [Dir.sign_right, mul_one]; linarith
  · rw [Dir.sign_left]
    rw [not_lt] at hlt
    have hlt' : commonEnd i < c.pos i := lt_of_le_of_ne hlt (Ne.symm hne)
    have hr : (commonEnd i - c.pos i) * (-1) = c.pos i - commonEnd i := by ring
    rw [hr]; linarith

end Config

end DPSS
