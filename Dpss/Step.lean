/-
# DPSS — one step of the system

Everything so far has described pieces in isolation. This file joins them:
fly to the next event, then let every event that is now due fire.

## Events fire simultaneously

Several events can come due at the same instant — that is ordinary, not
exceptional. So rather than composing individual updates (whose order would
then matter), each drone's post-event direction is defined **as a function of
the whole configuration**, `newDir`. Simultaneity is then automatic.

## The priority order, and the paper's nondeterminism

`newDir` resolves competing events in the order

    border  >  separation  >  meet  >  unchanged

Most of these can never actually compete, and it is worth knowing which:

* A drone cannot meet both neighbours at once. Meeting the right neighbour
  requires heading right; meeting the left neighbour requires heading left.
* A drone cannot separate from both neighbours at once. The two separations
  would have to happen at `commonEnd (i-1)` and `commonEnd i`, which are
  different points.
* A separation and a meet **can** coincide. This looked like the genuine
  ambiguity Avigad–van Doorn flag (§2) — when three or more drones come
  together, the middle one may escort either neighbour, and they deliberately
  leave it unspecified — so giving separation priority was recorded for a long
  time as *one* resolution among several.

  **It is not.** `Priority.lean` computes both answers for every pair of events
  that can be due at one drone at one instant: two combinations are impossible,
  five agree, and the one that differs is the paper's *bounce*, where taking
  the meet instead provably walks a drone out of its own interval. And
  `Nondeterminism.lean` models the paper's actual open case as a **relation**,
  then proves it collapses: on any configuration satisfying the standing
  conditions there is exactly one legitimate successor, so every trajectory of
  the relation is this function's run. Which is what the paper itself asserts —
  *"our upper bound only concerns phase 2, where these issues do not arise"*.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §2.
-/

import Dpss.NextEvent

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## The left-hand neighbour

`nextIdx` gave us the drone to the right. Several events are most naturally
described from the point of view of the *right* member of a pair, so we need
the other direction too. -/

/-- The drone immediately to the left of `i`. -/
def prevIdx (i : Fin n) (h : 0 < i.val) : Fin n :=
  ⟨i.val - 1, by have := i.isLt; omega⟩

@[simp] theorem prevIdx_val (i : Fin n) (h : 0 < i.val) :
    (prevIdx i h).val = i.val - 1 := rfl

/-- The left neighbour has room to its right — namely `i` itself. -/
theorem prevIdx_lt (i : Fin n) (h : 0 < i.val) : (prevIdx i h).val + 1 < n := by
  have := i.isLt; simp only [prevIdx_val]; omega

/-- Stepping left then right returns you to where you started. -/
@[simp] theorem nextIdx_prevIdx (i : Fin n) (h : 0 < i.val) :
    nextIdx (prevIdx i h) (prevIdx_lt i h) = i := by
  apply Fin.ext
  simp only [nextIdx_val, prevIdx_val]
  omega

/-! ## Which events are due for a given drone -/

/-- A separation with the right-hand neighbour: `i` is the left member, so it
turns back to the left, into its own interval. -/
def SepRight (c : Config n) (i : Fin n) : Prop :=
  ∃ h : i.val + 1 < n, c.AtSeparation i h

/-- A separation with the left-hand neighbour: `i` is the right member, so it
turns back to the right. -/
def SepLeft (c : Config n) (i : Fin n) : Prop :=
  ∃ h : 0 < i.val, c.AtSeparation (prevIdx i h) (prevIdx_lt i h)

/-- A meet with the right-hand neighbour. -/
def MeetRight (c : Config n) (i : Fin n) : Prop :=
  ∃ h : i.val + 1 < n, c.CoLocated i h ∧ c.Approaching i h

/-- A meet with the left-hand neighbour. -/
def MeetLeft (c : Config n) (i : Fin n) : Prop :=
  ∃ h : 0 < i.val,
    c.CoLocated (prevIdx i h) (prevIdx_lt i h) ∧
    c.Approaching (prevIdx i h) (prevIdx_lt i h)

/-- The heading a drone adopts on meeting its **left** neighbour: towards the
boundary they share, which is this drone's own left endpoint. -/
noncomputable def escortDirLeft (c : Config n) (i : Fin n) : Dir :=
  if c.pos i < leftEnd i then Dir.right else Dir.left

/-! ## The post-event direction -/

open Classical in
/-- Every drone's direction after all due events have fired. Drones with no
event due keep the heading they had. -/
noncomputable def newDir (c : Config n) (i : Fin n) : Dir :=
  if c.AtLeftBorder i then Dir.right
  else if c.AtRightBorder i then Dir.left
  else if c.SepRight i then Dir.left
  else if c.SepLeft i then Dir.right
  else if c.MeetRight i then c.escortDir i
  else if c.MeetLeft i then c.escortDirLeft i
  else c.dir i

/-- A drone with nothing due carries on. -/
theorem newDir_of_noEvent {c : Config n} {i : Fin n}
    (h1 : ¬ c.AtLeftBorder i) (h2 : ¬ c.AtRightBorder i)
    (h3 : ¬ c.SepRight i) (h4 : ¬ c.SepLeft i)
    (h5 : ¬ c.MeetRight i) (h6 : ¬ c.MeetLeft i) :
    c.newDir i = c.dir i := by
  unfold newDir
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]

/-- A drone on the left border turns round, whatever else is going on. Border
events take priority precisely so that this is unconditional. -/
@[simp] theorem newDir_atLeftBorder {c : Config n} {i : Fin n}
    (h : c.AtLeftBorder i) : c.newDir i = Dir.right := by
  unfold newDir; rw [if_pos h]

@[simp] theorem newDir_atRightBorder {c : Config n} {i : Fin n}
    (h1 : ¬ c.AtLeftBorder i) (h2 : c.AtRightBorder i) :
    c.newDir i = Dir.left := by
  unfold newDir; rw [if_neg h1, if_pos h2]

/-- `newDir` never consults the clock, so configurations agreeing on positions
and headings turn identically. Needed to recognise that a configuration reached
mid-trace is the same one analysed earlier. -/
theorem newDir_congr {c c' : Config n} (hp : c.pos = c'.pos)
    (hd : c.dir = c'.dir) (i : Fin n) : c.newDir i = c'.newDir i := by
  obtain ⟨ta, pa, da⟩ := c
  obtain ⟨tb, pb, db⟩ := c'
  simp only at hp hd
  subst hp
  subst hd
  rfl

/-! ## The step

Fly to the next event, then fire everything due. -/

/-- One step of the system. -/
noncomputable def step (c : Config n) (hn : 0 < n) : Config n :=
  let c' := c.advance (c.timeToNextEvent hn)
  { time := c'.time, pos := c'.pos, dir := fun i => c'.newDir i }

@[simp] theorem step_time (c : Config n) (hn : 0 < n) :
    (c.step hn).time = c.time + c.timeToNextEvent hn := rfl

@[simp] theorem step_pos (c : Config n) (hn : 0 < n) (i : Fin n) :
    (c.step hn).pos i = c.pos i + (c.dir i).sign * c.timeToNextEvent hn := rfl

/-- Stepping moves the drones exactly as flying to the next event does; the
events themselves only change headings. -/
@[simp] theorem step_gap (c : Config n) (hn : 0 < n) (i : Fin n)
    (h : i.val + 1 < n) :
    (c.step hn).gap i h = (c.advance (c.timeToNextEvent hn)).gap i h := rfl

/-! ## The step is well behaved -/

/-- The step never overshoots a collision: the global deadline is at most any
approaching pair's meeting time. -/
theorem timeToNextEvent_le_meetTime {c : Config n} (hn : 0 < n) {i : Fin n}
    {h : i.val + 1 < n} (hA : c.Approaching i h) :
    c.timeToNextEvent hn ≤ c.meetTime i h :=
  le_trans (timeToNextEvent_le hn i) (droneNextTime_le_meetTime hA)

/-- **A step preserves the ordering of the drones.**

This is the payoff of `ordered_advance`: because the step flies for no longer
than the time to the next collision, nobody passes anybody. The event part of
the step cannot disturb it, since events do not move drones. -/
theorem adjOrdered_step {c : Config n} (hn : 0 < n) (hp : c.OnPerimeter)
    (ha : c.AdjOrdered) (hec : c.EscortsCoherent) :
    (c.step hn).AdjOrdered := by
  intro i h
  rw [step_gap]
  exact gap_nonneg_advance (ha i h)
    (timeToNextEvent_nonneg hn hp ha hec)
    (fun hA => timeToNextEvent_le_meetTime hn hA)

/-- And therefore the full order relation too. -/
theorem ordered_step {c : Config n} (hn : 0 < n) (hp : c.OnPerimeter)
    (ha : c.AdjOrdered) (hec : c.EscortsCoherent) : (c.step hn).Ordered :=
  ordered_of_adjOrdered (adjOrdered_step hn hp ha hec)

/-- **Time strictly advances**, provided no event was already due. Together
with `timeToNextEvent_pos` this is what makes a run make progress. -/
theorem step_time_lt {c : Config n} (hn : 0 < n) (hp : c.OnPerimeter)
    (ha : c.AdjOrdered) (hec : c.EscortsCoherent) (hnd : c.NoEventDue) :
    c.time < (c.step hn).time := by
  rw [step_time]
  have := timeToNextEvent_pos hn hp ha hec hnd
  linarith

/-- Time never runs backwards, even when an event was already due. -/
theorem step_time_le {c : Config n} (hn : 0 < n) (hp : c.OnPerimeter)
    (ha : c.AdjOrdered) (hec : c.EscortsCoherent) :
    c.time ≤ (c.step hn).time := by
  rw [step_time]
  have := timeToNextEvent_nonneg hn hp ha hec
  linarith

/-! ## Runs

A run is the orbit of `step` from a starting configuration. Non-Zeno will be
the statement that the times along a run are **unbounded** — that the system
cannot pack infinitely many events into a finite stretch. -/

/-- The configuration after `k` steps. -/
noncomputable def run (c : Config n) (hn : 0 < n) : ℕ → Config n
  | 0 => c
  | k + 1 => (c.run hn k).step hn

@[simp] theorem run_zero (c : Config n) (hn : 0 < n) : c.run hn 0 = c := rfl

@[simp] theorem run_succ (c : Config n) (hn : 0 < n) (k : ℕ) :
    c.run hn (k + 1) = (c.run hn k).step hn := rfl

/-- What it means for the system to be free of Zeno behaviour: the times along
the run grow without bound, so every instant is eventually passed.

Stated here and proved in `NonZenoProof.lean`. `timeToNextEvent_pos` gives
strictly positive steps, which is necessary but nowhere near sufficient: a
sequence of strictly positive steps can still sum to something finite. The
proof instead counts turns — see `TurnSpacing.lean`. -/
def NonZeno (c : Config n) (hn : 0 < n) : Prop :=
  ∀ T : ℝ, ∃ k : ℕ, T < (c.run hn k).time

end Config

end DPSS
