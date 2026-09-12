/-
# DPSS — the state between events

Everything so far reads the system at **event indices**: `run hn k` is the
configuration after `k` steps. That is the natural index for an event-driven
model, and for most purposes it is enough — between events nothing turns, so a
property checked at every event is checked everywhere.

**Lemma 3.7 is where that stops being true.** Its conclusion is a deadline:
*drone `j+1` is left synchronized by time `t + 1/n`*. Real time, not step
count. And its proof reads drone `j`'s heading and position at the real instant
`t`, which is in general **strictly inside a step** — the previous event is
before `t`, the next one after it.

The index-shaped reading of left synchronization is genuinely weaker than the
real-time one, and weaker in exactly the place the lemma needs strength: a
drone heading right can sit left of its endpoint mid-step and be back inside
its interval by the next event. So this file adds the real-time layer.

## What it costs, and what it does not

No new choice and no partial function. The position of drone `i` at real time
`s`, *read inside step `p`*, is

    posIn p i s = pos_p i + sign (dir_p i) * (s − time_p)

which is total, and `InStep p s` says `s` lies in that step. Non-Zeno supplies
a step containing any given instant (`exists_lastBefore`), so nothing is lost
by never naming "the" step of `s`.

The engine of the file is one three-line fact: **a linear function nonnegative
at both ends of an interval is nonnegative throughout it**
(`nonneg_of_endpoints`). Position, gap and balance are all linear in time
within a step, so every "it holds at the events, therefore it holds in
between" argument is that lemma with different names plugged in.

## The zero-time stretch

A second small tool that turns out to be used everywhere: **if the clock does
not move between two indices, no drone moves either.** Steps of zero length are
routine here (an event already due costs no time), and the consequence is that
index order and time order can be interchanged freely as long as one is
careful to carry positions rather than indices.
-/

import Dpss.Meeting

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## A linear function nonnegative at both ends

Within one step every quantity of interest — a position, a gap, a balance —
is affine in time. So "nonnegative at both events" gives "nonnegative
throughout", which is this lemma and nothing more. -/

/-- A linear function nonnegative at `0` and at `d` is nonnegative on `[0, d]`. -/
theorem nonneg_of_endpoints {a r u d : ℝ} (h0 : 0 ≤ a) (h1 : 0 ≤ a + r * d)
    (hu : 0 ≤ u) (hud : u ≤ d) : 0 ≤ a + r * u := by
  rcases le_or_gt 0 r with hr | hr
  · nlinarith
  · nlinarith

/-! ## Reading the system between events -/

/-- Where drone `i` is at real time `s`, read inside step `p`. Total: it is the
straight-line extrapolation of step `p`, meaningful when `s` really is in that
step. -/
noncomputable def posIn (c : Config n) (hn : 0 < n) (p : ℕ) (i : Fin n) (s : ℝ) : ℝ :=
  (c.run hn p).pos i + ((c.run hn p).dir i).sign * (s - (c.run hn p).time)

/-- Real time `s` falls inside step `p`: after its opening event and at or
before its closing one. -/
def InStep (c : Config n) (hn : 0 < n) (p : ℕ) (s : ℝ) : Prop :=
  (c.run hn p).time ≤ s ∧ s ≤ (c.run hn (p + 1)).time

theorem inStep_start (c : Config n) (hn : 0 < n) (hi : c.Invariant) (p : ℕ) :
    c.InStep hn p ((c.run hn p).time) :=
  ⟨le_rfl, time_mono_run' hn hi (Nat.le_succ p)⟩

theorem inStep_end (c : Config n) (hn : 0 < n) (hi : c.Invariant) (p : ℕ) :
    c.InStep hn p ((c.run hn (p + 1)).time) :=
  ⟨time_mono_run' hn hi (Nat.le_succ p), le_rfl⟩

/-- The step's length, named. -/
theorem time_succ_eq (c : Config n) (hn : 0 < n) (p : ℕ) :
    (c.run hn (p + 1)).time
      = (c.run hn p).time + (c.run hn p).timeToNextEvent hn := rfl

/-- And the distance each drone covers over it. -/
theorem pos_succ_eq (c : Config n) (hn : 0 < n) (p : ℕ) (i : Fin n) :
    (c.run hn (p + 1)).pos i
      = (c.run hn p).pos i
        + ((c.run hn p).dir i).sign * (c.run hn p).timeToNextEvent hn := rfl

/-- Read at its own opening event, `posIn` is the configuration's position. -/
@[simp] theorem posIn_start (c : Config n) (hn : 0 < n) (p : ℕ) (i : Fin n) :
    c.posIn hn p i ((c.run hn p).time) = (c.run hn p).pos i := by
  unfold posIn; ring

/-- And read at the closing event, it is the next configuration's position —
which is what makes the two readings of a shared instant agree. -/
@[simp] theorem posIn_end (c : Config n) (hn : 0 < n) (p : ℕ) (i : Fin n) :
    c.posIn hn p i ((c.run hn (p + 1)).time) = (c.run hn (p + 1)).pos i := by
  unfold posIn
  rw [time_succ_eq, pos_succ_eq]
  ring

/-- The step, written as a displacement from its own start. -/
theorem pos_succ_eq' (c : Config n) (hn : 0 < n) (p : ℕ) (i : Fin n) :
    (c.run hn (p + 1)).pos i
      = (c.run hn p).pos i
        + ((c.run hn p).dir i).sign
          * ((c.run hn (p + 1)).time - (c.run hn p).time) := by
  rw [time_succ_eq, pos_succ_eq]; ring

/-! ## Bounds inside a step

A drone's position over a step is monotone, so a bound holding at both events
holds throughout. -/

/-- **A lower bound at both ends of a step holds inside it.** -/
theorem le_posIn {c : Config n} (hn : 0 < n) {p : ℕ} {i : Fin n} {s a : ℝ}
    (hs : c.InStep hn p s) (h0 : a ≤ (c.run hn p).pos i)
    (h1 : a ≤ (c.run hn (p + 1)).pos i) : a ≤ c.posIn hn p i s := by
  have hd := pos_succ_eq' c hn p i
  have hkey := nonneg_of_endpoints (a := (c.run hn p).pos i - a)
    (r := ((c.run hn p).dir i).sign)
    (u := s - (c.run hn p).time)
    (d := (c.run hn (p + 1)).time - (c.run hn p).time)
    (by linarith) (by rw [hd] at h1; linarith) (by linarith [hs.1]) (by linarith [hs.2])
  unfold posIn
  linarith

/-- **And an upper bound at both ends holds inside it.** The right-hand mirror
of the previous lemma. -/
theorem posIn_le {c : Config n} (hn : 0 < n) {p : ℕ} {i : Fin n} {s a : ℝ}
    (hs : c.InStep hn p s) (h0 : (c.run hn p).pos i ≤ a)
    (h1 : (c.run hn (p + 1)).pos i ≤ a) : c.posIn hn p i s ≤ a := by
  have hd := pos_succ_eq' c hn p i
  have hkey := nonneg_of_endpoints (a := a - (c.run hn p).pos i)
    (r := -((c.run hn p).dir i).sign)
    (u := s - (c.run hn p).time)
    (d := (c.run hn (p + 1)).time - (c.run hn p).time)
    (by linarith) (by rw [hd] at h1; linarith) (by linarith [hs.1]) (by linarith [hs.2])
  unfold posIn
  linarith

/-- **Drones do not overtake between events either.** The gap is affine in time
within a step and nonnegative at both ends, so it is nonnegative throughout. -/
theorem posIn_le_posIn_next {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {p : ℕ} {i : Fin n} {h : i.val + 1 < n} {s : ℝ} (hs : c.InStep hn p s) :
    c.posIn hn p i s ≤ c.posIn hn p (nextIdx i h) s := by
  have hg0 : 0 ≤ (c.run hn p).gap i h := (invariant_run hn hi p).adjOrdered i h
  have hg1 : 0 ≤ (c.run hn (p + 1)).gap i h :=
    (invariant_run hn hi (p + 1)).adjOrdered i h
  have hdi := pos_succ_eq' c hn p i
  have hdj := pos_succ_eq' c hn p (nextIdx i h)
  have hgapdef : ∀ q : ℕ, (c.run hn q).gap i h
      = (c.run hn q).pos (nextIdx i h) - (c.run hn q).pos i := fun _ => rfl
  rw [hgapdef] at hg0 hg1
  have hkey := nonneg_of_endpoints (a := (c.run hn p).gap i h)
    (r := ((c.run hn p).dir (nextIdx i h)).sign - ((c.run hn p).dir i).sign)
    (u := s - (c.run hn p).time)
    (d := (c.run hn (p + 1)).time - (c.run hn p).time)
    (by rw [hgapdef]; linarith) (by rw [hgapdef]; rw [hdi, hdj] at hg1; linarith)
    (by linarith [hs.1]) (by linarith [hs.2])
  rw [hgapdef] at hkey
  unfold posIn
  linarith

/-! ## Every instant is inside a step

Non-Zeno is what makes this true: the times along a run are unbounded, so no
instant escapes off the end. -/

/-- **Every instant at or after the start lies in some step.** -/
theorem exists_lastBefore {c : Config n} (hn : 0 < n) (hi : c.Invariant) {T : ℝ}
    (hT : c.time ≤ T) :
    ∃ p : ℕ, (c.run hn p).time ≤ T ∧ T < (c.run hn (p + 1)).time := by
  classical
  have hex : ∃ q : ℕ, T < (c.run hn q).time := nonZeno hn hi T
  have hspec : T < (c.run hn (Nat.find hex)).time := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, run_zero] at hspec
    linarith
  obtain ⟨p, hp⟩ : ∃ p, Nat.find hex = p + 1 := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨p, ?_, by rw [← hp]; exact hspec⟩
  have hlt : p < Nat.find hex := by omega
  have := Nat.find_min hex hlt
  linarith [not_lt.mp this]

/-! ## The clock can stall, and then nothing moves

A step takes zero time when an event is already due, and several steps in a row
can. Over such a stretch positions are frozen — which is what lets index order
and time order be traded against each other without losing information. -/

/-- **No time, no motion.** -/
theorem pos_eq_of_time_le {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {a b : ℕ} (hab : a ≤ b) (ht : (c.run hn b).time ≤ (c.run hn a).time)
    (i : Fin n) : (c.run hn b).pos i = (c.run hn a).pos i := by
  obtain ⟨m, rfl⟩ : ∃ m, b = a + m := ⟨b - a, by omega⟩
  clear hab
  induction m with
  | zero => rfl
  | succ m ih =>
    have hmono : (c.run hn (a + m)).time ≤ (c.run hn (a + (m + 1))).time :=
      time_mono_run' hn hi (by omega)
    have hprev : (c.run hn (a + m)).pos i = (c.run hn a).pos i :=
      ih (le_trans hmono ht)
    have hlow : (c.run hn a).time ≤ (c.run hn (a + m)).time :=
      time_mono_run' hn hi (by omega)
    have hz : (c.run hn (a + m)).timeToNextEvent hn = 0 := by
      have he : (c.run hn (a + (m + 1))).time
          = (c.run hn (a + m)).time + (c.run hn (a + m)).timeToNextEvent hn := by
        rw [show a + (m + 1) = (a + m) + 1 from rfl, time_succ_eq]
      linarith
    have hstep : (c.run hn (a + (m + 1))).pos i
        = (c.run hn (a + m)).pos i
          + ((c.run hn (a + m)).dir i).sign
            * (c.run hn (a + m)).timeToNextEvent hn := by
      rw [show a + (m + 1) = (a + m) + 1 from rfl, pos_succ_eq]
    rw [hstep, hz, hprev]
    ring

/-- The gap is frozen too. -/
theorem gap_eq_of_time_le {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {a b : ℕ} (hab : a ≤ b) (ht : (c.run hn b).time ≤ (c.run hn a).time)
    {i : Fin n} (h : i.val + 1 < n) :
    (c.run hn b).gap i h = (c.run hn a).gap i h := by
  unfold gap
  rw [pos_eq_of_time_le hn hi hab ht, pos_eq_of_time_le hn hi hab ht]

/-- **A meeting recorded at one instant is a meeting at every index sharing
it.** This is what lets a time-shaped `HaveMetBy` be converted into an
index-shaped one. -/
theorem coLocated_of_time_le {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {a b : ℕ} (hab : a ≤ b) (ht : (c.run hn b).time ≤ (c.run hn a).time)
    {i : Fin n} {h : i.val + 1 < n} (hco : (c.run hn b).CoLocated i h) :
    (c.run hn a).CoLocated i h := by
  unfold CoLocated at hco ⊢
  rwa [gap_eq_of_time_le hn hi hab ht] at hco

/-! ## Synchronization in real time

The definitions `LeftSync` and `RightSync` quantify over step indices. These
quantify over instants, and they are what Lemma 3.7 both consumes and
produces. -/

/-- Drone `i` never goes left of its left endpoint at any instant from `T` on.
Unlike `LeftSync`, this constrains the drone **between** events as well as at
them. -/
def LeftSyncAt (c : Config n) (hn : 0 < n) (i : Fin n) (T : ℝ) : Prop :=
  ∀ (p : ℕ) (s : ℝ), T ≤ s → c.InStep hn p s → leftEnd i ≤ c.posIn hn p i s

/-- And the right-hand mirror. -/
def RightSyncAt (c : Config n) (hn : 0 < n) (i : Fin n) (T : ℝ) : Prop :=
  ∀ (p : ℕ) (s : ℝ), T ≤ s → c.InStep hn p s → c.posIn hn p i s ≤ rightEnd i

theorem leftSyncAt_mono {c : Config n} {hn : 0 < n} {i : Fin n} {T T' : ℝ}
    (hTT : T ≤ T') (hs : LeftSyncAt c hn i T) : LeftSyncAt c hn i T' :=
  fun p s hsT hin => hs p s (le_trans hTT hsT) hin

theorem rightSyncAt_mono {c : Config n} {hn : 0 < n} {i : Fin n} {T T' : ℝ}
    (hTT : T ≤ T') (hs : RightSyncAt c hn i T) : RightSyncAt c hn i T' :=
  fun p s hsT hin => hs p s (le_trans hTT hsT) hin

/-- The real-time notion implies the index-shaped one, read at any event at or
after the deadline. -/
theorem leftSync_of_leftSyncAt {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {T : ℝ} {k : ℕ} (hs : LeftSyncAt c hn i T)
    (hk : T ≤ (c.run hn k).time) : LeftSync c hn i k := by
  intro j hj
  have hTj : T ≤ (c.run hn j).time := le_trans hk (time_mono_run' hn hi hj)
  have := hs j ((c.run hn j).time) hTj (inStep_start c hn hi j)
  rwa [posIn_start] at this

theorem rightSync_of_rightSyncAt {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {T : ℝ} {k : ℕ} (hs : RightSyncAt c hn i T)
    (hk : T ≤ (c.run hn k).time) : RightSync c hn i k := by
  intro j hj
  have hTj : T ≤ (c.run hn j).time := le_trans hk (time_mono_run' hn hi hj)
  have := hs j ((c.run hn j).time) hTj (inStep_start c hn hi j)
  rwa [posIn_start] at this

/-- **And conversely**, index-shaped synchronization from step `k` gives
real-time synchronization from the instant of step `k`. The only work is the
degenerate case where an earlier index shares that instant — and then nothing
has moved, so it does not matter. -/
theorem leftSyncAt_of_leftSync {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {k : ℕ} (hs : LeftSync c hn i k) :
    LeftSyncAt c hn i ((c.run hn k).time) := by
  intro p s hsT hin
  rcases le_or_gt k p with hkp | hpk
  · exact le_posIn hn hin (hs p hkp) (hs (p + 1) (by omega))
  · -- `p` is before `k`, so the instant `s` is the shared closing event
    have h1 : (c.run hn (p + 1)).time ≤ (c.run hn k).time :=
      time_mono_run' hn hi (by omega)
    have hseq : s = (c.run hn (p + 1)).time := le_antisymm hin.2 (by linarith)
    have hfreeze : (c.run hn k).pos i = (c.run hn (p + 1)).pos i :=
      pos_eq_of_time_le hn hi (by omega) (by linarith [hin.2]) i
    rw [hseq, posIn_end, ← hfreeze]
    exact hs k le_rfl

theorem rightSyncAt_of_rightSync {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {k : ℕ} (hs : RightSync c hn i k) :
    RightSyncAt c hn i ((c.run hn k).time) := by
  intro p s hsT hin
  rcases le_or_gt k p with hkp | hpk
  · exact posIn_le hn hin (hs p hkp) (hs (p + 1) (by omega))
  · have h1 : (c.run hn (p + 1)).time ≤ (c.run hn k).time :=
      time_mono_run' hn hi (by omega)
    have hseq : s = (c.run hn (p + 1)).time := le_antisymm hin.2 (by linarith)
    have hfreeze : (c.run hn k).pos i = (c.run hn (p + 1)).pos i :=
      pos_eq_of_time_le hn hi (by omega) (by linarith [hin.2]) i
    rw [hseq, posIn_end, ← hfreeze]
    exact hs k le_rfl

/-! ## The leftmost drone is synchronized from the start

The base case of the induction that proves Theorem 2.1: drone `0`'s left
endpoint is the left border of the perimeter, which no drone ever crosses. -/

/-- **Drone `0` is left synchronized at every instant.** -/
theorem leftSyncAt_zero {c : Config n} (hn : 0 < n) (hi : c.Invariant) (T : ℝ) :
    LeftSyncAt c hn (⟨0, hn⟩ : Fin n) T := by
  intro p s _ hin
  rw [leftEnd_zero hn]
  exact le_posIn hn hin (onPerimeter_run hn hi p _).1
    (onPerimeter_run hn hi (p + 1) _).1

end Config

end DPSS
