/-
# DPSS — the perimeter reflected

**B7.** Every convergence result here concerns *left* synchronization.
Avigad–van Doorn get the other half in four words — *"by symmetry"* — which on
paper is honest and in Lean is not.

The way to make it honest here is a **reflection**: flip the perimeter
end-for-end, reverse every heading, and renumber the drones backwards. The
algorithm is invariant under that, so right synchronization of a run *is* left
synchronization of the mirrored run, and every result proved on the left
transfers for free.

    position   x  ↦  1 − x
    heading    →  ↦  ←
    index      i  ↦  n−1−i

This file builds the reflection and its geometry. The step-commutation proof —
that mirroring and running commute — comes next, and is the substantial part.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §3 ("By symmetry, it suffices to show that
all the drones are left synchronized by time 2 − 1/n").
-/

import Dpss.EventuallyTurns

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

/-! ## Reflecting an index -/

/-- Drone `i` counted from the other end. -/
def mirrorIdx (i : Fin n) : Fin n :=
  ⟨n - 1 - i.val, by have := i.isLt; omega⟩

@[simp] theorem mirrorIdx_val (i : Fin n) :
    (mirrorIdx i).val = n - 1 - i.val := rfl

/-- Reflecting twice is doing nothing. -/
@[simp] theorem mirrorIdx_mirrorIdx (i : Fin n) : mirrorIdx (mirrorIdx i) = i := by
  apply Fin.ext
  have := i.isLt
  simp only [mirrorIdx_val]
  omega

/-- Reflection reverses the ordering of drones. -/
theorem mirrorIdx_le_mirrorIdx {i j : Fin n} (hij : i ≤ j) :
    mirrorIdx j ≤ mirrorIdx i := by
  have hi := i.isLt
  have hj := j.isLt
  have h : i.val ≤ j.val := Fin.le_def.mp hij
  rw [Fin.le_def]
  simp only [mirrorIdx_val]
  omega

/-! ## Reflecting the geometry

The interval assigned to the reflected drone is the reflection of the interval
assigned to the original: left and right endpoints swap. -/

theorem cast_mirror (i : Fin n) : ((n - 1 - i.val : ℕ) : ℝ) = (n : ℝ) - 1 - (i.val : ℝ) := by
  have hi := i.isLt
  have h1 : (1 : ℕ) ≤ n := by omega
  have h2 : i.val ≤ n - 1 := by omega
  rw [Nat.cast_sub h2, Nat.cast_sub h1, Nat.cast_one]

theorem leftEnd_mirrorIdx (i : Fin n) : leftEnd (mirrorIdx i) = 1 - rightEnd i := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold leftEnd rightEnd
  rw [mirrorIdx_val, cast_mirror i]
  field_simp
  ring

theorem rightEnd_mirrorIdx (i : Fin n) : rightEnd (mirrorIdx i) = 1 - leftEnd i := by
  have h1 := rightEnd_sub_leftEnd (mirrorIdx i)
  have h2 := rightEnd_sub_leftEnd i
  have h3 := leftEnd_mirrorIdx i
  linarith

/-! ## Reflecting a configuration -/

namespace Config

/-- The configuration seen from the other end of the perimeter: positions
reflected, headings reversed, drones renumbered backwards. -/
noncomputable def mirror (c : Config n) : Config n where
  time := c.time
  pos := fun i => 1 - c.pos (mirrorIdx i)
  dir := fun i => (c.dir (mirrorIdx i)).flip

@[simp] theorem mirror_time (c : Config n) : c.mirror.time = c.time := rfl

@[simp] theorem mirror_pos (c : Config n) (i : Fin n) :
    c.mirror.pos i = 1 - c.pos (mirrorIdx i) := rfl

@[simp] theorem mirror_dir (c : Config n) (i : Fin n) :
    c.mirror.dir i = (c.dir (mirrorIdx i)).flip := rfl

/-- Reflecting twice is doing nothing. -/
theorem mirror_mirror (c : Config n) : c.mirror.mirror = c := by
  refine Config.ext rfl (funext fun i => ?_) (funext fun i => ?_)
  · simp only [mirror_pos, mirrorIdx_mirrorIdx]; ring
  · simp only [mirror_dir, mirrorIdx_mirrorIdx, Dir.flip_flip]

/-! ## The reflection respects the standing invariant -/

theorem onPerimeter_mirror {c : Config n} (hp : c.OnPerimeter) :
    c.mirror.OnPerimeter := by
  intro i
  obtain ⟨h0, h1⟩ := hp (mirrorIdx i)
  exact ⟨by simp only [mirror_pos]; linarith, by simp only [mirror_pos]; linarith⟩

theorem ordered_mirror {c : Config n} (ho : c.Ordered) : c.mirror.Ordered := by
  intro i j hij
  simp only [mirror_pos]
  have := ho (mirrorIdx j) (mirrorIdx i) (mirrorIdx_le_mirrorIdx hij)
  linarith

/-! ## What the reflection does to synchronization

The point of the whole exercise: staying at or beyond your *left* endpoint in
the mirrored world is staying at or before your *right* endpoint in this
one. -/

theorem leftEnd_le_mirror_pos_iff {c : Config n} (i : Fin n) :
    leftEnd i ≤ c.mirror.pos i ↔ c.pos (mirrorIdx i) ≤ rightEnd (mirrorIdx i) := by
  simp only [mirror_pos]
  rw [rightEnd_mirrorIdx i]
  constructor <;> intro hx <;> linarith

theorem mirror_pos_le_rightEnd_iff {c : Config n} (i : Fin n) :
    c.mirror.pos i ≤ rightEnd i ↔ leftEnd (mirrorIdx i) ≤ c.pos (mirrorIdx i) := by
  simp only [mirror_pos]
  rw [leftEnd_mirrorIdx i]
  constructor <;> intro hx <;> linarith

/-! ## Reflected indices

Reflection turns "the drone to my right" into "the drone to my left". These
identities carry that, and they are the fiddly part of the whole construction.
-/

theorem mirrorIdx_pos {i : Fin n} (h : i.val + 1 < n) : 0 < (mirrorIdx i).val := by
  simp only [mirrorIdx_val]; omega

theorem mirrorIdx_lt {i : Fin n} (h : 0 < i.val) : (mirrorIdx i).val + 1 < n := by
  have := i.isLt; simp only [mirrorIdx_val]; omega

/-- The reflection of a pair, indexed from its other end. -/
theorem mirror_next_lt (i : Fin n) (h : i.val + 1 < n) :
    (mirrorIdx (nextIdx i h)).val + 1 < n := by
  have := i.isLt
  simp only [mirrorIdx_val, nextIdx_val]
  omega

/-- **The identity everything else rests on.** Reflecting a pair and then
taking its right-hand member gives the reflection of its left-hand member. -/
theorem nextIdx_mirrorIdx_next (i : Fin n) (h : i.val + 1 < n) :
    nextIdx (mirrorIdx (nextIdx i h)) (mirror_next_lt i h) = mirrorIdx i := by
  apply Fin.ext
  have := i.isLt
  simp only [nextIdx_val, mirrorIdx_val]
  omega

/-! ## Reflected local quantities -/

/-- A gap in the mirrored world is the corresponding gap here. -/
theorem gap_mirror (c : Config n) (i : Fin n) (h : i.val + 1 < n) :
    c.mirror.gap i h = c.gap (mirrorIdx (nextIdx i h)) (mirror_next_lt i h) := by
  unfold gap
  simp only [mirror_pos]
  rw [nextIdx_mirrorIdx_next i h]
  ring

/-- A separation rate in the mirrored world is the corresponding one here.
Both headings flip and the pair order reverses; the two effects cancel. -/
theorem sepRate_mirror (c : Config n) (i : Fin n) (h : i.val + 1 < n) :
    c.mirror.sepRate i h
      = c.sepRate (mirrorIdx (nextIdx i h)) (mirror_next_lt i h) := by
  unfold sepRate
  simp only [mirror_dir, Dir.sign_flip]
  rw [nextIdx_mirrorIdx_next i h]
  ring

/-- Co-location is preserved. -/
theorem coLocated_mirror (c : Config n) (i : Fin n) (h : i.val + 1 < n) :
    c.mirror.CoLocated i h
      ↔ c.CoLocated (mirrorIdx (nextIdx i h)) (mirror_next_lt i h) := by
  unfold CoLocated
  rw [gap_mirror]

/-- Approaching is preserved: both drones reverse, and so does their order. -/
theorem approaching_mirror (c : Config n) (i : Fin n) (h : i.val + 1 < n) :
    c.mirror.Approaching i h
      ↔ c.Approaching (mirrorIdx (nextIdx i h)) (mirror_next_lt i h) := by
  unfold Approaching
  simp only [mirror_dir]
  rw [nextIdx_mirrorIdx_next i h]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases Dir.eq_left_or_right (c.dir (mirrorIdx (nextIdx i h))) with hx | hx
      · rw [hx] at h2; exact absurd h2 (fun hc => Dir.noConfusion hc)
      · exact hx
    · rcases Dir.eq_left_or_right (c.dir (mirrorIdx i)) with hx | hx
      · exact hx
      · rw [hx] at h1; exact absurd h1 (fun hc => Dir.noConfusion hc)
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    exact ⟨rfl, rfl⟩

/-- Escorting is preserved. -/
theorem escorting_mirror (c : Config n) (i : Fin n) (h : i.val + 1 < n) :
    c.mirror.Escorting i h
      ↔ c.Escorting (mirrorIdx (nextIdx i h)) (mirror_next_lt i h) := by
  unfold Escorting
  rw [coLocated_mirror]
  simp only [mirror_dir]
  rw [nextIdx_mirrorIdx_next i h]
  constructor
  · rintro ⟨hc, hd⟩
    refine ⟨hc, ?_⟩
    have := congrArg Dir.flip hd
    simpa using this.symm
  · rintro ⟨hc, hd⟩
    refine ⟨hc, ?_⟩
    rw [hd]

/-! ## Reflected borders and deadlines

The two perimeter ends swap, and so do the two border events. -/

theorem flip_eq_left_iff (d : Dir) : d.flip = Dir.left ↔ d = Dir.right := by
  cases d <;> simp [Dir.flip]

theorem flip_eq_right_iff (d : Dir) : d.flip = Dir.right ↔ d = Dir.left := by
  cases d <;> simp [Dir.flip]

/-- Reaching the left border in the mirrored world is reaching the right
border here. -/
theorem atLeftBorder_mirror (c : Config n) (i : Fin n) :
    c.mirror.AtLeftBorder i ↔ c.AtRightBorder (mirrorIdx i) := by
  unfold AtLeftBorder AtRightBorder
  simp only [mirror_pos, mirror_dir, flip_eq_left_iff]
  constructor
  · rintro ⟨hp, hd⟩; exact ⟨by linarith, hd⟩
  · rintro ⟨hp, hd⟩; exact ⟨by rw [hp]; ring, hd⟩

theorem atRightBorder_mirror (c : Config n) (i : Fin n) :
    c.mirror.AtRightBorder i ↔ c.AtLeftBorder (mirrorIdx i) := by
  unfold AtLeftBorder AtRightBorder
  simp only [mirror_pos, mirror_dir, flip_eq_right_iff]
  constructor
  · rintro ⟨hp, hd⟩; exact ⟨by linarith, hd⟩
  · rintro ⟨hp, hd⟩; exact ⟨by rw [hp]; ring, hd⟩

/-- **A drone's time to its border is unchanged by reflection.** Which border
it is heading for swaps, and so does its distance to it — the two cancel. -/
theorem borderTime_mirror (c : Config n) (i : Fin n) :
    c.mirror.borderTime i = c.borderTime (mirrorIdx i) := by
  unfold borderTime
  rcases Dir.eq_left_or_right (c.dir (mirrorIdx i)) with hx | hx
  · have h1 : c.mirror.dir i = Dir.right := by simp only [mirror_dir, hx]; rfl
    rw [if_neg (by rw [h1]; exact fun hc => Dir.noConfusion hc), if_pos hx]
    simp only [mirror_pos]; ring
  · have h1 : c.mirror.dir i = Dir.left := by simp only [mirror_dir, hx]; rfl
    rw [if_pos h1, if_neg (by rw [hx]; exact fun hc => Dir.noConfusion hc)]
    simp only [mirror_pos]

/-- Meeting times correspond. -/
theorem meetTime_mirror (c : Config n) (i : Fin n) (h : i.val + 1 < n) :
    c.mirror.meetTime i h
      = c.meetTime (mirrorIdx (nextIdx i h)) (mirror_next_lt i h) := by
  unfold meetTime
  rw [gap_mirror]

/-- **Separation deadlines correspond**, for an escorting pair — which is the
only case the scheduler consults them in. The reflected pair escorts to the
reflection of the boundary the original escorts to. -/
theorem separationTime_mirror (c : Config n) (i : Fin n) (h : i.val + 1 < n)
    (he : c.mirror.Escorting i h) :
    c.mirror.separationTime i
      = c.separationTime (mirrorIdx (nextIdx i h)) := by
  have hco : c.CoLocated (mirrorIdx (nextIdx i h)) (mirror_next_lt i h) :=
    (coLocated_mirror c i h).mp he.1
  have hsame : c.pos (mirrorIdx i) = c.pos (mirrorIdx (nextIdx i h)) := by
    unfold CoLocated gap at hco
    rw [nextIdx_mirrorIdx_next i h] at hco
    linarith
  have hdir : c.mirror.dir i = c.mirror.dir (nextIdx i h) := he.2
  have hd : c.dir (mirrorIdx (nextIdx i h)) = c.dir (mirrorIdx i) := by
    simp only [mirror_dir] at hdir
    have hf := congrArg Dir.flip hdir
    have h2 : c.dir (mirrorIdx i) = c.dir (mirrorIdx (nextIdx i h)) := by simpa using hf
    exact h2.symm
  unfold separationTime
  simp only [mirror_pos, mirror_dir, Dir.sign_flip]
  rw [show commonEnd i = rightEnd i from rfl,
    show commonEnd (mirrorIdx (nextIdx i h)) = rightEnd (mirrorIdx (nextIdx i h)) from rfl]
  have hkey : rightEnd (mirrorIdx (nextIdx i h)) = 1 - leftEnd (nextIdx i h) :=
    rightEnd_mirrorIdx _
  have hkey2 : leftEnd (nextIdx i h) = rightEnd i :=
    (rightEnd_eq_leftEnd_succ i h).symm
  rw [hkey, hkey2, hsame, hd]
  ring

/-! ## The global deadline is unchanged

Per-drone deadlines do **not** correspond: `droneNextTime i` consults the pair
to `i`'s right, while its reflection consults the pair to the reflected drone's
*left*. But the two candidate *sets* agree — every border and every pair event
appears on both sides, just indexed from the other end — so the minima agree.

The argument is one-sided: proving `mirror` never has a *later* deadline, then
applying that to `mirror c` and using the involution gives equality. -/

/-- The reflected pair whose events are those of the pair `(j, j+1)`. -/
theorem gap_mirror_pair (c : Config n) (j : Fin n) (hj : j.val + 1 < n) :
    c.mirror.gap (mirrorIdx (nextIdx j hj)) (mirror_next_lt j hj) = c.gap j hj := by
  rw [gap_mirror]
  congr 1
  rw [nextIdx_mirrorIdx_next, mirrorIdx_mirrorIdx]

/-- Re-indexing a pair predicate along an index equality. Needed because the
index appears inside a proof argument, which blocks `rw`. -/
theorem approaching_congr (c : Config n) {i i' : Fin n} (h : i.val + 1 < n)
    (h' : i'.val + 1 < n) (hii : i = i') :
    c.Approaching i h ↔ c.Approaching i' h' := by
  subst hii; exact Iff.rfl

theorem escorting_congr (c : Config n) {i i' : Fin n} (h : i.val + 1 < n)
    (h' : i'.val + 1 < n) (hii : i = i') :
    c.Escorting i h ↔ c.Escorting i' h' := by
  subst hii; exact Iff.rfl

theorem coLocated_congr (c : Config n) {i i' : Fin n} (h : i.val + 1 < n)
    (h' : i'.val + 1 < n) (hii : i = i') :
    c.CoLocated i h ↔ c.CoLocated i' h' := by
  subst hii; exact Iff.rfl

theorem atSeparation_congr (c : Config n) {i i' : Fin n} (h : i.val + 1 < n)
    (h' : i'.val + 1 < n) (hii : i = i') :
    c.AtSeparation i h ↔ c.AtSeparation i' h' := by
  subst hii; exact Iff.rfl

theorem mirror_pair_idx (j : Fin n) (hj : j.val + 1 < n) :
    mirrorIdx (nextIdx (mirrorIdx (nextIdx j hj)) (mirror_next_lt j hj)) = j := by
  rw [nextIdx_mirrorIdx_next, mirrorIdx_mirrorIdx]

theorem approaching_mirror_pair (c : Config n) (j : Fin n) (hj : j.val + 1 < n) :
    c.mirror.Approaching (mirrorIdx (nextIdx j hj)) (mirror_next_lt j hj)
      ↔ c.Approaching j hj := by
  rw [approaching_mirror]
  exact approaching_congr c _ hj (mirror_pair_idx j hj)

theorem escorting_mirror_pair (c : Config n) (j : Fin n) (hj : j.val + 1 < n) :
    c.mirror.Escorting (mirrorIdx (nextIdx j hj)) (mirror_next_lt j hj)
      ↔ c.Escorting j hj := by
  rw [escorting_mirror]
  exact escorting_congr c _ hj (mirror_pair_idx j hj)

theorem meetTime_mirror_pair (c : Config n) (j : Fin n) (hj : j.val + 1 < n) :
    c.mirror.meetTime (mirrorIdx (nextIdx j hj)) (mirror_next_lt j hj)
      = c.meetTime j hj := by
  unfold meetTime
  rw [gap_mirror_pair]

theorem separationTime_mirror_pair (c : Config n) (j : Fin n)
    (hj : j.val + 1 < n) (he : c.Escorting j hj) :
    c.mirror.separationTime (mirrorIdx (nextIdx j hj)) = c.separationTime j := by
  have he' : c.mirror.Escorting (mirrorIdx (nextIdx j hj)) (mirror_next_lt j hj) :=
    (escorting_mirror_pair c j hj).mpr he
  rw [separationTime_mirror c _ (mirror_next_lt j hj) he']
  congr 1
  rw [nextIdx_mirrorIdx_next, mirrorIdx_mirrorIdx]

/-- **Reflection never makes the next event later.** -/
theorem timeToNextEvent_mirror_le (c : Config n) (hn : 0 < n) :
    c.mirror.timeToNextEvent hn ≤ c.timeToNextEvent hn := by
  refine Finset.le_inf' _ _ (fun j _ => ?_)
  -- every candidate of `droneNextTime c j` is matched on the mirror side
  have hborder : c.mirror.timeToNextEvent hn ≤ c.borderTime j := by
    refine le_trans (timeToNextEvent_le hn (mirrorIdx j)) ?_
    refine le_trans (droneNextTime_le_borderTime c.mirror (mirrorIdx j)) ?_
    rw [borderTime_mirror, mirrorIdx_mirrorIdx]
  unfold droneNextTime
  split_ifs with hj hA hE
  · refine le_min hborder ?_
    refine le_trans (timeToNextEvent_le hn (mirrorIdx (nextIdx j hj))) ?_
    refine le_trans (droneNextTime_le_meetTime
      ((approaching_mirror_pair c j hj).mpr hA)) ?_
    rw [meetTime_mirror_pair]
  · refine le_min hborder ?_
    refine le_trans (timeToNextEvent_le hn (mirrorIdx (nextIdx j hj))) ?_
    refine le_trans (droneNextTime_le_separationTime
      ((escorting_mirror_pair c j hj).mpr hE)) ?_
    rw [separationTime_mirror_pair c j hj hE]
  · exact hborder
  · exact hborder

/-- **The global deadline is invariant under reflection.** -/
theorem timeToNextEvent_mirror (c : Config n) (hn : 0 < n) :
    c.mirror.timeToNextEvent hn = c.timeToNextEvent hn := by
  refine le_antisymm (timeToNextEvent_mirror_le c hn) ?_
  have h := timeToNextEvent_mirror_le c.mirror hn
  rwa [mirror_mirror] at h

/-! ## Reflected events

Under reflection `SepRight` becomes `SepLeft`, `MeetRight` becomes `MeetLeft`,
and each border event becomes the other. -/

theorem mirrorIdx_pos_iff (i : Fin n) : 0 < (mirrorIdx i).val ↔ i.val + 1 < n := by
  have := i.isLt
  simp only [mirrorIdx_val]
  omega

/-- The drone to the left of the reflected drone is the reflection of the drone
to its right. -/
theorem prevIdx_mirrorIdx (i : Fin n) (h : i.val + 1 < n) :
    prevIdx (mirrorIdx i) ((mirrorIdx_pos_iff i).mpr h) = mirrorIdx (nextIdx i h) := by
  apply Fin.ext
  have := i.isLt
  simp only [prevIdx_val, mirrorIdx_val, nextIdx_val]
  omega

/-- A separation in the mirrored world is a separation here. -/
theorem atSeparation_mirror (c : Config n) (i : Fin n) (h : i.val + 1 < n) :
    c.mirror.AtSeparation i h
      ↔ c.AtSeparation (mirrorIdx (nextIdx i h)) (mirror_next_lt i h) := by
  have hce : commonEnd (mirrorIdx (nextIdx i h)) = 1 - commonEnd i := by
    unfold commonEnd
    rw [rightEnd_mirrorIdx, rightEnd_eq_leftEnd_succ i h]
    rfl
  constructor
  · rintro ⟨hco, hp⟩
    have hco' := (coLocated_mirror c i h).mp hco
    have hsame : c.pos (mirrorIdx i) = c.pos (mirrorIdx (nextIdx i h)) := by
      have hx := hco'
      unfold CoLocated gap at hx
      rw [nextIdx_mirrorIdx_next i h] at hx
      linarith
    refine ⟨hco', ?_⟩
    simp only [mirror_pos] at hp
    rw [hce, ← hsame]
    linarith
  · rintro ⟨hco', hp⟩
    have hsame : c.pos (mirrorIdx i) = c.pos (mirrorIdx (nextIdx i h)) := by
      have hx := hco'
      unfold CoLocated gap at hx
      rw [nextIdx_mirrorIdx_next i h] at hx
      linarith
    rw [hce] at hp
    refine ⟨(coLocated_mirror c i h).mpr hco', ?_⟩
    simp only [mirror_pos]
    linarith

/-- Separating from the right becomes separating from the left. -/
theorem sepRight_mirror (c : Config n) (i : Fin n) :
    c.mirror.SepRight i ↔ c.SepLeft (mirrorIdx i) := by
  unfold SepRight SepLeft
  constructor
  · rintro ⟨h, hs⟩
    refine ⟨(mirrorIdx_pos_iff i).mpr h, ?_⟩
    exact (atSeparation_congr c _ _ (prevIdx_mirrorIdx i h)).mpr
      ((atSeparation_mirror c i h).mp hs)
  · rintro ⟨hp, hs⟩
    have h : i.val + 1 < n := (mirrorIdx_pos_iff i).mp hp
    refine ⟨h, (atSeparation_mirror c i h).mpr ?_⟩
    exact (atSeparation_congr c _ _ (prevIdx_mirrorIdx i h)).mp hs

/-- Meeting the right neighbour becomes meeting the left one. -/
theorem meetRight_mirror (c : Config n) (i : Fin n) :
    c.mirror.MeetRight i ↔ c.MeetLeft (mirrorIdx i) := by
  unfold MeetRight MeetLeft
  constructor
  · rintro ⟨h, hco, hA⟩
    refine ⟨(mirrorIdx_pos_iff i).mpr h, ?_, ?_⟩
    · exact (coLocated_congr c _ _ (prevIdx_mirrorIdx i h)).mpr
        ((coLocated_mirror c i h).mp hco)
    · exact (approaching_congr c _ _ (prevIdx_mirrorIdx i h)).mpr
        ((approaching_mirror c i h).mp hA)
  · rintro ⟨hp, hco, hA⟩
    have h : i.val + 1 < n := (mirrorIdx_pos_iff i).mp hp
    refine ⟨h, ?_, ?_⟩
    · exact (coLocated_mirror c i h).mpr
        ((coLocated_congr c _ _ (prevIdx_mirrorIdx i h)).mp hco)
    · exact (approaching_mirror c i h).mpr
        ((approaching_congr c _ _ (prevIdx_mirrorIdx i h)).mp hA)

/-- The mirror images of the previous two, obtained from them by reflecting
the configuration rather than reproving anything. -/
theorem sepLeft_mirror (c : Config n) (i : Fin n) :
    c.mirror.SepLeft i ↔ c.SepRight (mirrorIdx i) := by
  have h := sepRight_mirror c.mirror (mirrorIdx i)
  rw [mirror_mirror, mirrorIdx_mirrorIdx] at h
  exact h.symm

theorem meetLeft_mirror (c : Config n) (i : Fin n) :
    c.mirror.MeetLeft i ↔ c.MeetRight (mirrorIdx i) := by
  have h := meetRight_mirror c.mirror (mirrorIdx i)
  rw [mirror_mirror, mirrorIdx_mirrorIdx] at h
  exact h.symm

/-! ## Reflected escort headings

`escortDir` and `escortDirLeft` reflect into each other — **except exactly on
the shared boundary**, where they tie-break oppositely. That case never arises
where it is used: a meet is only consulted once a separation has been ruled
out, and for a co-located pair a separation is *precisely* being on the
boundary. Both lemmas therefore carry that disequality. -/

theorem escortDir_mirror (c : Config n) (i : Fin n)
    (hne : c.mirror.pos i ≠ commonEnd i) :
    c.mirror.escortDir i = (c.escortDirLeft (mirrorIdx i)).flip := by
  have hle : leftEnd (mirrorIdx i) = 1 - commonEnd i := by
    unfold commonEnd; exact leftEnd_mirrorIdx i
  have hpos : c.mirror.pos i = 1 - c.pos (mirrorIdx i) := rfl
  unfold escortDir escortDirLeft
  rcases lt_trichotomy (c.pos (mirrorIdx i)) (leftEnd (mirrorIdx i)) with hx | hx | hx
  · rw [hle] at hx
    rw [if_neg (by rw [hpos, not_lt]; linarith), if_pos (by rw [hle]; exact hx)]
    rfl
  · exact absurd (by rw [hpos, hx, hle]; ring) hne
  · rw [hle] at hx
    rw [if_pos (by rw [hpos]; linarith), if_neg (by rw [hle, not_lt]; linarith)]
    rfl

theorem escortDirLeft_mirror (c : Config n) (i : Fin n)
    (hne : c.mirror.pos i ≠ leftEnd i) :
    c.mirror.escortDirLeft i = (c.escortDir (mirrorIdx i)).flip := by
  have hce : commonEnd (mirrorIdx i) = 1 - leftEnd i := by
    unfold commonEnd; exact rightEnd_mirrorIdx i
  have hpos : c.mirror.pos i = 1 - c.pos (mirrorIdx i) := rfl
  unfold escortDir escortDirLeft
  rcases lt_trichotomy (c.pos (mirrorIdx i)) (commonEnd (mirrorIdx i)) with hx | hx | hx
  · rw [hce] at hx
    rw [if_neg (by rw [hpos, not_lt]; linarith), if_pos (by rw [hce]; exact hx)]
    rfl
  · exact absurd (by rw [hpos, hx, hce]; ring) hne
  · rw [hce] at hx
    rw [if_pos (by rw [hpos]; linarith), if_neg (by rw [hce, not_lt]; linarith)]
    rfl

/-! ## Mutual exclusion

The branch orders of `newDir` do *not* correspond under reflection — the left
border is checked first on one side and second on the other. That is harmless
because the paired branches are mutually exclusive, which is what these say. -/

theorem not_sepLeft_of_sepRight {c : Config n} {i : Fin n} (h : c.SepRight i) :
    ¬ c.SepLeft i := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  rintro hl
  have h1 : c.pos i = commonEnd i := h.2.2
  have h2 : c.pos i = leftEnd i := pos_eq_leftEnd_of_sepLeft hl
  have : leftEnd i < commonEnd i := by unfold commonEnd; exact leftEnd_lt_rightEnd hn i
  rw [h1] at h2
  linarith

theorem not_meetLeft_of_meetRight {c : Config n} {i : Fin n} (h : c.MeetRight i) :
    ¬ c.MeetLeft i := by
  obtain ⟨_hh, _hc, hA⟩ := h
  exact not_meetLeft_of_dir_right hA.1

/-- A meeting pair not separating is a pair off its shared boundary. -/
theorem pos_ne_commonEnd_of_meetRight {c : Config n} {i : Fin n}
    (hm : c.MeetRight i) (hns : ¬ c.SepRight i) : c.pos i ≠ commonEnd i := by
  obtain ⟨h, hco, -⟩ := hm
  intro hp
  exact hns ⟨h, hco, hp⟩

/-- And likewise on the other side. -/
theorem pos_ne_leftEnd_of_meetLeft {c : Config n} {i : Fin n}
    (hm : c.MeetLeft i) (hns : ¬ c.SepLeft i) : c.pos i ≠ leftEnd i := by
  obtain ⟨hp0, hco, -⟩ := hm
  intro hp
  refine hns ⟨hp0, hco, ?_⟩
  have hsame : c.pos (nextIdx (prevIdx i hp0) (prevIdx_lt i hp0)) = c.pos i := by
    rw [nextIdx_prevIdx]
  have hgap : c.gap (prevIdx i hp0) (prevIdx_lt i hp0) = 0 := hco
  unfold gap at hgap
  rw [hsame] at hgap
  have hce : commonEnd (prevIdx i hp0) = leftEnd i := by
    unfold commonEnd
    rw [rightEnd_eq_leftEnd_succ (prevIdx i hp0) (prevIdx_lt i hp0)]
    congr 1
    exact nextIdx_prevIdx i hp0
  rw [hce, ← hp]
  linarith

/-! ## The reflected heading

**`newDir` commutes with reflection.** Seven branches on each side, paired by
the correspondences above; the pairing crosses the priority order, which is
harmless because paired branches are mutually exclusive. -/

theorem newDir_mirror (c : Config n) (i : Fin n) :
    c.mirror.newDir i = (c.newDir (mirrorIdx i)).flip := by
  have hALB := atLeftBorder_mirror c i
  have hARB := atRightBorder_mirror c i
  have hSR := sepRight_mirror c i
  have hSL := sepLeft_mirror c i
  have hMR := meetRight_mirror c i
  have hML := meetLeft_mirror c i
  by_cases b1 : c.mirror.AtLeftBorder i
  · have r2 : c.AtRightBorder (mirrorIdx i) := hALB.mp b1
    have r1 : ¬ c.AtLeftBorder (mirrorIdx i) := not_atLeftBorder_of_atRightBorder r2
    rw [newDir_atLeftBorder b1, newDir_atRightBorder r1 r2]
    rfl
  by_cases b2 : c.mirror.AtRightBorder i
  · have r1 : c.AtLeftBorder (mirrorIdx i) := hARB.mp b2
    rw [newDir_atRightBorder b1 b2, newDir_atLeftBorder r1]
    rfl
  have nr1 : ¬ c.AtLeftBorder (mirrorIdx i) := fun hx => b2 (hARB.mpr hx)
  have nr2 : ¬ c.AtRightBorder (mirrorIdx i) := fun hx => b1 (hALB.mpr hx)
  by_cases b3 : c.mirror.SepRight i
  · have r4 : c.SepLeft (mirrorIdx i) := hSR.mp b3
    have nb4 : ¬ c.mirror.SepLeft i := not_sepLeft_of_sepRight b3
    have nr3 : ¬ c.SepRight (mirrorIdx i) := fun hx => nb4 (hSL.mpr hx)
    have hl : c.mirror.newDir i = Dir.left := by
      unfold newDir; rw [if_neg b1, if_neg b2, if_pos b3]
    have hr : c.newDir (mirrorIdx i) = Dir.right := by
      unfold newDir; rw [if_neg nr1, if_neg nr2, if_neg nr3, if_pos r4]
    rw [hl, hr]; rfl
  by_cases b4 : c.mirror.SepLeft i
  · have r3 : c.SepRight (mirrorIdx i) := hSL.mp b4
    have hl : c.mirror.newDir i = Dir.right := by
      unfold newDir; rw [if_neg b1, if_neg b2, if_neg b3, if_pos b4]
    have hr : c.newDir (mirrorIdx i) = Dir.left := by
      unfold newDir; rw [if_neg nr1, if_neg nr2, if_pos r3]
    rw [hl, hr]; rfl
  have nr3 : ¬ c.SepRight (mirrorIdx i) := fun hx => b4 (hSL.mpr hx)
  have nr4 : ¬ c.SepLeft (mirrorIdx i) := fun hx => b3 (hSR.mpr hx)
  by_cases b5 : c.mirror.MeetRight i
  · have r6 : c.MeetLeft (mirrorIdx i) := hMR.mp b5
    have nb6 : ¬ c.mirror.MeetLeft i := not_meetLeft_of_meetRight b5
    have nr5 : ¬ c.MeetRight (mirrorIdx i) := fun hx => nb6 (hML.mpr hx)
    have hne : c.mirror.pos i ≠ commonEnd i := pos_ne_commonEnd_of_meetRight b5 b3
    have hl : c.mirror.newDir i = c.mirror.escortDir i := by
      unfold newDir; rw [if_neg b1, if_neg b2, if_neg b3, if_neg b4, if_pos b5]
    have hr : c.newDir (mirrorIdx i) = c.escortDirLeft (mirrorIdx i) := by
      unfold newDir
      rw [if_neg nr1, if_neg nr2, if_neg nr3, if_neg nr4, if_neg nr5, if_pos r6]
    rw [hl, hr, escortDir_mirror c i hne]
  by_cases b6 : c.mirror.MeetLeft i
  · have r5 : c.MeetRight (mirrorIdx i) := hML.mp b6
    have hne : c.mirror.pos i ≠ leftEnd i := pos_ne_leftEnd_of_meetLeft b6 b4
    have hl : c.mirror.newDir i = c.mirror.escortDirLeft i := by
      unfold newDir
      rw [if_neg b1, if_neg b2, if_neg b3, if_neg b4, if_neg b5, if_pos b6]
    have hr : c.newDir (mirrorIdx i) = c.escortDir (mirrorIdx i) := by
      unfold newDir
      rw [if_neg nr1, if_neg nr2, if_neg nr3, if_neg nr4, if_pos r5]
    rw [hl, hr, escortDirLeft_mirror c i hne]
  have nr5 : ¬ c.MeetRight (mirrorIdx i) := fun hx => b6 (hML.mpr hx)
  have nr6 : ¬ c.MeetLeft (mirrorIdx i) := fun hx => b5 (hMR.mpr hx)
  rw [newDir_of_noEvent b1 b2 b3 b4 b5 b6,
    newDir_of_noEvent nr1 nr2 nr3 nr4 nr5 nr6]
  rfl

/-! ## Reflection commutes with running the system

The payoff. -/

/-- Flying and reflecting commute. -/
theorem advance_mirror (c : Config n) (dt : ℝ) :
    c.mirror.advance dt = (c.advance dt).mirror := by
  refine Config.ext rfl (funext fun i => ?_) (funext fun i => ?_)
  · simp only [advance_pos, mirror_pos, mirror_dir, Dir.sign_flip]
    ring
  · simp only [advance_dir, mirror_dir]

/-- **Stepping and reflecting commute.** -/
theorem step_mirror (c : Config n) (hn : 0 < n) :
    c.mirror.step hn = (c.step hn).mirror := by
  have hdt : c.mirror.timeToNextEvent hn = c.timeToNextEvent hn :=
    timeToNextEvent_mirror c hn
  refine Config.ext ?_ (funext fun i => ?_) (funext fun i => ?_)
  · simp only [step_time, mirror_time, hdt]
  · simp only [step_pos, mirror_pos, mirror_dir, Dir.sign_flip, hdt]
    ring
  · show (c.mirror.advance (c.mirror.timeToNextEvent hn)).newDir i
      = ((c.advance (c.timeToNextEvent hn)).newDir (mirrorIdx i)).flip
    rw [hdt, advance_mirror, newDir_mirror]

/-- **Running and reflecting commute.** -/
theorem run_mirror (c : Config n) (hn : 0 < n) (k : ℕ) :
    c.mirror.run hn k = (c.run hn k).mirror := by
  induction k with
  | zero => rfl
  | succ k ih => rw [run_succ, ih, step_mirror, run_succ]

/-! ## "By symmetry", made honest

Right synchronization of a run **is** left synchronization of the mirrored
run. Every result proved on the left now transfers. -/

/-- **The transfer principle.** -/
theorem rightSync_iff_leftSync_mirror (c : Config n) (hn : 0 < n) (i : Fin n)
    (k : ℕ) : RightSync c hn i k ↔ LeftSync c.mirror hn (mirrorIdx i) k := by
  unfold RightSync LeftSync
  constructor
  · intro h j hj
    rw [run_mirror]
    exact (leftEnd_le_mirror_pos_iff (c := c.run hn j) (mirrorIdx i)).mpr
      (by rw [mirrorIdx_mirrorIdx]; exact h j hj)
  · intro h j hj
    have hx := h j hj
    rw [run_mirror] at hx
    have := (leftEnd_le_mirror_pos_iff (c := c.run hn j) (mirrorIdx i)).mp hx
    rwa [mirrorIdx_mirrorIdx] at this

/-- The reflection of a well-behaved configuration is well behaved, so the
transfer principle applies wherever the invariant is assumed. -/
theorem invariant_mirror {c : Config n} (hn : 0 < n) (hi : c.Invariant) :
    c.mirror.Invariant := by
  refine ⟨onPerimeter_mirror hi.onPerimeter, ?_, ?_⟩
  · intro i h
    have := (gap_mirror c i h) ▸ (hi.adjOrdered (mirrorIdx (nextIdx i h))
      (mirror_next_lt i h))
    exact this
  · intro i h he
    have he' : c.Escorting (mirrorIdx (nextIdx i h)) (mirror_next_lt i h) :=
      (escorting_mirror c i h).mp he
    rw [separationTime_mirror c i h he]
    exact hi.escortsCoherent _ _ he'

end Config

end DPSS
