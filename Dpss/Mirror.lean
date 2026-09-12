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

end Config

end DPSS
