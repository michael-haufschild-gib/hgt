import GaloisForLFunctions.HTGeometry.StaticShortcutRecurrenceChannelProductionLaw

/-!
# Static shortcut cross-recurrence capacity law

Selector recurrence contains unavoidable diagonal self-memory. This module removes it exactly.
The survivor counts only distinct samples that reuse one observer channel. Bounded channel capacity
can therefore support a long adaptive shortcut history only by paying genuine cross-time
recurrence. A uniform cross-coherence ceiling yields the sharp capacity obstruction.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {J C F : Type*} [Fintype J] [DecidableEq J]
variable [Fintype C] [DecidableEq C]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Unavoidable self-memory paid once by every selected sample. -/
def selectorDiagonalRecurrenceEnergy (r : J → F) (w : J → ℝ) : ℝ :=
  ∑ j, w j ^ (2 : ℕ) * ‖r j‖ ^ (2 : ℕ)

/-- Genuine cross-time recurrence retained only inside a reused observer channel. -/
def selectorCrossRecurrenceEnergy
    (r : J → F) (chosen : J → C) (w : J → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i,
    if chosen i = chosen j then
      w i * w j * inner ℝ (r i) (r j)
    else 0

/-- Cross-load counts ordered distinct-time pairs assigned to the same channel. -/
def selectorCrossLoad (chosen : J → C) (w : J → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i,
    if chosen i = chosen j then w i * w j else 0

omit [DecidableEq J] in
theorem selectorLoadEnergy_nonneg (chosen : J → C) (w : J → ℝ) :
    0 ≤ selectorLoadEnergy chosen w := by
  unfold selectorLoadEnergy
  positivity

omit [Fintype C] in
theorem selectorCrossLoad_nonneg
    (chosen : J → C) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) :
    0 ≤ selectorCrossLoad chosen w := by
  unfold selectorCrossLoad
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  by_cases hc : chosen i = chosen j
  · simp [hc, mul_nonneg (hw i) (hw j)]
  · simp [hc]

theorem selectorRecurrenceEnergy_eq_diagonal_add_cross
    (r : J → F) (chosen : J → C) (w : J → ℝ) :
    selectorRecurrenceEnergy r chosen w =
      selectorDiagonalRecurrenceEnergy r w +
        selectorCrossRecurrenceEnergy r chosen w := by
  rw [selectorRecurrenceEnergy_eq_pairSum]
  unfold selectorDiagonalRecurrenceEnergy selectorCrossRecurrenceEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  let f : J → ℝ := fun j =>
    if chosen i = chosen j then
      w i * w j * inner ℝ (r i) (r j)
    else 0
  calc
    (∑ j, if chosen i = chosen j then
        w i * w j * inner ℝ (r i) (r j) else 0) = ∑ j, f j := rfl
    _ = (∑ j ∈ Finset.univ.erase i, f j) + f i := by
      exact (Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)).symm
    _ = w i ^ (2 : ℕ) * ‖r i‖ ^ (2 : ℕ) +
        ∑ j ∈ Finset.univ.erase i,
          if chosen i = chosen j then
            w i * w j * inner ℝ (r i) (r j) else 0 := by
      simp only [f, if_pos, real_inner_self_eq_norm_sq]
      ring

theorem selectorLoadEnergy_eq_diagonal_add_cross
    (chosen : J → C) (w : J → ℝ) :
    selectorLoadEnergy chosen w =
      (∑ j, w j ^ (2 : ℕ)) + selectorCrossLoad chosen w := by
  have hload :
      selectorLoadEnergy chosen w =
        selectorRecurrenceEnergy (fun _ : J => (1 : ℝ)) chosen w := by
    unfold selectorLoadEnergy selectorRecurrenceEnergy
    apply Finset.sum_congr rfl
    intro c hc
    rw [weightedRecurrenceEnergy_eq_norm_sq]
    simp [weightedMemorySum, selectorChannelWeight, Real.norm_eq_abs, sq_abs]
  rw [hload, selectorRecurrenceEnergy_eq_pairSum]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_one, one_pow,
    mul_one]
  unfold selectorCrossLoad
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  let f : J → ℝ := fun j =>
    if chosen i = chosen j then w i * w j else 0
  calc
    (∑ j, if chosen i = chosen j then w i * w j else 0) = ∑ j, f j := rfl
    _ = (∑ j ∈ Finset.univ.erase i, f j) + f i := by
      exact (Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)).symm
    _ = w i ^ (2 : ℕ) +
        ∑ j ∈ Finset.univ.erase i,
          if chosen i = chosen j then w i * w j else 0 := by
      simp only [f, if_pos]
      ring

omit [Fintype C] in
theorem selectorCrossRecurrenceEnergy_le_coherence_mul_crossLoad
    (r : J → F) (chosen : J → C) (w : J → ℝ) {mu : ℝ}
    (hw : ∀ j, 0 ≤ w j)
    (hcoh : ∀ i j, i ≠ j → inner ℝ (r i) (r j) ≤ mu) :
    selectorCrossRecurrenceEnergy r chosen w ≤
      mu * selectorCrossLoad chosen w := by
  unfold selectorCrossRecurrenceEnergy selectorCrossLoad
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hc : chosen i = chosen j
  · simp only [hc, if_true]
    rw [mul_assoc]
    have h := mul_le_mul_of_nonneg_left
      (hcoh i j (Finset.ne_of_mem_erase hj).symm)
      (mul_nonneg (hw i) (hw j))
    nlinarith
  · simp [hc]

omit [DecidableEq J] [InnerProductSpace ℝ F] in
theorem selectorDiagonalRecurrenceEnergy_le
    (r : J → F) (w : J → ℝ) {D : ℝ}
    (hnorm : ∀ j, ‖r j‖ ^ (2 : ℕ) ≤ D) :
    selectorDiagonalRecurrenceEnergy r w ≤ D * ∑ j, w j ^ (2 : ℕ) := by
  unfold selectorDiagonalRecurrenceEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  calc
    w j ^ (2 : ℕ) * ‖r j‖ ^ (2 : ℕ) ≤ w j ^ (2 : ℕ) * D :=
      mul_le_mul_of_nonneg_left (hnorm j) (sq_nonneg (w j))
    _ = D * w j ^ (2 : ℕ) := by ring

theorem selectorThreshold_sq_load_le_diagonal_add_cross
    (r : J → F) (q : C → F) (chosen : J → C) (w : J → ℝ)
    {eta B : ℝ}
    (heta : 0 ≤ eta)
    (hw : ∀ j, 0 ≤ w j)
    (halign : ∀ j, eta ≤ inner ℝ (r j) (q (chosen j)))
    (hq : ∀ c, ‖q c‖ ^ (2 : ℕ) ≤ B) :
    eta ^ (2 : ℕ) * selectorLoadEnergy chosen w ≤
      B * (selectorDiagonalRecurrenceEnergy r w +
        selectorCrossRecurrenceEnergy r chosen w) := by
  rw [← selectorRecurrenceEnergy_eq_diagonal_add_cross]
  exact selectorThreshold_sq_load_le_recurrenceEnergy
    r q chosen w heta hw halign hq

/-- A uniform off-diagonal coherence ceiling converts the shortcut inequality into an exact
diagonal-versus-cross-load gap. -/
theorem selectorCoherenceGap_mul_load_le_diagonal
    (r : J → F) (q : C → F) (chosen : J → C) (w : J → ℝ)
    {eta B D mu : ℝ}
    (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (hw : ∀ j, 0 ≤ w j)
    (halign : ∀ j, eta ≤ inner ℝ (r j) (q (chosen j)))
    (hq : ∀ c, ‖q c‖ ^ (2 : ℕ) ≤ B)
    (hnorm : ∀ j, ‖r j‖ ^ (2 : ℕ) ≤ D)
    (hcoh : ∀ i j, i ≠ j → inner ℝ (r i) (r j) ≤ mu) :
    (eta ^ (2 : ℕ) - B * mu) * selectorLoadEnergy chosen w ≤
      B * (D - mu) * ∑ j, w j ^ (2 : ℕ) := by
  have hthreshold := selectorThreshold_sq_load_le_diagonal_add_cross
    r q chosen w heta hw halign hq
  have hdiag := selectorDiagonalRecurrenceEnergy_le r w hnorm
  have hcross := selectorCrossRecurrenceEnergy_le_coherence_mul_crossLoad
    r chosen w hw hcoh
  have hupper :
      B * (selectorDiagonalRecurrenceEnergy r w +
          selectorCrossRecurrenceEnergy r chosen w) ≤
        B * (D * (∑ j, w j ^ (2 : ℕ)) + mu * selectorCrossLoad chosen w) :=
    mul_le_mul_of_nonneg_left (add_le_add hdiag hcross) hB
  have hload := selectorLoadEnergy_eq_diagonal_add_cross chosen w
  calc
    (eta ^ (2 : ℕ) - B * mu) * selectorLoadEnergy chosen w =
        eta ^ (2 : ℕ) * selectorLoadEnergy chosen w -
          B * mu * ((∑ j, w j ^ (2 : ℕ)) + selectorCrossLoad chosen w) := by
      rw [hload]
      ring
    _ ≤ B * (D * (∑ j, w j ^ (2 : ℕ)) + mu * selectorCrossLoad chosen w) -
          B * mu * ((∑ j, w j ^ (2 : ℕ)) + selectorCrossLoad chosen w) :=
      sub_le_sub_right (hthreshold.trans hupper) _
    _ = B * (D - mu) * ∑ j, w j ^ (2 : ℕ) := by ring

/-- Under a positive coherence gap, bounded observer-channel capacity converts cross-time
anti-coherence into a quantitative obstruction to a long shortcut history. -/
theorem selectorMass_sq_le_capacity_mul_diagonal_of_coherence
    (r : J → F) (q : C → F) (chosen : J → C) (w : J → ℝ)
    {eta B D mu : ℝ} {K : ℕ}
    (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (hgap : 0 ≤ eta ^ (2 : ℕ) - B * mu)
    (hw : ∀ j, 0 ≤ w j)
    (halign : ∀ j, eta ≤ inner ℝ (r j) (q (chosen j)))
    (hq : ∀ c, ‖q c‖ ^ (2 : ℕ) ≤ B)
    (hnorm : ∀ j, ‖r j‖ ^ (2 : ℕ) ≤ D)
    (hcoh : ∀ i j, i ≠ j → inner ℝ (r i) (r j) ≤ mu)
    (hcapacity : (selectorOccupiedChannels chosen w).card ≤ K) :
    (eta ^ (2 : ℕ) - B * mu) * (∑ j, w j) ^ (2 : ℕ) ≤
      B * K * (D - mu) * ∑ j, w j ^ (2 : ℕ) := by
  have hmass := selectorTotalWeight_sq_le_occupied_mul_load chosen w
  have hloadNonneg := selectorLoadEnergy_nonneg chosen w
  have hcapacityLoad :
      (∑ j, w j) ^ (2 : ℕ) ≤ K * selectorLoadEnergy chosen w := by
    calc
      (∑ j, w j) ^ (2 : ℕ) ≤
          (selectorOccupiedChannels chosen w).card *
            selectorLoadEnergy chosen w := hmass
      _ ≤ K * selectorLoadEnergy chosen w := by gcongr
  have hsource := selectorCoherenceGap_mul_load_le_diagonal
    r q chosen w heta hB hw halign hq hnorm hcoh
  calc
    (eta ^ (2 : ℕ) - B * mu) * (∑ j, w j) ^ (2 : ℕ) ≤
        (eta ^ (2 : ℕ) - B * mu) * (K * selectorLoadEnergy chosen w) :=
      mul_le_mul_of_nonneg_left hcapacityLoad hgap
    _ = K * ((eta ^ (2 : ℕ) - B * mu) * selectorLoadEnergy chosen w) := by ring
    _ ≤ K * (B * (D - mu) * ∑ j, w j ^ (2 : ℕ)) := by gcongr
    _ = B * K * (D - mu) * ∑ j, w j ^ (2 : ℕ) := by ring

/-- If diagonal memory cannot pay a shortcut history and distinct-time recurrence stays below
`mu`, more than `K` observer channels must be occupied. -/
theorem selectorOccupiedChannels_gt_of_coherenceBudget_lt
    (r : J → F) (q : C → F) (chosen : J → C) (w : J → ℝ)
    {eta B D mu : ℝ} {K : ℕ}
    (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (hgap : 0 ≤ eta ^ (2 : ℕ) - B * mu)
    (hw : ∀ j, 0 ≤ w j)
    (halign : ∀ j, eta ≤ inner ℝ (r j) (q (chosen j)))
    (hq : ∀ c, ‖q c‖ ^ (2 : ℕ) ≤ B)
    (hnorm : ∀ j, ‖r j‖ ^ (2 : ℕ) ≤ D)
    (hcoh : ∀ i j, i ≠ j → inner ℝ (r i) (r j) ≤ mu)
    (hbudget : B * K * (D - mu) * (∑ j, w j ^ (2 : ℕ)) <
      (eta ^ (2 : ℕ) - B * mu) * (∑ j, w j) ^ (2 : ℕ)) :
    K < (selectorOccupiedChannels chosen w).card := by
  by_contra hnot
  have hcapacity : (selectorOccupiedChannels chosen w).card ≤ K :=
    Nat.le_of_not_gt hnot
  have hbound := selectorMass_sq_le_capacity_mul_diagonal_of_coherence
    r q chosen w heta hB hgap hw halign hq hnorm hcoh hcapacity
  linarith

/-- Unit-sample form: a bounded channel family can carry only linearly many
pairwise anti-coherent shortcuts. -/
theorem selectorCard_sq_le_capacity_mul_card_of_coherence
    (r : J → F) (q : C → F) (chosen : J → C)
    {eta B D mu : ℝ} {K : ℕ}
    (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (hgap : 0 ≤ eta ^ (2 : ℕ) - B * mu)
    (halign : ∀ j, eta ≤ inner ℝ (r j) (q (chosen j)))
    (hq : ∀ c, ‖q c‖ ^ (2 : ℕ) ≤ B)
    (hnorm : ∀ j, ‖r j‖ ^ (2 : ℕ) ≤ D)
    (hcoh : ∀ i j, i ≠ j → inner ℝ (r i) (r j) ≤ mu)
    (hcapacity : (selectorOccupiedChannels chosen (fun _ => 1)).card ≤ K) :
    (eta ^ (2 : ℕ) - B * mu) * (Fintype.card J : ℝ) ^ (2 : ℕ) ≤
      B * K * (D - mu) * (Fintype.card J : ℝ) := by
  simpa using selectorMass_sq_le_capacity_mul_diagonal_of_coherence
    r q chosen (fun _ => 1) heta hB hgap (fun _ => by norm_num)
      halign hq hnorm hcoh hcapacity

/-- After self-memory is charged once, bounded channel capacity forces genuine cross-time
recurrence inside reused observer channels. -/
theorem selectorCapacity_forces_crossRecurrence
    (r : J → F) (q : C → F) (chosen : J → C) (w : J → ℝ)
    {eta B : ℝ} {K : ℕ}
    (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (hw : ∀ j, 0 ≤ w j)
    (halign : ∀ j, eta ≤ inner ℝ (r j) (q (chosen j)))
    (hq : ∀ c, ‖q c‖ ^ (2 : ℕ) ≤ B)
    (hcapacity : (selectorOccupiedChannels chosen w).card ≤ K) :
    eta ^ (2 : ℕ) * (∑ j, w j) ^ (2 : ℕ) -
        B * K * selectorDiagonalRecurrenceEnergy r w ≤
      B * K * selectorCrossRecurrenceEnergy r chosen w := by
  have hmain := selectorMass_sq_le_capacity_mul_recurrence
    r q chosen w heta hB hw halign hq hcapacity
  rw [selectorRecurrenceEnergy_eq_diagonal_add_cross] at hmain
  linarith

end

end GaloisForLFunctions.HTGeometry
