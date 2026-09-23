import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSlowEntropyTaylor

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The exact relative-information error is controlled by the cubic displacement sum. -/
theorem egbFixedChargeAGibbsSlow_entropy_cubic_remainder (n m : ℕ) :
    |egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) -
      ((2 : ℝ) ^ (n + 3) / 2) * egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSlowEnergy n)| ≤
        (7 / (2 : ℝ) ^ (n + 3)) * ∑ i, |egbFixedChargeAGibbsSlowDisplacement n m i| ^ (3 : ℕ) := by
  have hn : 0 < (2 : ℝ) ^ (n + 3) := pow_pos (by norm_num) _
  have he : egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) -
      ((2 : ℝ) ^ (n + 3) / 2) * egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSlowEnergy n) =
        (∑ i, ((1 + egbFixedChargeAGibbsSlowDisplacement n m i) *
          Real.log (1 + egbFixedChargeAGibbsSlowDisplacement n m i) -
            egbFixedChargeAGibbsSlowDisplacement n m i - (egbFixedChargeAGibbsSlowDisplacement n m i) ^ (2 : ℕ) / 2)) /
          (2 : ℝ) ^ (n + 3) := by
    rw [egbFixedChargeAGibbsSlow_information_displacement_formula,
      egbFixedChargeAGibbsSlow_collision_displacement_formula]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div,
      egbFixedChargeAGibbsSlowDisplacement_mass_zero, sub_zero]
    field_simp
    <;> ring
  rw [he, abs_div, abs_of_pos hn]
  have hsum := Finset.abs_sum_le_sum_abs
    (fun i : Fin (2 ^ (n + 3)) =>
      (1 + egbFixedChargeAGibbsSlowDisplacement n m i) * Real.log (1 + egbFixedChargeAGibbsSlowDisplacement n m i) -
        egbFixedChargeAGibbsSlowDisplacement n m i - (egbFixedChargeAGibbsSlowDisplacement n m i) ^ (2 : ℕ) / 2)
    Finset.univ
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (2 ^ (n + 3))))) =>
    egbFixedChargeAGibbsSlow_entropy_coordinate_remainder n m i)
  have h := div_le_div_of_nonneg_right (hsum.trans hb) hn.le
  rw [← Finset.mul_sum] at h
  calc
    _ ≤ (7 * ∑ i, |egbFixedChargeAGibbsSlowDisplacement n m i| ^ (3 : ℕ)) /
        (2 : ℝ) ^ (n + 3) := h
    _ = _ := by ring

/-- Pointwise geometric decay controls the cubic sum by the squared displacement sum. -/
theorem egbFixedChargeAGibbsSlow_displacement_cubic_bound (n m : ℕ) :
    ∑ i, |egbFixedChargeAGibbsSlowDisplacement n m i| ^ (3 : ℕ) ≤
      ((2 / 3 : ℝ) ^ m / 2) * ∑ i, egbFixedChargeAGibbsSlowDisplacement n m i ^ (2 : ℕ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_right (egbFixedChargeAGibbsSlowDisplacement_bound n m i)
    (sq_nonneg (egbFixedChargeAGibbsSlowDisplacement n m i))
  have he : |egbFixedChargeAGibbsSlowDisplacement n m i| ^ (3 : ℕ) =
      |egbFixedChargeAGibbsSlowDisplacement n m i| * egbFixedChargeAGibbsSlowDisplacement n m i ^ (2 : ℕ) := by
    rw [pow_succ _ 2, sq_abs]
    ring
  rw [he]
  exact h

/-- Relative entropy differs from half the normalized collision excess by an explicit smaller geometric term. -/
theorem egbFixedChargeAGibbsSlow_entropy_quadratic_remainder (n m : ℕ) :
    |egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) -
      ((2 : ℝ) ^ (n + 3) / 2) * egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSlowEnergy n)| ≤
        (7 * (2 : ℝ) ^ (n + 3) / 2) * (2 / 3 : ℝ) ^ m *
          egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSlowEnergy n) := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    _ ≤ (7 / (2 : ℝ) ^ (n + 3)) * ∑ i, |egbFixedChargeAGibbsSlowDisplacement n m i| ^ (3 : ℕ) :=
      egbFixedChargeAGibbsSlow_entropy_cubic_remainder n m
    _ ≤ (7 / (2 : ℝ) ^ (n + 3)) *
        (((2 / 3 : ℝ) ^ m / 2) * ∑ i, egbFixedChargeAGibbsSlowDisplacement n m i ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left (egbFixedChargeAGibbsSlow_displacement_cubic_bound n m) (by positivity)
    _ = _ := by
      rw [egbFixedChargeAGibbsSlow_collision_displacement_formula]
      field_simp

end
end GaloisForLFunctions.HTGeometry
