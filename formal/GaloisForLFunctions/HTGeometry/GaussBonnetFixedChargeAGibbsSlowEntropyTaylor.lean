import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSlowDisplacement

/-! The corpus parity-digit logarithm estimate controls the critical Gibbs entropy integrand. -/
namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem entropy_coordinate_remainder (x : ℝ) (hx : |x| ≤ 1 / 2) :
    |(1 + x) * Real.log (1 + x) - x - x ^ 2 / 2| ≤ 7 * |x| ^ 3 := by
  have hlog := abs_log_one_add_taylor_le (x := x) (by linarith)
  have hlin : |1 + x| ≤ 3 / 2 := by
    have h := abs_add_le (1 : ℝ) x
    norm_num only [abs_one] at h
    linarith
  have he : (1 + x) * Real.log (1 + x) - x - x ^ 2 / 2 =
      (1 + x) * (Real.log (1 + x) - x + x ^ 2 / 2) - x ^ 3 / 2 := by ring
  rw [he]
  have h : |(1 + x) * (Real.log (1 + x) - x + x ^ 2 / 2) - x ^ 3 / 2| ≤
      |(1 + x) * (Real.log (1 + x) - x + x ^ 2 / 2)| + |x ^ 3 / 2| := by
    rw [abs_le]
    constructor <;> linarith [
      neg_abs_le ((1 + x) * (Real.log (1 + x) - x + x ^ 2 / 2)),
      le_abs_self ((1 + x) * (Real.log (1 + x) - x + x ^ 2 / 2)),
      neg_abs_le (x ^ 3 / 2), le_abs_self (x ^ 3 / 2)]
  rw [abs_mul, abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  have hp := mul_le_mul hlin hlog (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 2)
  nlinarith [pow_nonneg (abs_nonneg x) 3]

/-- The slow Gibbs information integrand has an explicit cubic remainder at every time. -/
theorem egbFixedChargeAGibbsSlow_entropy_coordinate_remainder (n m : ℕ)
    (i : Fin (2 ^ (n + 3))) :
    |(1 + egbFixedChargeAGibbsSlowDisplacement n m i) *
        Real.log (1 + egbFixedChargeAGibbsSlowDisplacement n m i) -
      egbFixedChargeAGibbsSlowDisplacement n m i - (egbFixedChargeAGibbsSlowDisplacement n m i) ^ 2 / 2| ≤
        7 * |egbFixedChargeAGibbsSlowDisplacement n m i| ^ 3 :=
  entropy_coordinate_remainder _ (egbFixedChargeAGibbsSlowDisplacement_half_bound n m i)

/-- The slow relative information is an exact normalized sum of displacement entropy terms. -/
theorem egbFixedChargeAGibbsSlow_information_displacement_formula (n m : ℕ) :
    egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) =
      (∑ i, (1 + egbFixedChargeAGibbsSlowDisplacement n m i) *
        Real.log (1 + egbFixedChargeAGibbsSlowDisplacement n m i)) / (2 : ℝ) ^ (n + 3) := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [egbFixedChargeAGibbsEntropyDeficit, relEntropy, tsum_fintype]
  simp_rw [egbFixedChargeAGibbsSlowDisplacement_population]
  have hr (i : Fin (2 ^ (n + 3))) :
      ((1 + egbFixedChargeAGibbsSlowDisplacement n m i) / (2 : ℝ) ^ (n + 3)) /
        ((2 : ℝ) ^ (n + 3))⁻¹ = 1 + egbFixedChargeAGibbsSlowDisplacement n m i := by field_simp
  simp_rw [hr]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Collision excess is exactly the normalized displacement square sum. -/
theorem egbFixedChargeAGibbsSlow_collision_displacement_formula (n m : ℕ) :
    egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSlowEnergy n) =
      (∑ i, egbFixedChargeAGibbsSlowDisplacement n m i ^ 2) / ((2 : ℝ) ^ (n + 3)) ^ 2 := by
  unfold egbFixedChargeAGibbsCollisionExcess
  simp_rw [egbFixedChargeAGibbsSlowDisplacement_population]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end GaloisForLFunctions.HTGeometry
