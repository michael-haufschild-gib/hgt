import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSlowEntropyRemainder

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Filter Topology

/-- Relative information normalized by its sharp exponential decay factor. -/
def egbFixedChargeAGibbsSlowNormalizedInformation (n m : ℕ) : ℝ :=
  egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) / (4 / 9 : ℝ) ^ m

/-- The exact leading information coefficient of the slow positive Gibbs state. -/
def egbFixedChargeAGibbsSlowInformationPrefactor (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (n + 3) / 2) * egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n)

/-- The leading information coefficient is strictly positive. -/
theorem egbFixedChargeAGibbsSlowInformationPrefactor_pos (n : ℕ) :
    0 < egbFixedChargeAGibbsSlowInformationPrefactor n :=
  mul_pos (by positivity) (egbFixedChargeAGibbsSlow_collision_initial_pos n)

/-- Normalized information approaches its leading coefficient with an explicit geometric error. -/
theorem egbFixedChargeAGibbsSlowNormalizedInformation_error (n m : ℕ) :
    |egbFixedChargeAGibbsSlowNormalizedInformation n m - egbFixedChargeAGibbsSlowInformationPrefactor n| ≤
      (7 * egbFixedChargeAGibbsSlowInformationPrefactor n) * (2 / 3 : ℝ) ^ m := by
  have hr : 0 < (4 / 9 : ℝ) ^ m := pow_pos (by norm_num) _
  have h := egbFixedChargeAGibbsSlow_entropy_quadratic_remainder n m
  rw [egbFixedChargeAGibbsSlow_collision_exact] at h
  have hd := div_le_div_of_nonneg_right h hr.le
  unfold egbFixedChargeAGibbsSlowNormalizedInformation egbFixedChargeAGibbsSlowInformationPrefactor
  have he : egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) / (4 / 9 : ℝ) ^ m -
      ((2 : ℝ) ^ (n + 3) / 2) * egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n) =
        (egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) -
          ((2 : ℝ) ^ (n + 3) / 2) * ((4 / 9 : ℝ) ^ m *
            egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n))) / (4 / 9 : ℝ) ^ m := by
    field_simp
    <;> ring
  rw [he, abs_div, abs_of_pos hr]
  calc
    _ ≤ ((7 * (2 : ℝ) ^ (n + 3) / 2) * (2 / 3 : ℝ) ^ m *
        ((4 / 9 : ℝ) ^ m * egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n))) /
          (4 / 9 : ℝ) ^ m := hd
    _ = _ := by field_simp <;> ring

/-- The sharp exponential normalization has an exact nonzero limit. -/
theorem egbFixedChargeAGibbsSlowNormalizedInformation_limit (n : ℕ) :
    Tendsto (fun m => egbFixedChargeAGibbsSlowNormalizedInformation n m) atTop
      (nhds (egbFixedChargeAGibbsSlowInformationPrefactor n)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1)
  have hc : Tendsto (fun _ : ℕ => 7 * egbFixedChargeAGibbsSlowInformationPrefactor n) atTop
      (nhds (7 * egbFixedChargeAGibbsSlowInformationPrefactor n)) := tendsto_const_nhds
  have hb : Tendsto (fun m : ℕ => (7 * egbFixedChargeAGibbsSlowInformationPrefactor n) * (2 / 3 : ℝ) ^ m)
      atTop (nhds 0) := by simpa using hc.mul hp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using
    squeeze_zero (fun m => abs_nonneg (egbFixedChargeAGibbsSlowNormalizedInformation n m -
      egbFixedChargeAGibbsSlowInformationPrefactor n))
      (egbFixedChargeAGibbsSlowNormalizedInformation_error n) hb

end
end GaloisForLFunctions.HTGeometry
