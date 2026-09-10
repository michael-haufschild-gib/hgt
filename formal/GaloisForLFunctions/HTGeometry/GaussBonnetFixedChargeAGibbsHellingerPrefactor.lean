import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSlowHellingerRemainder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Squared Hellinger distance of the actual positive slow Gibbs family from uniformity. -/
def egbFixedChargeAGibbsSlowHellingerSquared (n m : ℕ) : ℝ :=
  finitePacketHellinger
    (egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsSlowEnergy n))
    (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ^ 2
open Filter Topology

/-- Relative squared Hellinger distance normalized by its sharp exponential decay factor. -/
def egbFixedChargeAGibbsSlowNormalizedHellinger (n m : ℕ) : ℝ :=
  egbFixedChargeAGibbsSlowHellingerSquared n m / (4 / 9 : ℝ) ^ m

/-- The exact leading squared Hellinger distance coefficient of the slow positive Gibbs state. -/
def egbFixedChargeAGibbsSlowHellingerPrefactor (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (n + 3) / 4) * egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n)

/-- The leading squared Hellinger distance coefficient is strictly positive. -/
theorem egbFixedChargeAGibbsSlowHellingerPrefactor_pos (n : ℕ) :
    0 < egbFixedChargeAGibbsSlowHellingerPrefactor n :=
  mul_pos (by positivity) (egbFixedChargeAGibbsSlow_collision_initial_pos n)

/-- Normalized squared Hellinger distance approaches its leading coefficient with an explicit geometric error. -/
theorem egbFixedChargeAGibbsSlowNormalizedHellinger_error (n m : ℕ) :
    |egbFixedChargeAGibbsSlowNormalizedHellinger n m - egbFixedChargeAGibbsSlowHellingerPrefactor n| ≤
      (2 * egbFixedChargeAGibbsSlowHellingerPrefactor n) * (2 / 3 : ℝ) ^ m := by
  have hr : 0 < (4 / 9 : ℝ) ^ m := pow_pos (by norm_num) _
  have h := egbFixedChargeAGibbsSlow_hellinger_quadratic_remainder n m
  rw [egbFixedChargeAGibbsSlow_collision_exact] at h
  have hd := div_le_div_of_nonneg_right h hr.le
  unfold egbFixedChargeAGibbsSlowNormalizedHellinger egbFixedChargeAGibbsSlowHellingerPrefactor
  have he : egbFixedChargeAGibbsSlowHellingerSquared n m / (4 / 9 : ℝ) ^ m -
      ((2 : ℝ) ^ (n + 3) / 4) * egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n) =
        (egbFixedChargeAGibbsSlowHellingerSquared n m -
          ((2 : ℝ) ^ (n + 3) / 4) * ((4 / 9 : ℝ) ^ m *
            egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n))) / (4 / 9 : ℝ) ^ m := by
    field_simp
    <;> ring
  rw [he, abs_div, abs_of_pos hr]
  calc
    _ ≤ (((2 : ℝ) ^ (n + 3) / 2) * (2 / 3 : ℝ) ^ m *
        ((4 / 9 : ℝ) ^ m * egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n))) /
          (4 / 9 : ℝ) ^ m := hd
    _ = _ := by field_simp <;> ring

/-- The sharp exponential normalization has an exact nonzero limit. -/
theorem egbFixedChargeAGibbsSlowNormalizedHellinger_limit (n : ℕ) :
    Tendsto (fun m => egbFixedChargeAGibbsSlowNormalizedHellinger n m) atTop
      (nhds (egbFixedChargeAGibbsSlowHellingerPrefactor n)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1)
  have hc : Tendsto (fun _ : ℕ => 2 * egbFixedChargeAGibbsSlowHellingerPrefactor n) atTop
      (nhds (2 * egbFixedChargeAGibbsSlowHellingerPrefactor n)) := tendsto_const_nhds
  have hb : Tendsto (fun m : ℕ => (2 * egbFixedChargeAGibbsSlowHellingerPrefactor n) * (2 / 3 : ℝ) ^ m)
      atTop (nhds 0) := by simpa using hc.mul hp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using
    squeeze_zero (fun m => abs_nonneg (egbFixedChargeAGibbsSlowNormalizedHellinger n m -
      egbFixedChargeAGibbsSlowHellingerPrefactor n))
      (egbFixedChargeAGibbsSlowNormalizedHellinger_error n) hb

end
end GaloisForLFunctions.HTGeometry
