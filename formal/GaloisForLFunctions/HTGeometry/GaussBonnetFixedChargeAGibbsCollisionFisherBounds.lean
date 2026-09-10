import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionProjectiveMinimum

/-!
# Spectral bound and asymptotic collapse of collision Fisher geometry

The squared gap between the two collision rates bounds the Fisher value.
Equality occurs precisely when the two weighted moment contributions agree
and are nonzero. Every fixed input eventually loses its Fisher value.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter

private theorem active_collision_pos (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ)
    (hz : ¬ (egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0)) :
    0 < egbFixedChargeAGibbsCollisionExcess n (m + 1) β E := by
  have hn := egbFixedChargeAGibbsCollisionExcess_nonneg n (m + 1) β E
  have hne : egbFixedChargeAGibbsCollisionExcess n (m + 1) β E ≠ 0 := by
    intro he
    exact hz ((egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mp he)
  exact lt_of_le_of_ne hn (Ne.symm hne)

private theorem spectral_balance_square (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (25 / 144 : ℝ) * egbFixedChargeAGibbsCollisionExcess n (m + 1) β E ^ 2 -
      4 * egbFixedChargeAGibbsCollisionHankelDefect n m β E =
      (25 / 144 : ℝ) *
        ((4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E -
          (1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) ^ 2 := by
  rw [egbFixedChargeAGibbsCollisionExcess_two_rate, egbFixedChargeAGibbsCollisionHankelDefect_formula,
    show (1 / 81 : ℝ) = (4 / 9 : ℝ) * (1 / 36 : ℝ) by norm_num, mul_pow]
  ring

/-- The collision Fisher value is bounded by the squared separation of the two temporal rates. -/
theorem egbFixedChargeAGibbsCollisionFisherValue_upper_bound (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionFisherValue n m β E ≤ 25 / 144 := by
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · rw [(egbFixedChargeAGibbsCollisionFisherValue_zero_iff n m β E).mpr (Or.inl hz.1)]
    norm_num
  · have hc := active_collision_pos n m β E hz
    rw [egbFixedChargeAGibbsCollisionFisherValue_formula]
    apply (div_le_iff₀ (sq_pos_of_pos hc)).mpr
    have h := spectral_balance_square n m β E
    nlinarith [sq_nonneg ((4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E -
      (1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E)]

/-- Saturation requires an active history with equal slow and fast weighted contributions. -/
theorem egbFixedChargeAGibbsCollisionFisherValue_upper_eq_iff (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionFisherValue n m β E = 25 / 144 ↔
      0 < egbFixedChargeAGibbsCollisionExcess n (m + 1) β E ∧
      (4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E =
        (1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E := by
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · have hc := (egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mpr hz
    rw [(egbFixedChargeAGibbsCollisionFisherValue_zero_iff n m β E).mpr (Or.inl hz.1), hc]
    norm_num
  · have hc := active_collision_pos n m β E hz
    simp only [hc, true_and]
    rw [egbFixedChargeAGibbsCollisionFisherValue_formula, div_eq_iff (sq_pos_of_pos hc).ne']
    have h := spectral_balance_square n m β E
    constructor
    · intro he
      have hs : ((4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E -
          (1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) ^ 2 = 0 := by
        nlinarith [h]
      exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hs)
    · intro he
      rw [he] at h
      nlinarith [h]

/-- Every fixed input has vanishing temporal Fisher value in the long-time limit. -/
theorem egbFixedChargeAGibbsCollisionFisherValue_tendsto_zero (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m : ℕ => egbFixedChargeAGibbsCollisionFisherValue n m β E)
      atTop (nhds 0) := by
  have h := egbFixedChargeAGibbsCollisionExcess_step_ratio_limit n β E
  change Tendsto (fun m : ℕ => egbFixedChargeAGibbsCollisionRatio n m β E) atTop
    (nhds (egbFixedChargeAGibbsDominantCollisionRate n β E)) at h
  have hs := (Filter.tendsto_add_atTop_iff_nat
    (f := fun m : ℕ => egbFixedChargeAGibbsCollisionRatio n m β E) 1).mpr h
  have ht := (h.const_mul 4).mul (hs.sub h)
  simpa only [← egbFixedChargeAGibbsCollisionFisherValue_ratio_increment, sub_self, mul_zero] using ht

end
end GaloisForLFunctions.HTGeometry
