import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsInformationRateClassification

/-!
# Input-selected collision envelopes

The critical thermal kernel obtained from arXiv:2609.00025 exposes an exact
spectral envelope for every Gibbs input. These are mathematical consequences
of that kernel, not a proposed physical stochastic evolution.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Energy in the slowest nonzero nonconstant spectral sector. -/
def egbFixedChargeAGibbsDominantModeEnergy (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 then
    egbFixedChargeAGibbsFastModeEnergy n β E
  else egbFixedChargeAGibbsSlowModeEnergy n β E

/-- Every selected collision rate lies between zero and four ninths. -/
theorem egbFixedChargeAGibbsDominantCollisionRate_bounds (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    0 ≤ egbFixedChargeAGibbsDominantCollisionRate n β E ∧
      egbFixedChargeAGibbsDominantCollisionRate n β E ≤ 4 / 9 := by
  unfold egbFixedChargeAGibbsDominantCollisionRate
  split_ifs <;> norm_num

/-- A positive selected rate is equivalent to positive surviving energy. -/
theorem egbFixedChargeAGibbsDominantModeEnergy_pos_iff (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    0 < egbFixedChargeAGibbsDominantModeEnergy n β E ↔
      0 < egbFixedChargeAGibbsDominantCollisionRate n β E := by
  have ha := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
  have hb := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
  unfold egbFixedChargeAGibbsDominantModeEnergy egbFixedChargeAGibbsDominantCollisionRate
  split_ifs with hA hB
  · simp [hB]
  · have hp : 0 < egbFixedChargeAGibbsFastModeEnergy n β E :=
      lt_of_le_of_ne hb (by intro h; exact hB h.symm)
    norm_num [hp]
  · have hp : 0 < egbFixedChargeAGibbsSlowModeEnergy n β E :=
      lt_of_le_of_ne ha (by intro h; exact hA h.symm)
    norm_num [hp]

/-- The surviving sector gives matching geometric lower and upper collision envelopes. -/
theorem egbFixedChargeAGibbsCollisionExcess_dominant_bounds (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsDominantCollisionRate n β E ^ (m + 1) *
        egbFixedChargeAGibbsDominantModeEnergy n β E ≤
      egbFixedChargeAGibbsCollisionExcess n (m + 1) β E ∧
    egbFixedChargeAGibbsCollisionExcess n (m + 1) β E ≤
      egbFixedChargeAGibbsDominantCollisionRate n β E ^ (m + 1) *
        (egbFixedChargeAGibbsSlowModeEnergy n β E +
          egbFixedChargeAGibbsFastModeEnergy n β E) := by
  have ha := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
  have hb := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
  rw [egbFixedChargeAGibbsCollisionExcess_two_rate]
  unfold egbFixedChargeAGibbsDominantModeEnergy egbFixedChargeAGibbsDominantCollisionRate
  split_ifs with hA hB
  · simp [hA, hB]
  · simp [hA]
  · have hpow : (1 / 36 : ℝ) ^ (m + 1) ≤ (4 / 9 : ℝ) ^ (m + 1) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have hf : 0 ≤ (1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E :=
      mul_nonneg (by positivity) hb
    have hp := mul_le_mul_of_nonneg_right hpow hb
    constructor <;> nlinarith

end
end GaloisForLFunctions.HTGeometry
