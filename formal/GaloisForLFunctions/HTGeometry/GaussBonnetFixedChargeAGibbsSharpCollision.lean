import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSlowRealization

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The optimal collision coefficient across all finite Gibbs energy landscapes is the spectral value. -/
theorem egbFixedChargeAGibbsCollisionExcess_sharp_factor (n m : ℕ) (B : ℝ) :
    (∀ (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ),
      egbFixedChargeAGibbsCollisionExcess n m β E ≤ B * egbFixedChargeAGibbsCollisionExcess n 0 β E) ↔
        (4 / 9 : ℝ) ^ m ≤ B := by
  constructor
  · intro h
    have hw := h 1 (egbFixedChargeAGibbsSlowEnergy n)
    rw [egbFixedChargeAGibbsSlow_collision_exact] at hw
    nlinarith [egbFixedChargeAGibbsSlow_collision_initial_pos n]
  · intro h β E
    exact (egbFixedChargeAGibbsCollisionExcess_spectral_bound n m β E).trans
      (mul_le_mul_of_nonneg_right h (egbFixedChargeAGibbsCollisionExcess_nonneg n 0 β E))

/-- Even restricting inverse temperature to one leaves the same optimal collision coefficient. -/
theorem egbFixedChargeAGibbsCollisionExcess_unit_temperature_sharp (n m : ℕ) (B : ℝ) :
    (∀ E : Fin (2 ^ (n + 3)) → ℝ,
      egbFixedChargeAGibbsCollisionExcess n m 1 E ≤ B * egbFixedChargeAGibbsCollisionExcess n 0 1 E) ↔
        (4 / 9 : ℝ) ^ m ≤ B := by
  constructor
  · intro h
    have hw := h (egbFixedChargeAGibbsSlowEnergy n)
    rw [egbFixedChargeAGibbsSlow_collision_exact] at hw
    nlinarith [egbFixedChargeAGibbsSlow_collision_initial_pos n]
  · intro h E
    exact (egbFixedChargeAGibbsCollisionExcess_spectral_bound n m 1 E).trans
      (mul_le_mul_of_nonneg_right h (egbFixedChargeAGibbsCollisionExcess_nonneg n 0 1 E))

end
end GaloisForLFunctions.HTGeometry
