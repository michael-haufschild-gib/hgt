import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalSlowProfile

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The slow real mode survives every finite number of transitions. -/
theorem egbFixedChargeACriticalSlowProfile_survives (n m : ℕ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
      (egbFixedChargeACriticalSlowProfile n) ≠ 0 := by
  rw [egbFixedChargeACriticalSlowProfile_evolution]
  intro h
  have h0 := congrFun h 0
  change (2 / 3 : ℝ) ^ m * egbFixedChargeACriticalSlowProfile n 0 = 0 at h0
  have hp := mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2 / 3) m)
    (egbFixedChargeACriticalSlowProfile_first_pos n)
  linarith

/-- The optimal uniform coefficient for centered energy after any finite time is exactly four ninths to that power. -/
theorem egbFixedChargeACriticalCenteredEnergy_sharp_factor (n m : ℕ) (B : ℝ) :
    (∀ f : Fin (2 ^ (n + 3)) → ℝ,
      egbFixedChargeACriticalCenteredEnergy n
        ((egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f) ≤
          B * egbFixedChargeACriticalCenteredEnergy n f) ↔ (4 / 9 : ℝ) ^ m ≤ B := by
  constructor
  · intro h
    have hw := h (egbFixedChargeACriticalSlowProfile n)
    rw [egbFixedChargeACriticalSlowProfile_energy_exact] at hw
    nlinarith [egbFixedChargeACriticalSlowProfile_energy_pos n]
  · intro h f
    exact (egbFixedChargeACriticalCenteredEnergy_geometric n m f).trans
      (mul_le_mul_of_nonneg_right h (egbFixedChargeACriticalCenteredEnergy_nonneg n f))

end
end GaloisForLFunctions.HTGeometry
