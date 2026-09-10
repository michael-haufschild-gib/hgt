import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalModeOrthogonality

/-! # Internally normalized real slow and fast modes -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

def egbFixedChargeACriticalUnitSlow (n : ℕ) : Fin (2 ^ (n + 3)) → ℝ :=
  fun i => (Real.sqrt (egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalSlowProfile n)))⁻¹ *
    egbFixedChargeACriticalSlowProfile n i

def egbFixedChargeACriticalUnitFast (n : ℕ) : Fin (2 ^ (n + 3)) → ℝ :=
  fun i => (Real.sqrt (egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalFastProfile n)))⁻¹ *
    egbFixedChargeACriticalFastProfile n i

/-- Both normalized modes retain exactly zero total mass. -/
theorem egbFixedChargeACriticalUnitModes_mass_zero (n : ℕ) :
    (∑ i, egbFixedChargeACriticalUnitSlow n i) = 0 ∧
      (∑ i, egbFixedChargeACriticalUnitFast n i) = 0 := by
  simp only [egbFixedChargeACriticalUnitSlow, egbFixedChargeACriticalUnitFast, ← Finset.mul_sum,
    egbFixedChargeACriticalSlowProfile_mass_zero, egbFixedChargeACriticalFastProfile_mass_zero, mul_zero, and_self]

/-- Centering preserves both normalized modes. -/
theorem egbFixedChargeACriticalUnitModes_centered (n : ℕ) :
    egbFixedChargeACriticalCenteredProfile n (egbFixedChargeACriticalUnitSlow n) = egbFixedChargeACriticalUnitSlow n ∧
      egbFixedChargeACriticalCenteredProfile n (egbFixedChargeACriticalUnitFast n) = egbFixedChargeACriticalUnitFast n := by
  unfold egbFixedChargeACriticalUnitSlow egbFixedChargeACriticalUnitFast
  simp only [egbFixedChargeACriticalCenteredProfile_scale, egbFixedChargeACriticalSlowProfile_centered,
    egbFixedChargeACriticalFastProfile_centered, and_self]

/-- Both normalizations have exactly unit centered energy; positivity is proved internally. -/
theorem egbFixedChargeACriticalUnitModes_energy_one (n : ℕ) :
    egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalUnitSlow n) = 1 ∧
      egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalUnitFast n) = 1 := by
  have hs := egbFixedChargeACriticalSlowProfile_energy_pos n
  have hf := egbFixedChargeACriticalFastProfile_energy_pos n
  unfold egbFixedChargeACriticalUnitSlow egbFixedChargeACriticalUnitFast
  constructor
  · rw [egbFixedChargeACriticalCenteredEnergy_scale,
      inv_pow, Real.sq_sqrt hs.le, inv_mul_cancel₀ hs.ne']
  · rw [egbFixedChargeACriticalCenteredEnergy_scale,
      inv_pow, Real.sq_sqrt hf.le, inv_mul_cancel₀ hf.ne']

/-- Normalizing the two harmonics preserves exact orthogonality. -/
theorem egbFixedChargeACriticalUnitModes_orthogonal (n : ℕ) :
    ∑ i, egbFixedChargeACriticalUnitSlow n i * egbFixedChargeACriticalUnitFast n i = 0 := by
  let a := (Real.sqrt (egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalSlowProfile n)))⁻¹
  let b := (Real.sqrt (egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalFastProfile n)))⁻¹
  change (∑ i, (a * egbFixedChargeACriticalSlowProfile n i) * (b * egbFixedChargeACriticalFastProfile n i)) = 0
  calc
    _ = (a * b) * ∑ i, egbFixedChargeACriticalSlowProfile n i * egbFixedChargeACriticalFastProfile n i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [egbFixedChargeACriticalSlowFast_orthogonal, mul_zero]

/-- The unit slow mode evolves with the exact slow amplitude. -/
theorem egbFixedChargeACriticalUnitSlow_evolution (n m : ℕ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
      (egbFixedChargeACriticalUnitSlow n) =
      fun i => (2 / 3 : ℝ) ^ m * egbFixedChargeACriticalUnitSlow n i := by
  have h := egbFixedChargeACriticalMarkov_affine_action n m (egbFixedChargeACriticalSlowProfile n) 0
    (Real.sqrt (egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalSlowProfile n)))⁻¹
  simp only [zero_add, egbFixedChargeACriticalSlowProfile_evolution] at h
  unfold egbFixedChargeACriticalUnitSlow
  rw [h]
  funext i
  ring

/-- The unit fast mode evolves with the exact fast amplitude. -/
theorem egbFixedChargeACriticalUnitFast_evolution (n m : ℕ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
      (egbFixedChargeACriticalUnitFast n) =
      fun i => (1 / 6 : ℝ) ^ m * egbFixedChargeACriticalUnitFast n i := by
  have h := egbFixedChargeACriticalMarkov_affine_action n m (egbFixedChargeACriticalFastProfile n) 0
    (Real.sqrt (egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalFastProfile n)))⁻¹
  simp only [zero_add, egbFixedChargeACriticalFastProfile_evolution] at h
  unfold egbFixedChargeACriticalUnitFast
  rw [h]
  funext i
  ring

end
end GaloisForLFunctions.HTGeometry
