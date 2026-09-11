import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalHiddenEnergy
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalUnitModes

/-! # An internally normalized erased direction orthogonal to both surviving modes -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Normalize the existing hidden profile by its internally proved positive energy. -/
def egbFixedChargeACriticalUnitHidden (n : ℕ) : Fin (2 ^ (n + 3)) → ℝ :=
  fun i => (Real.sqrt (egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalHiddenProfile n)))⁻¹ *
    egbFixedChargeACriticalHiddenProfile n i

/-- Normalization preserves zero total mass. -/
theorem egbFixedChargeACriticalUnitHidden_mass_zero (n : ℕ) :
    ∑ i, egbFixedChargeACriticalUnitHidden n i = 0 := by
  simp only [egbFixedChargeACriticalUnitHidden, ← Finset.mul_sum,
    egbFixedChargeACriticalHiddenProfile_mass_zero, mul_zero]

/-- The normalized hidden direction is already centered. -/
theorem egbFixedChargeACriticalUnitHidden_centered (n : ℕ) :
    egbFixedChargeACriticalCenteredProfile n (egbFixedChargeACriticalUnitHidden n) =
      egbFixedChargeACriticalUnitHidden n := by
  unfold egbFixedChargeACriticalUnitHidden
  rw [egbFixedChargeACriticalCenteredProfile_scale, egbFixedChargeACriticalHiddenProfile_centered]

/-- The erased direction has exact unit energy on every grid. -/
theorem egbFixedChargeACriticalUnitHidden_energy_one (n : ℕ) :
    egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalUnitHidden n) = 1 := by
  have h := egbFixedChargeACriticalHiddenProfile_energy_pos n
  unfold egbFixedChargeACriticalUnitHidden
  rw [egbFixedChargeACriticalCenteredEnergy_scale, inv_pow, Real.sq_sqrt h.le, inv_mul_cancel₀ h.ne']

/-- The unit hidden mode retains the exact zero-rate evolution, including the initial identity step. -/
theorem egbFixedChargeACriticalUnitHidden_evolution (n m : ℕ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
      (egbFixedChargeACriticalUnitHidden n) =
        fun i => (0 : ℝ) ^ m * egbFixedChargeACriticalUnitHidden n i := by
  have h := egbFixedChargeACriticalMarkov_affine_action n m (egbFixedChargeACriticalHiddenProfile n) 0
    (Real.sqrt (egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalHiddenProfile n)))⁻¹
  simp only [zero_add, egbFixedChargeACriticalHiddenProfile_evolution] at h
  unfold egbFixedChargeACriticalUnitHidden
  rw [h]
  funext i
  ring

/-- Kernel symmetry forces the erased direction to be orthogonal to both surviving unit modes. -/
theorem egbFixedChargeACriticalUnitHidden_orthogonal (n : ℕ) :
    (∑ i, egbFixedChargeACriticalUnitHidden n i * egbFixedChargeACriticalUnitSlow n i) = 0 ∧
      (∑ i, egbFixedChargeACriticalUnitHidden n i * egbFixedChargeACriticalUnitFast n i) = 0 := by
  constructor
  · have h := egbFixedChargeACriticalMarkov_pairing_symm n 1
      (egbFixedChargeACriticalUnitHidden n) (egbFixedChargeACriticalUnitSlow n)
    rw [egbFixedChargeACriticalUnitHidden_evolution, egbFixedChargeACriticalUnitSlow_evolution] at h
    simp [pow_one] at h
    have he : (2 / 3 : ℝ) * (∑ i, egbFixedChargeACriticalUnitHidden n i * egbFixedChargeACriticalUnitSlow n i) = 0 := by
      calc
        _ = ∑ i, egbFixedChargeACriticalUnitHidden n i * ((2 / 3 : ℝ) * egbFixedChargeACriticalUnitSlow n i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = 0 := by simpa only [one_div] using h
    linarith
  · have h := egbFixedChargeACriticalMarkov_pairing_symm n 1
      (egbFixedChargeACriticalUnitHidden n) (egbFixedChargeACriticalUnitFast n)
    rw [egbFixedChargeACriticalUnitHidden_evolution, egbFixedChargeACriticalUnitFast_evolution] at h
    simp [pow_one] at h
    have he : (1 / 6 : ℝ) * (∑ i, egbFixedChargeACriticalUnitHidden n i * egbFixedChargeACriticalUnitFast n i) = 0 := by
      calc
        _ = ∑ i, egbFixedChargeACriticalUnitHidden n i * ((1 / 6 : ℝ) * egbFixedChargeACriticalUnitFast n i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = 0 := by simpa only [one_div] using h
    linarith

end
end GaloisForLFunctions.HTGeometry
