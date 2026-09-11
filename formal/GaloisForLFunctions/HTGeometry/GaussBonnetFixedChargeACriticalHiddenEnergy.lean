import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalHiddenProfile
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalCenteredEnergy

/-! # Positive energy of the exact erased real mode -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The already constructed hidden profile has exactly zero invariant mean. -/
theorem egbFixedChargeACriticalHiddenProfile_centered (n : ℕ) :
    egbFixedChargeACriticalCenteredProfile n (egbFixedChargeACriticalHiddenProfile n) =
      egbFixedChargeACriticalHiddenProfile n := by
  funext i
  change egbFixedChargeACriticalHiddenProfile n i -
    egbFixedChargeACriticalRealMean n (egbFixedChargeACriticalHiddenProfile n) = _
  rw [egbFixedChargeACriticalRealMean, egbFixedChargeACriticalHiddenProfile_mass_zero, mul_zero, sub_zero]

/-- The erased mode carries strictly positive initial energy. -/
theorem egbFixedChargeACriticalHiddenProfile_energy_pos (n : ℕ) :
    0 < egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalHiddenProfile n) := by
  unfold egbFixedChargeACriticalCenteredEnergy
  rw [egbFixedChargeACriticalHiddenProfile_centered]
  have h := Finset.single_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin (2 ^ (n + 3))))) =>
      sq_nonneg (egbFixedChargeACriticalHiddenProfile n i)) (Finset.mem_univ 0)
  nlinarith [egbFixedChargeACriticalHiddenProfile_first_pos n]

/-- The zero-rate power describes the hidden mode at time zero and every positive time in one exact identity. -/
theorem egbFixedChargeACriticalHiddenProfile_evolution (n m : ℕ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
      (egbFixedChargeACriticalHiddenProfile n) =
        fun i => (0 : ℝ) ^ m * egbFixedChargeACriticalHiddenProfile n i := by
  cases m with
  | zero => simp only [egbFixedChargeACriticalMarkovIteratedKernel_zero, pow_zero, one_mul]
  | succ m =>
      rw [egbFixedChargeACriticalHiddenProfile_erased n m]
      funext i
      simp

end
end GaloisForLFunctions.HTGeometry
