import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalSpectralGap

namespace GaloisForLFunctions.HTGeometry

open QuantumAlg
noncomputable section

/-- The real first Fourier harmonic witnesses the slow nonconstant relaxation mode. -/
def egbFixedChargeACriticalSlowProfile (n : ℕ) : Fin (2 ^ (n + 3)) → ℝ :=
  fun i => (QFTMatrix (n + 3) i (egbFixedChargeAFiveFourierModes n 1)).re

/-- The real first harmonic decays by exactly two thirds at every transition. -/
theorem egbFixedChargeACriticalSlowProfile_evolution (n m : ℕ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
      (egbFixedChargeACriticalSlowProfile n) =
        fun i => (2 / 3 : ℝ) ^ m * egbFixedChargeACriticalSlowProfile n i := by
  have h := egbFixedChargeACriticalMarkov_real_action n m
    (fun i => QFTMatrix (n + 3) i (egbFixedChargeAFiveFourierModes n 1))
  rw [egbFixedChargeACriticalMarkovMatrix_slow_mode] at h
  change (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
    (egbFixedChargeACriticalSlowProfile n) = _ at h
  rw [h]
  funext i
  have hc : (2 / 3 : ℂ) ^ m = (((2 / 3 : ℝ) ^ m : ℝ) : ℂ) := by
    norm_num [Complex.ofReal_pow, Complex.ofReal_div]
  rw [hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

/-- The slow mode has zero total mass. -/
theorem egbFixedChargeACriticalSlowProfile_mass_zero (n : ℕ) :
    ∑ i, egbFixedChargeACriticalSlowProfile n i = 0 := by
  have h := FiniteMarkovKernel.sum_applyReal
    (egbFixedChargeACriticalMarkovIteratedKernel n 1) (egbFixedChargeACriticalSlowProfile n)
  rw [egbFixedChargeACriticalSlowProfile_evolution n 1] at h
  simp only [pow_one, ← Finset.mul_sum] at h
  linarith

/-- The slow real mode has a positive coordinate and is therefore nonzero. -/
theorem egbFixedChargeACriticalSlowProfile_first_pos (n : ℕ) :
    0 < egbFixedChargeACriticalSlowProfile n 0 := by
  simp only [egbFixedChargeACriticalSlowProfile, QFT_entry, Fin.val_zero, Nat.zero_mul,
    pow_zero, mul_one, invSqrtN, ← Complex.ofReal_inv, Complex.ofReal_re]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (pow_pos (by norm_num) _))

/-- Removing the invariant mean leaves the slow mode unchanged. -/
theorem egbFixedChargeACriticalSlowProfile_centered (n : ℕ) :
    egbFixedChargeACriticalCenteredProfile n (egbFixedChargeACriticalSlowProfile n) =
      egbFixedChargeACriticalSlowProfile n := by
  funext i
  change egbFixedChargeACriticalSlowProfile n i -
    egbFixedChargeACriticalRealMean n (egbFixedChargeACriticalSlowProfile n) = _
  rw [egbFixedChargeACriticalRealMean, egbFixedChargeACriticalSlowProfile_mass_zero,
    mul_zero, sub_zero]

/-- The slow profile carries strictly positive centered energy. -/
theorem egbFixedChargeACriticalSlowProfile_energy_pos (n : ℕ) :
    0 < egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalSlowProfile n) := by
  unfold egbFixedChargeACriticalCenteredEnergy
  rw [egbFixedChargeACriticalSlowProfile_centered]
  have h := Finset.single_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin (2 ^ (n + 3))))) =>
      sq_nonneg (egbFixedChargeACriticalSlowProfile n i)) (Finset.mem_univ 0)
  nlinarith [egbFixedChargeACriticalSlowProfile_first_pos n]

/-- The slow profile realizes the four-ninths energy decay exactly at every time. -/
theorem egbFixedChargeACriticalSlowProfile_energy_exact (n m : ℕ) :
    egbFixedChargeACriticalCenteredEnergy n
      ((egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
        (egbFixedChargeACriticalSlowProfile n)) =
          (4 / 9 : ℝ) ^ m * egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalSlowProfile n) := by
  rw [egbFixedChargeACriticalSlowProfile_evolution, egbFixedChargeACriticalCenteredEnergy_scale]
  have hp : ((2 / 3 : ℝ) ^ m) ^ (2 : ℕ) = (4 / 9 : ℝ) ^ m := by
    rw [pow_two, ← mul_pow]
    norm_num
  rw [hp]

end
end GaloisForLFunctions.HTGeometry
