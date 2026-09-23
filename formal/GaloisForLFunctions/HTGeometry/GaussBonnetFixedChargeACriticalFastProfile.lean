import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalSlowProfile

namespace GaloisForLFunctions.HTGeometry

open QuantumAlg
noncomputable section

/-- The real second Fourier harmonic witnesses the fast nonconstant relaxation mode. -/
def egbFixedChargeACriticalFastProfile (n : ℕ) : Fin (2 ^ (n + 3)) → ℝ :=
  fun i => (QFTMatrix (n + 3) i (egbFixedChargeAFiveFourierModes n 2)).re

/-- The real second harmonic decays by exactly one sixth at every transition. -/
theorem egbFixedChargeACriticalFastProfile_evolution (n m : ℕ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
      (egbFixedChargeACriticalFastProfile n) =
        fun i => (1 / 6 : ℝ) ^ m * egbFixedChargeACriticalFastProfile n i := by
  have h := egbFixedChargeACriticalMarkov_real_action n m
    (fun i => QFTMatrix (n + 3) i (egbFixedChargeAFiveFourierModes n 2))
  rw [egbFixedChargeACriticalMarkovMatrix_fast_mode] at h
  change (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
    (egbFixedChargeACriticalFastProfile n) = _ at h
  rw [h]
  funext i
  have hc : (1 / 6 : ℂ) ^ m = (((1 / 6 : ℝ) ^ m : ℝ) : ℂ) := by
    norm_num [Complex.ofReal_pow, Complex.ofReal_div]
  rw [hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

/-- The fast mode has zero total mass. -/
theorem egbFixedChargeACriticalFastProfile_mass_zero (n : ℕ) :
    ∑ i, egbFixedChargeACriticalFastProfile n i = 0 := by
  have h := FiniteMarkovKernel.sum_applyReal
    (egbFixedChargeACriticalMarkovIteratedKernel n 1) (egbFixedChargeACriticalFastProfile n)
  rw [egbFixedChargeACriticalFastProfile_evolution n 1] at h
  simp only [pow_one, ← Finset.mul_sum] at h
  linarith

/-- The fast real mode has a positive coordinate and is therefore nonzero. -/
theorem egbFixedChargeACriticalFastProfile_first_pos (n : ℕ) :
    0 < egbFixedChargeACriticalFastProfile n 0 := by
  simp only [egbFixedChargeACriticalFastProfile, QFT_entry, Fin.val_zero, Nat.zero_mul,
    pow_zero, mul_one, invSqrtN, ← Complex.ofReal_inv, Complex.ofReal_re]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (pow_pos (by norm_num) _))

/-- Removing the invariant mean leaves the fast mode unchanged. -/
theorem egbFixedChargeACriticalFastProfile_centered (n : ℕ) :
    egbFixedChargeACriticalCenteredProfile n (egbFixedChargeACriticalFastProfile n) =
      egbFixedChargeACriticalFastProfile n := by
  funext i
  change egbFixedChargeACriticalFastProfile n i -
    egbFixedChargeACriticalRealMean n (egbFixedChargeACriticalFastProfile n) = _
  rw [egbFixedChargeACriticalRealMean, egbFixedChargeACriticalFastProfile_mass_zero,
    mul_zero, sub_zero]

/-- The fast profile carries strictly positive centered energy. -/
theorem egbFixedChargeACriticalFastProfile_energy_pos (n : ℕ) :
    0 < egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalFastProfile n) := by
  unfold egbFixedChargeACriticalCenteredEnergy
  rw [egbFixedChargeACriticalFastProfile_centered]
  have h := Finset.single_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin (2 ^ (n + 3))))) =>
      sq_nonneg (egbFixedChargeACriticalFastProfile n i)) (Finset.mem_univ 0)
  nlinarith [egbFixedChargeACriticalFastProfile_first_pos n]

/-- The fast profile realizes the one-thirty-sixth energy decay exactly at every time. -/
theorem egbFixedChargeACriticalFastProfile_energy_exact (n m : ℕ) :
    egbFixedChargeACriticalCenteredEnergy n
      ((egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
        (egbFixedChargeACriticalFastProfile n)) =
          (1 / 36 : ℝ) ^ m * egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeACriticalFastProfile n) := by
  rw [egbFixedChargeACriticalFastProfile_evolution, egbFixedChargeACriticalCenteredEnergy_scale]
  have hp : ((1 / 6 : ℝ) ^ m) ^ (2 : ℕ) = (1 / 36 : ℝ) ^ m := by
    rw [pow_two, ← mul_pow]
    norm_num
  rw [hp]

end
end GaloisForLFunctions.HTGeometry
