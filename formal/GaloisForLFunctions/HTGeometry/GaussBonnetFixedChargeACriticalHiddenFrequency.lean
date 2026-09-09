import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalFourierNullspace

namespace GaloisForLFunctions.HTGeometry

open QuantumAlg
open scoped Matrix
noncomputable section

private theorem grid_size_bound (n : ℕ) : 8 ≤ 2 ^ (n + 3) := by
  have hp : 0 < (2 : ℕ) ^ n := pow_pos (by omega) n
  rw [pow_add]
  norm_num
  omega

/-- The third positive frequency is absent on every grid in the critical family. -/
def egbFixedChargeACriticalHiddenFrequency (n : ℕ) : Fin (2 ^ (n + 3)) :=
  ⟨3, by have := grid_size_bound n; omega⟩

/-- This frequency never aliases with any of the five retained modes. -/
theorem egbFixedChargeACriticalHiddenFrequency_missing (n : ℕ) :
    ¬ ∃ k : Fin 5,
      egbFixedChargeACriticalHiddenFrequency n = egbFixedChargeAFiveFourierModes n k := by
  rintro ⟨k, hk⟩
  have hv := congrArg Fin.val hk
  have hb := grid_size_bound n
  fin_cases k <;> norm_num [egbFixedChargeACriticalHiddenFrequency,
    egbFixedChargeAFiveFourierModes] at hv <;> omega

/-- A concrete nonzero input in the Fourier nullspace. -/
def egbFixedChargeACriticalHiddenFourierMode (n : ℕ) : Fin (2 ^ (n + 3)) → ℂ :=
  fun i => QFTMatrix (n + 3) i (egbFixedChargeACriticalHiddenFrequency n)

/-- The hidden input is nonzero before any transition occurs. -/
theorem egbFixedChargeACriticalHiddenFourierMode_ne_zero (n : ℕ) :
    egbFixedChargeACriticalHiddenFourierMode n ≠ 0 :=
  egbFixedChargeACriticalMarkovMatrix_frequency_ne_zero n _

/-- Every positive number of transitions erases the hidden input exactly. -/
theorem egbFixedChargeACriticalHiddenFourierMode_erased (n m : ℕ) :
    (egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) *ᵥ
      egbFixedChargeACriticalHiddenFourierMode n = 0 := by
  unfold egbFixedChargeACriticalHiddenFourierMode
  rw [egbFixedChargeACriticalMarkovMatrix_frequency_action]
  have hz := (egbFixedChargeACriticalMarkovSpectrum_zero_iff n
    (egbFixedChargeACriticalHiddenFrequency n)).mpr
      (egbFixedChargeACriticalHiddenFrequency_missing n)
  funext i
  simp [hz]

/-- Taking real coordinates commutes with every transition power. -/
theorem egbFixedChargeACriticalMarkov_real_action (n m : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℂ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
      (fun i => (f i).re) = fun i =>
        (((egbFixedChargeACriticalMarkovMatrix n ^ m) *ᵥ f) i).re := by
  funext i
  change (∑ j, ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).re * (f j).re) =
    (∑ j, (egbFixedChargeACriticalMarkovMatrix n ^ m) i j * f j).re
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.mul_re, egbFixedChargeACriticalMarkovMatrix_pow_im_zero]
  ring

end
end GaloisForLFunctions.HTGeometry
