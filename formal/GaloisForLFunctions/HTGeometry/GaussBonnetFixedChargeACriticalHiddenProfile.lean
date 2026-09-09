import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalHiddenFrequency

namespace GaloisForLFunctions.HTGeometry

open QuantumAlg
noncomputable section

/-- A real signed profile in the exact nullspace of the critical transition. -/
def egbFixedChargeACriticalHiddenProfile (n : ℕ) : Fin (2 ^ (n + 3)) → ℝ :=
  fun i => (egbFixedChargeACriticalHiddenFourierMode n i).re

/-- The real hidden mode also vanishes after every positive number of transitions. -/
theorem egbFixedChargeACriticalHiddenProfile_erased (n m : ℕ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n (m + 1)).toFinitePositiveKernel.applyReal
      (egbFixedChargeACriticalHiddenProfile n) = 0 := by
  unfold egbFixedChargeACriticalHiddenProfile
  rw [egbFixedChargeACriticalMarkov_real_action,
    egbFixedChargeACriticalHiddenFourierMode_erased]
  rfl

/-- The hidden real profile has zero total mass, as required for a probability perturbation. -/
theorem egbFixedChargeACriticalHiddenProfile_mass_zero (n : ℕ) :
    ∑ i, egbFixedChargeACriticalHiddenProfile n i = 0 := by
  calc
    _ = ∑ i, (egbFixedChargeACriticalMarkovIteratedKernel n 1).toFinitePositiveKernel.applyReal
        (egbFixedChargeACriticalHiddenProfile n) i :=
      (FiniteMarkovKernel.sum_applyReal _ _).symm
    _ = 0 := by rw [egbFixedChargeACriticalHiddenProfile_erased n 0]; simp

/-- A positive first coordinate witnesses that the real perturbation is nontrivial. -/
theorem egbFixedChargeACriticalHiddenProfile_first_pos (n : ℕ) :
    0 < egbFixedChargeACriticalHiddenProfile n 0 := by
  simp only [egbFixedChargeACriticalHiddenProfile, egbFixedChargeACriticalHiddenFourierMode,
    QFT_entry, Fin.val_zero, Nat.zero_mul, pow_zero, mul_one, invSqrtN,
    ← Complex.ofReal_inv, Complex.ofReal_re]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (pow_pos (by norm_num) _))

/-- The real null profile is a nonzero vector. -/
theorem egbFixedChargeACriticalHiddenProfile_ne_zero (n : ℕ) :
    egbFixedChargeACriticalHiddenProfile n ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have hp := egbFixedChargeACriticalHiddenProfile_first_pos n
  change egbFixedChargeACriticalHiddenProfile n 0 = 0 at h0
  linarith

end
end GaloisForLFunctions.HTGeometry
