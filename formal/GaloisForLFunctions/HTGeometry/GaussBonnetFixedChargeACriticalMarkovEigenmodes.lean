import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalMarkovMixing

/-!
Exact nonzero eigenmodes of the critical Gibbs Markov chain from arXiv:2609.00025.
The slow mode realizes the rate 2/3, so the geometric mixing bound records a real
spectral obstruction to faster exponential relaxation.
-/
namespace GaloisForLFunctions.HTGeometry

open QuantumAlg
open scoped Matrix

noncomputable section

/-- Each chosen QFT column is an exact eigenmode for every number of transitions. -/
theorem egbFixedChargeACriticalMarkovMatrix_eigenmode
    (n m : ℕ) (k : Fin 5) :
    (egbFixedChargeACriticalMarkovMatrix n ^ m) *ᵥ
      (fun i => QFTMatrix (n + 3) i (egbFixedChargeAFiveFourierModes n k)) =
        fun i => (egbFixedChargeACriticalMarkovEigenvalues k : ℂ) ^ m *
          QFTMatrix (n + 3) i (egbFixedChargeAFiveFourierModes n k) := by
  rw [egbFixedChargeACriticalMarkovMatrix_QFT, egbFixedChargeAQFTMultiplier_pow]
  funext i
  have h := congrArg
    (fun M : Matrix (Fin (2 ^ (n + 3))) (Fin (2 ^ (n + 3))) ℂ =>
      M i (egbFixedChargeAFiveFourierModes n k))
    (egbFixedChargeAQFTMultiplier_intertwine (n + 3)
      (fun j => egbFixedChargeAFiveModeSpectrum n egbFixedChargeACriticalMarkovEigenvalues j ^ m))
  change _ = (QFTMatrix (n + 3) * Matrix.diagonal
    (fun j => egbFixedChargeAFiveModeSpectrum n egbFixedChargeACriticalMarkovEigenvalues j ^ m))
      i (egbFixedChargeAFiveFourierModes n k) at h
  rw [Matrix.mul_apply, Matrix.mul_diagonal, egbFixedChargeAFiveModeSpectrum_mode] at h
  exact h.trans (mul_comm _ _)

/-- Every chosen Fourier eigenmode is a nonzero source profile. -/
theorem egbFixedChargeACriticalMarkovMatrix_eigenmode_ne_zero
    (n : ℕ) (k : Fin 5) :
    (fun i : Fin (2 ^ (n + 3)) =>
      QFTMatrix (n + 3) i (egbFixedChargeAFiveFourierModes n k)) ≠ 0 := by
  intro h
  have hv := congrFun h 0
  have hn : invSqrtN (n + 3) ≠ 0 := by
    unfold invSqrtN
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt
      (Real.sqrt_pos.mpr (pow_pos (by norm_num) _))))
  apply hn
  simpa only [QFT_entry, Fin.val_zero, Nat.zero_mul, pow_zero, mul_one, Pi.zero_apply] using hv

/-- The first harmonic realizes exactly the slow rate 2/3 at every step. -/
theorem egbFixedChargeACriticalMarkovMatrix_slow_mode
    (n m : ℕ) :
    (egbFixedChargeACriticalMarkovMatrix n ^ m) *ᵥ
      (fun i => QFTMatrix (n + 3) i (egbFixedChargeAFiveFourierModes n 1)) =
        fun i => (2 / 3 : ℂ) ^ m * QFTMatrix (n + 3) i (egbFixedChargeAFiveFourierModes n 1) := by
  simpa [egbFixedChargeACriticalMarkovEigenvalues] using
    egbFixedChargeACriticalMarkovMatrix_eigenmode n m 1

/-- The second harmonic realizes the faster rate 1/6 at every step. -/
theorem egbFixedChargeACriticalMarkovMatrix_fast_mode
    (n m : ℕ) :
    (egbFixedChargeACriticalMarkovMatrix n ^ m) *ᵥ
      (fun i => QFTMatrix (n + 3) i (egbFixedChargeAFiveFourierModes n 2)) =
        fun i => (1 / 6 : ℂ) ^ m * QFTMatrix (n + 3) i (egbFixedChargeAFiveFourierModes n 2) := by
  simpa [egbFixedChargeACriticalMarkovEigenvalues] using
    egbFixedChargeACriticalMarkovMatrix_eigenmode n m 2

end

end GaloisForLFunctions.HTGeometry
