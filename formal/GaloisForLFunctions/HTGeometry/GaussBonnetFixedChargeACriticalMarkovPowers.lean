import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalMarkovEigenmodes

/-!
Every iterate of the critical Gibbs transition is packaged as the corpus's finite
Markov kernel. This exposes the exact QFT mixing family to probability and
information-processing interfaces without requiring positivity or mass hypotheses.
-/
namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every real transition probability remains nonnegative under repeated steps. -/
theorem egbFixedChargeACriticalMarkovMatrix_pow_nonneg
    (n m : ℕ) (i j : Fin (2 ^ (n + 3))) :
    0 ≤ ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).re := by
  induction m generalizing i j with
  | zero =>
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply, Complex.re_sum]
    apply Finset.sum_nonneg
    intro k _
    simp only [Complex.mul_re, egbFixedChargeACriticalMarkovMatrix, Matrix.of_apply,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg (ih i k) (egbFixedChargeACriticalMarkovWeight_nonneg n k j)

/-- Symmetry is preserved by every number of transitions. -/
theorem egbFixedChargeACriticalMarkovMatrix_pow_symm
    (n m : ℕ) (i j : Fin (2 ^ (n + 3))) :
    (egbFixedChargeACriticalMarkovMatrix n ^ m) i j =
      (egbFixedChargeACriticalMarkovMatrix n ^ m) j i := by
  have h : (egbFixedChargeACriticalMarkovMatrix n).transpose =
      egbFixedChargeACriticalMarkovMatrix n := by
    ext i j
    change (egbFixedChargeACriticalMarkovWeight n j i : ℂ) =
      (egbFixedChargeACriticalMarkovWeight n i j : ℂ)
    rw [egbFixedChargeACriticalMarkovWeight_symm]
  have hp : (egbFixedChargeACriticalMarkovMatrix n ^ m).transpose =
      egbFixedChargeACriticalMarkovMatrix n ^ m := by
    rw [Matrix.transpose_pow, h]
  exact (congrArg (fun M => M i j) hp).symm

/-- Every iterated transition has unit real row mass. -/
theorem egbFixedChargeACriticalMarkovMatrix_pow_row_sum
    (n m : ℕ) (i : Fin (2 ^ (n + 3))) :
    ∑ j : Fin (2 ^ (n + 3)), ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).re = 1 := by
  have hs := egbFixedChargeAQFTMultiplier_row_sum (n + 3)
    (fun j => egbFixedChargeAFiveModeSpectrum n egbFixedChargeACriticalMarkovEigenvalues j ^ m) i
  rw [← egbFixedChargeAQFTMultiplier_pow, ← egbFixedChargeACriticalMarkovMatrix_QFT] at hs
  have h0 : egbFixedChargeAFiveModeSpectrum n egbFixedChargeACriticalMarkovEigenvalues 0 = 1 := by
    simpa [egbFixedChargeAFiveFourierModes, egbFixedChargeACriticalMarkovEigenvalues] using
      egbFixedChargeAFiveModeSpectrum_mode n egbFixedChargeACriticalMarkovEigenvalues 0
  rw [h0, one_pow] at hs
  have hr := congrArg Complex.re hs
  simpa only [Complex.re_sum, Complex.one_re] using hr

/-- Every iterated transition has unit real column mass. -/
theorem egbFixedChargeACriticalMarkovMatrix_pow_column_sum
    (n m : ℕ) (j : Fin (2 ^ (n + 3))) :
    ∑ i : Fin (2 ^ (n + 3)), ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).re = 1 := by
  simp_rw [egbFixedChargeACriticalMarkovMatrix_pow_symm n m _ j]
  exact egbFixedChargeACriticalMarkovMatrix_pow_row_sum n m j

/-- Any number of critical Gibbs transitions as an existing corpus Markov kernel. -/
def egbFixedChargeACriticalMarkovIteratedKernel (n m : ℕ) :
    FiniteMarkovKernel (Fin (2 ^ (n + 3))) (Fin (2 ^ (n + 3))) where
  weight i j := ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).re
  nonneg := egbFixedChargeACriticalMarkovMatrix_pow_nonneg n m
  column_sum := egbFixedChargeACriticalMarkovMatrix_pow_column_sum n m

/-- The real transition weights obey the exact one-step composition law. -/
theorem egbFixedChargeACriticalMarkovMatrix_pow_step
    (n m : ℕ) (i j : Fin (2 ^ (n + 3))) :
    ((egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) i j).re =
      ∑ k : Fin (2 ^ (n + 3)), egbFixedChargeACriticalMarkovWeight n i k *
        ((egbFixedChargeACriticalMarkovMatrix n ^ m) k j).re := by
  rw [pow_succ', Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Complex.mul_re, egbFixedChargeACriticalMarkovMatrix, Matrix.of_apply,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The packaged iterates are literal repeated applications of the original real Markov kernel. -/
theorem egbFixedChargeACriticalMarkovIteratedKernel_step
    (n m : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n (m + 1)).toFinitePositiveKernel.applyReal f =
      (egbFixedChargeACriticalMarkovKernel n).toFinitePositiveKernel.applyReal
        ((egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f) := by
  funext i
  change (∑ j, ((egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) i j).re * f j) =
    ∑ k, egbFixedChargeACriticalMarkovWeight n i k *
      ∑ j, ((egbFixedChargeACriticalMarkovMatrix n ^ m) k j).re * f j
  simp only [egbFixedChargeACriticalMarkovMatrix_pow_step, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

end

end GaloisForLFunctions.HTGeometry
