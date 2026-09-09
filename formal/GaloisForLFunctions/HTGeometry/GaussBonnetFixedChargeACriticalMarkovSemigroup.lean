import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalMarkovRefresh

/-!
The packaged critical Gibbs Markov kernels form a literal semigroup on real
profiles. This connects their QFT powers to the corpus information-processing API.
-/
namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Zero transitions act as the identity on every real profile. -/
theorem egbFixedChargeACriticalMarkovIteratedKernel_zero
    (n : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n 0).toFinitePositiveKernel.applyReal f = f := by
  funext i
  change (∑ j, ((egbFixedChargeACriticalMarkovMatrix n ^ 0) i j).re * f j) = f i
  simp [Matrix.one_apply, apply_ite]

/-- One transition is the original critical Gibbs Markov action. -/
theorem egbFixedChargeACriticalMarkovIteratedKernel_one
    (n : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n 1).toFinitePositiveKernel.applyReal f =
      (egbFixedChargeACriticalMarkovKernel n).toFinitePositiveKernel.applyReal f := by
  funext i
  change (∑ j, ((egbFixedChargeACriticalMarkovMatrix n ^ 1) i j).re * f j) = _
  simp only [pow_one, egbFixedChargeACriticalMarkovMatrix, Matrix.of_apply, Complex.ofReal_re]
  rfl

/-- Arbitrary groups of transitions compose by adding their step counts. -/
theorem egbFixedChargeACriticalMarkovIteratedKernel_add
    (n a b : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n (a + b)).toFinitePositiveKernel.applyReal f =
      (egbFixedChargeACriticalMarkovIteratedKernel n a).toFinitePositiveKernel.applyReal
        ((egbFixedChargeACriticalMarkovIteratedKernel n b).toFinitePositiveKernel.applyReal f) := by
  funext i
  change (∑ j, ((egbFixedChargeACriticalMarkovMatrix n ^ (a + b)) i j).re * f j) =
    ∑ k, ((egbFixedChargeACriticalMarkovMatrix n ^ a) i k).re *
      ∑ j, ((egbFixedChargeACriticalMarkovMatrix n ^ b) k j).re * f j
  rw [pow_add (egbFixedChargeACriticalMarkovMatrix n) a b]
  simp only [Matrix.mul_apply, Complex.re_sum, Complex.mul_re,
    egbFixedChargeACriticalMarkovMatrix_pow_im_zero, mul_zero, sub_zero,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

end

end GaloisForLFunctions.HTGeometry
