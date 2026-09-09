import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalBistochastic

/-!
Majorization, permutation mixtures, and exact variance loss for the critical Gibbs
kernel derived from arXiv:2609.00025, applied to existing corpus statistics.
-/
namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every critical Gibbs transition is a convex mixture of input relabelings. -/
theorem egbFixedChargeACriticalMarkov_permutation_decomposition
    (n m : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) :
    ∃ w : Equiv.Perm (Fin (2 ^ (n + 3))) → ℝ,
      (∀ e, 0 ≤ w e) ∧ (∑ e, w e) = 1 ∧
        (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f =
          ∑ e, w e • (f ∘ e) := by
  simpa only [egbFixedChargeACriticalBistochastic_action] using
    bistochasticMixing_permutation_decomposition (egbFixedChargeACriticalBistochastic n m) f

/-- Every largest-entry partial sum decreases under every number of critical Gibbs transitions. -/
theorem egbFixedChargeACriticalMarkov_topSum_le
    (n m : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) (k : Fin (2 ^ (n + 3) + 1)) :
    topSum k.val ((egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f) ≤
      topSum k.val f := by
  simpa only [egbFixedChargeACriticalBistochastic_action] using
    bistochasticMixing_topSum_le (egbFixedChargeACriticalBistochastic n m) f k

/-- Total squared-norm loss is exactly the transition-weighted conditional variance. -/
theorem egbFixedChargeACriticalMarkov_variance_identity
    (n m : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) :
    (∑ i, f i ^ 2) - (∑ i,
      (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f i ^ 2) =
        ∑ i, ∑ j, ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).re *
          (f j - (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f i) ^ 2 := by
  have h := bistochasticMixing_variance_identity (egbFixedChargeACriticalBistochastic n m) f
  rw [egbFixedChargeACriticalBistochastic_action] at h
  exact h

/-- The critical Markov action cannot increase the squared norm of any real profile. -/
theorem egbFixedChargeACriticalMarkov_sum_sq_le
    (n m : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) :
    (∑ i, (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f i ^ 2) ≤
      ∑ i, f i ^ 2 := by
  simpa only [egbFixedChargeACriticalBistochastic_action] using
    bistochasticMixing_sum_sq_le (egbFixedChargeACriticalBistochastic n m) f

/-- Norm preservation is exactly constancy along every occupied transition edge. -/
theorem egbFixedChargeACriticalMarkov_sum_sq_eq_iff
    (n m : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) :
    (∑ i, (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f i ^ 2) =
      (∑ i, f i ^ 2) ↔
        ∀ i j : Fin (2 ^ (n + 3)), ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).re = 0 ∨
          f j = (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f i := by
  have h := bistochasticMixing_sum_sq_eq_iff (egbFixedChargeACriticalBistochastic n m) f
  rw [egbFixedChargeACriticalBistochastic_action] at h
  exact h

/-- Total variation between arbitrary real mass profiles contracts under the same evolution. -/
theorem egbFixedChargeACriticalMarkov_totalVariation_le
    (n m : ℕ) (f g : Fin (2 ^ (n + 3)) → ℝ) :
    (∑ i, |(egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f i -
      (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal g i|) ≤
        ∑ i, |f i - g i| := by
  simpa only [egbFixedChargeACriticalBistochastic_action] using
    bistochasticMixing_abs_sub_sum_le (egbFixedChargeACriticalBistochastic n m) f g

end

end GaloisForLFunctions.HTGeometry
