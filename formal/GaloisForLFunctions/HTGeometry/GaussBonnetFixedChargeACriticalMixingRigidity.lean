import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalMajorization

/-!
Exact rigidity of norm preservation for the critical Gibbs Markov kernel derived
from arXiv:2609.00025. Positive two-step transitions and positive diagonal entries
also resolve the single-step boundary: only constant profiles preserve their norm.
-/
namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem constant_profile_fixed (n m : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ)
    (hf : ∀ i, f i = f 0) :
    (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f = f := by
  funext i
  change (∑ j, ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).re * f j) = f i
  simp_rw [hf]
  rw [← Finset.sum_mul, egbFixedChargeACriticalMarkovMatrix_pow_row_sum, one_mul]

private theorem two_step_norm_preservation (n m : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) :
    (∑ i, (egbFixedChargeACriticalMarkovIteratedKernel n (m + 2)).toFinitePositiveKernel.applyReal f i ^ 2) =
      (∑ i, f i ^ 2) ↔ ∀ i, f i = f 0 := by
  constructor
  · intro he
    have h := (egbFixedChargeACriticalMarkov_sum_sq_eq_iff n (m + 2) f).mp he
    have hv (j : Fin (2 ^ (n + 3))) := (h 0 j).resolve_left
      (ne_of_gt (egbFixedChargeACriticalMarkovMatrix_two_step_pos n m 0 j))
    intro j
    exact (hv j).trans (hv 0).symm
  · intro hf
    rw [constant_profile_fixed n (m + 2) f hf]

/-- Every positive number of transitions preserves squared norm exactly for constant profiles. -/
theorem egbFixedChargeACriticalMarkov_norm_preserved_iff_constant
    (n m : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) :
    (∑ i, (egbFixedChargeACriticalMarkovIteratedKernel n (m + 1)).toFinitePositiveKernel.applyReal f i ^ 2) =
      (∑ i, f i ^ 2) ↔ ∀ i, f i = f 0 := by
  cases m with
  | zero =>
    constructor
    · intro he
      have h := (egbFixedChargeACriticalMarkov_sum_sq_eq_iff n 1 f).mp he
      have hd (i : Fin (2 ^ (n + 3))) :
          0 < ((egbFixedChargeACriticalMarkovMatrix n ^ 1) i i).re := by
        simp only [pow_one, egbFixedChargeACriticalMarkovMatrix, Matrix.of_apply,
          Complex.ofReal_re, egbFixedChargeACriticalMarkovWeight, sub_self,
          Real.cos_zero, one_pow, mul_one]
        positivity
      have hf : (egbFixedChargeACriticalMarkovIteratedKernel n 1).toFinitePositiveKernel.applyReal f = f := by
        funext i
        exact ((h i i).resolve_left (ne_of_gt (hd i))).symm
      have hff : (egbFixedChargeACriticalMarkovIteratedKernel n 2).toFinitePositiveKernel.applyReal f = f := by
        have ha := egbFixedChargeACriticalMarkovIteratedKernel_add n 1 1 f
        rw [ha, hf, hf]
      exact (two_step_norm_preservation n 0 f).mp (by rw [hff])
    · intro hf
      rw [constant_profile_fixed n 1 f hf]
  | succ m => exact two_step_norm_preservation n m f

/-- Every nonconstant profile loses a strictly positive amount of squared norm. -/
theorem egbFixedChargeACriticalMarkov_norm_strict_iff
    (n m : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) :
    (∑ i, (egbFixedChargeACriticalMarkovIteratedKernel n (m + 1)).toFinitePositiveKernel.applyReal f i ^ 2) <
      (∑ i, f i ^ 2) ↔ ¬ ∀ i, f i = f 0 := by
  constructor
  · intro h hf
    have he := (egbFixedChargeACriticalMarkov_norm_preserved_iff_constant n m f).mpr hf
    linarith
  · intro hf
    have hl := egbFixedChargeACriticalMarkov_sum_sq_le n (m + 1) f
    by_contra h
    have he := le_antisymm hl (le_of_not_gt h)
    exact hf ((egbFixedChargeACriticalMarkov_norm_preserved_iff_constant n m f).mp he)

/-- Constant profiles are the only fixed points of every positive-step evolution. -/
theorem egbFixedChargeACriticalMarkov_fixed_iff_constant
    (n m : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n (m + 1)).toFinitePositiveKernel.applyReal f = f ↔
      ∀ i, f i = f 0 := by
  constructor
  · intro hf
    exact (egbFixedChargeACriticalMarkov_norm_preserved_iff_constant n m f).mp (by rw [hf])
  · exact constant_profile_fixed n (m + 1) f

end

end GaloisForLFunctions.HTGeometry
