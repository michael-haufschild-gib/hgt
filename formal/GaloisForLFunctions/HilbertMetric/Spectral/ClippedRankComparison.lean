import GaloisForLFunctions.HilbertMetric.Spectral.ClippedThreshold

/-!
# Clipped energy refines rank–trace estimates

The affine rank penalty is bounded by the full clipped energy. This identifies
exactly which spectral information is discarded by a rank-only estimate.
-/

open Matrix Finset RiemannGaussian.HermitianRankTrace
open scoped NNReal
namespace GaloisForLFunctions.HilbertMetric.Clipped
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Clipped energy dominates the affine trace bound with one penalty per nonzero mode. -/
theorem rank_lower_bound {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) :
    (c : ℝ) * (trace A).re - (c : ℝ) ^ 2 / 4 * A.rank ≤ energy c A := by
  classical
  let s := Finset.univ.filter (fun i => hA.eigenvalues i ≠ 0)
  have hr : s.card = A.rank := by
    rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have ht : (trace A).re = ∑ i, hA.eigenvalues i := by
    simpa only [rtrace, RCLike.re_to_complex] using rtrace_eq_sum_eigenvalues hA
  have hp : ∀ i ∈ (univ : Finset ι),
      (c : ℝ) * hA.eigenvalues i - (if i ∈ s then (c : ℝ) ^ 2 / 4 else 0) ≤
        quadratic c (hA.eigenvalues i) := by
    intro i _
    by_cases hi : hA.eigenvalues i = 0
    · simp only [s, mem_filter, mem_univ, hi, ne_eq, not_true_eq_false,
        and_false, if_false, mul_zero, sub_zero]
      rw [quadratic_of_le c.coe_nonneg]
      simp
    · simp only [s, mem_filter, mem_univ, hi, ne_eq, not_false_eq_true,
        and_self, if_true]
      have hd := scalar_dual (show (c : ℝ) / 2 ≤ c by linarith only [c.coe_nonneg])
        (hA.eigenvalues i)
      nlinarith only [hd]
  have hs := sum_le_sum hp
  simp only [sum_sub_distrib, ← mul_sum, sum_ite_mem, univ_inter,
    sum_const, nsmul_eq_mul, hr] at hs
  rw [energy, spectralSum_eq hA, ht]
  nlinarith only [hs]

#print axioms rank_lower_bound

end
end GaloisForLFunctions.HilbertMetric.Clipped
