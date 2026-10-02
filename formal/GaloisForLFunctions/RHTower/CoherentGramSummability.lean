import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

noncomputable section
open scoped BigOperators
namespace RHTower

/-- Full finite Gram control, with all off-diagonal terms retained. -/
theorem norm_sum_sq_le_sum_norm_inner {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : ι → E) (s : Finset ι) :
    ‖∑ i ∈ s, f i‖^2 ≤ ∑ ij ∈ s ×ˢ s, ‖inner ℂ (f ij.1) (f ij.2)‖ := by
  calc
    _ = ‖inner ℂ (∑ i ∈ s, f i) (∑ j ∈ s, f j)‖ := by
      rw [inner_self_eq_norm_sq_to_K]
      change ‖∑ i ∈ s, f i‖^2 = ‖(‖∑ i ∈ s, f i‖ : ℂ)^2‖
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖inner ℂ (f i) (f j)‖ := by
      rw [sum_inner]
      simp_rw [inner_sum]
      exact (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ = _ := (Finset.sum_product s s (fun ij : ι × ι => ‖inner ℂ (f ij.1) (f ij.2)‖)).symm

/-- Absolute summability of the complete Gram matrix gives an unconditional
vector sum, without assuming absolute summability of the vector norms. -/
theorem summable_of_summable_norm_inner {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (f : ι → E)
    (h : Summable (fun ij : ι × ι => ‖inner ℂ (f ij.1) (f ij.2)‖)) :
    Summable f := by
  classical
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp h (ε^2) (sq_pos_of_pos hε)
  refine ⟨s.image Prod.fst, fun t ht => ?_⟩
  have hdis : Disjoint (t ×ˢ t) s := by
    apply Finset.disjoint_left.mpr
    intro ij hij hsij
    exact Finset.disjoint_left.mp ht (Finset.mem_product.mp hij).1
      (Finset.mem_image_of_mem Prod.fst hsij)
  have htail := hs (t ×ˢ t) hdis
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at htail
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp
    ((norm_sum_sq_le_sum_norm_inner f t).trans_lt htail)
end RHTower
