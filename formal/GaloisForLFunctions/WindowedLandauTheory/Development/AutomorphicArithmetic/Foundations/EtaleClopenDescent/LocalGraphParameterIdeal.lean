import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Ideal.Span

/-! At a transverse fixed point, the difference of the two coordinate
lists generates the same ideal as the first list. -/

noncomputable section

open scoped Matrix

namespace GlobalTheory.WH

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

private theorem span_range_mulVec_le (A : Matrix ι ι R) (t : ι → R) :
    Ideal.span (Set.range (A *ᵥ t)) ≤ Ideal.span (Set.range t) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  change (∑ j, A i j * t j) ∈ _
  exact (Ideal.span (Set.range t)).sum_mem fun j _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self j))

/-- Invertible row operations preserve the ideal of the entries of
the parameter vector. -/
theorem span_range_mulVec_eq (A : Matrix ι ι R) (hA : IsUnit A.det) (t : ι → R) :
    Ideal.span (Set.range (A *ᵥ t)) = Ideal.span (Set.range t) := by
  apply le_antisymm (span_range_mulVec_le A t)
  have he : A⁻¹ *ᵥ (A *ᵥ t) = t := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]
  have hm := span_range_mulVec_le A⁻¹ (A *ᵥ t)
  rwa [he] at hm

end GlobalTheory.WH
