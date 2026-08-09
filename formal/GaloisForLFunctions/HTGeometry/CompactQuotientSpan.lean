import GaloisForLFunctions.HTGeometry.EscapeSubgroup
import GaloisForLFunctions.HTGeometry.DenseOfVanishingDual

/-!
# A subgroup with compact quotient spans

If the quotient of a finite-dimensional real normed space by an additive subgroup is compact, the
subgroup spans the space over `ℝ`.  Otherwise a continuous functional vanishing on the span would
descend to a continuous surjection onto the real line, which no compact space admits.

This is the first half of "compact quotient forces a full lattice", the reduction that a
Siegel-type argument performs before it can speak of a fundamental parallelotope.

* **`span_eq_top_of_compactSpace_quotient`**.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A subgroup with compact quotient spans the space.** -/
theorem span_eq_top_of_compactSpace_quotient {P : AddSubgroup E}
    (h : CompactSpace (E ⧸ P)) : Submodule.span ℝ (P : Set E) = ⊤ := by
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ Submodule.span ℝ (P : Set E) := by
    by_contra hall
    exact hne (Submodule.eq_top_iff'.mpr fun z => not_not.mp fun hz => hall ⟨z, hz⟩)
  have hclosed : IsClosed ((Submodule.span ℝ (P : Set E) : Submodule ℝ E) : Set E) :=
    Submodule.closed_of_finiteDimensional _
  obtain ⟨f, hf0, hfx⟩ :=
    _root_.HTGeometry.exists_dual_vanishing_of_notMem_closed_submodule _ hclosed hx
  refine not_compactSpace_quotient_of_realSurjection
    (f.toLinearMap.toAddMonoidHom) f.continuous ?_ ?_ h
  · intro p hp
    exact hf0 p (Submodule.subset_span hp)
  · intro r
    refine ⟨(r / f x) • x, ?_⟩
    show f ((r / f x) • x) = r
    rw [map_smul, smul_eq_mul]
    field_simp

end GaloisForLFunctions.HTGeometry
