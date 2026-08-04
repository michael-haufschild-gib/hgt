import GaloisForLFunctions.HTGeometry.DifferentialMatroidFiniteClosure
import GaloisForLFunctions.HTGeometry.TranslateFamilyIndependence

/-!
# Transferring differential independence across a spanning family

A finite family over which a differentially independent family of the same size is differentially
algebraic is itself differentially independent: in the differential matroid the second family spans
the first, so its rank is at least the size of the first, while its rank cannot exceed its own size.

This is the exchange step that identifies a differential transcendence basis without computing any
transcendence degree.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

universe u v

/-- **A spanning family of the size of an independent one is independent.** -/
theorem differentialIndependent_of_range_subset_closure
    {C E : Type u} {ι : Type v} [Field C] [Field E] [Algebra C E]
    [Differential C] [Differential E] [DifferentialAlgebra C E] [CharZero E] [Fintype ι]
    {x y : ι → E} (hx : DifferentialIndependent C x) (hyinj : Function.Injective y)
    (hspan : ∀ i, DifferentialAlgebraicOver (differentialAdjoin C (Set.range y)) (x i)) :
    DifferentialIndependent C y := by
  classical
  set M := GaloisForLFunctions.differentialMatroid C E with hM
  have hxIndep : M.Indep (Set.range x) :=
    (GaloisForLFunctions.differentialMatroid_indep_iff).mpr
      (diffIndepOn_range_of_differentialIndependent hx)
  have hsub : Set.range x ⊆ M.closure (Set.range y) := by
    rintro _ ⟨i, rfl⟩
    exact (GaloisForLFunctions.differentialMatroid_mem_closure_range_fintype_iff y (x i)).mpr
      (hspan i)
  have hlerk : (Set.range x).encard ≤ M.eRk (Set.range y) := by
    calc (Set.range x).encard = M.eRk (Set.range x) := hxIndep.eRk_eq_encard.symm
      _ ≤ M.eRk (M.closure (Set.range y)) := M.eRk_mono hsub
      _ = M.eRk (Set.range y) := Matroid.eRk_closure_eq M _
  have hcard : (Set.range x).encard = (Set.range y).encard := by
    have hxu : (Set.range x).encard = (Set.univ : Set ι).encard := by
      rw [← Set.image_univ]
      exact Set.InjOn.encard_image (hx.injective.injOn)
    have hyu : (Set.range y).encard = (Set.univ : Set ι).encard := by
      rw [← Set.image_univ]
      exact Set.InjOn.encard_image hyinj.injOn
    rw [hxu, hyu]
  have hyIndep : M.Indep (Set.range y) := by
    rw [Matroid.indep_iff_eRk_eq_encard_of_finite (Set.finite_range y)]
    exact le_antisymm (M.eRk_le_encard _) (hcard ▸ hlerk)
  have hset : DiffIndepOn C (Set.range y) :=
    (GaloisForLFunctions.differentialMatroid_indep_iff).mp hyIndep
  have hequiv : DifferentialIndependent C (Subtype.val : Set.range y → E) := hset
  have hcomp := hequiv.comp (Set.rangeFactorization y)
    fun a b hab ↦ hyinj (congrArg Subtype.val hab)
  simpa [Function.comp_def, Set.rangeFactorization] using hcomp

end

end GaloisForLFunctions.HTGeometry
