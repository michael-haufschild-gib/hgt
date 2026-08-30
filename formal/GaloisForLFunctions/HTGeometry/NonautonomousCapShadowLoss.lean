import GaloisForLFunctions.HTGeometry.NonautonomousCapGaussian
import GaloisForLFunctions.HTGeometry.TwoDefectDecomposition

/-!
# The nonautonomous Gaussian example has no shadow loss

For the nonautonomous cap `B(w) = w exp w` on the Gaussian primitive the compositum of the shadow
field with the jet field of the output is contained in the four-generator field, which is algebraic
over the output jet field.  Hence the shadow-recovery defect vanishes and the two-defect identity
reduces to `ord_DA (B ∘ G) = ord_DA (G′) + 2`: the entire cost is the surviving primitive state.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

theorem gaussTripleField_le_quadField :
    IntermediateField.adjoin ℂ gaussTriple ≤ quadField := by
  rw [quadField, IntermediateField.adjoin_le_iff]
  intro y hy
  exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ hy)

theorem jetElem_gaussPrimitive_mem_quadField (k : ℕ) :
    jetElem differentiable_gaussPrimitive k ∈ quadField :=
  gaussTripleField_le_quadField (jetElem_gaussPrimitive_mem k)

theorem visibilityField_prodQ_le_quadField :
    visibilityField differentiable_gaussPrimitive differentiable_prodQ ≤ quadField := by
  rw [visibilityField, IntermediateField.adjoin_le_iff]
  rintro y (hy | hy)
  · rcases hy with rfl | ⟨j, rfl⟩
    · exact coordElem_mem_quadField
    · exact jetElem_gaussPrimitive_mem_quadField (j + 1)
  · rcases hy with rfl | ⟨k, rfl⟩
    · exact coordElem_mem_quadField
    · exact jetElem_prodQ_mem_quadField k

/-- **The nonautonomous Gaussian example loses no shadow states.** -/
theorem shadowLoss_prodQ_eq_zero :
    shadowLoss (f := fun w : ℂ => w * Complex.exp w) differentiable_gaussPrimitive
      differentiable_prodQ = 0 := by
  have hgoal : shadowLoss (f := fun w : ℂ => w * Complex.exp w) differentiable_gaussPrimitive
      differentiable_prodQ
      = Algebra.trdeg ↥(IntermediateField.adjoin ℂ (compSet differentiable_prodQ))
        ↥(IntermediateField.extendScalars
          (jetField_le_visibilityField differentiable_gaussPrimitive differentiable_prodQ)) := rfl
  rw [hgoal]
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ℂ (compSet differentiable_prodQ))
      ↥(IntermediateField.extendScalars
        (jetField_le_visibilityField differentiable_gaussPrimitive differentiable_prodQ)) := by
    refine ⟨fun x => ?_⟩
    have hx : IsAlgebraic ↥(IntermediateField.adjoin ℂ (compSet differentiable_prodQ))
        ((x : meroField (Set.univ : Set ℂ))) :=
      isAlgebraic_quadField_over_prodQField _ (visibilityField_prodQ_le_quadField x.2)
    have hinj : Function.Injective (algebraMap
        ↥(IntermediateField.extendScalars
          (jetField_le_visibilityField differentiable_gaussPrimitive differentiable_prodQ))
        (meroField (Set.univ : Set ℂ))) := Subtype.val_injective
    obtain ⟨p, hp0, hp⟩ := hx
    refine ⟨p, hp0, hinj ?_⟩
    rw [map_zero, ← hp]
    exact (Polynomial.aeval_algebraMap_apply (meroField (Set.univ : Set ℂ)) x p).symm
  exact trdeg_eq_zero

end

end GaloisForLFunctions.HTGeometry
