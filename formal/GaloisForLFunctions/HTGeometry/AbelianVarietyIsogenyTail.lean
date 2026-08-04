import GaloisForLFunctions.HTGeometry.AbelianVariety
import GaloisForLFunctions.HTGeometry.FiniteDeckFixedField

/-!
# Multiplication-isogeny tails of Abelian varieties

This module instantiates finite-depth deck invariance for the actual function field of an Abelian
variety and its multiplication morphisms.  Once standard finite-cover degree data are supplied,
the stable multiplication tail is exactly the fixed field of all multiplication-primary torsion
translations.  Deck invariance itself is derived from scheme translation and pullback functoriality.
-/

open CategoryTheory Limits
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

open AlgebraicGeometry

/-- For multiplication by `m` on an Abelian variety, exact finite cover degree data identify the
stable function-field tail with invariants of every multiplication-primary torsion translation.
No deck-invariance or fixed-field equality is assumed. -/
theorem abelianVarietyMultiplicationTail_eq_fixedField_primary
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) [IsDominant (abelianVarietyMultiplication A m).left]
    (hfinite : ∀ n, letI := abelianVarietyFunctionFieldAlgebra A
      Finite (abelianVarietyTorsionDeckGroup A (m ^ n)))
    (hfiniteDimensional : ∀ n, letI := abelianVarietyFunctionFieldAlgebra A
      FiniteDimensional
        (IntermediateField.map
          ((abelianVarietyMultiplicationFunctionFieldPullback A m) ^ n) ⊤)
        A.left.functionField)
    (hdegree : ∀ n, letI := abelianVarietyFunctionFieldAlgebra A
      Module.finrank
          (IntermediateField.map
            ((abelianVarietyMultiplicationFunctionFieldPullback A m) ^ n) ⊤)
          A.left.functionField =
        Nat.card (abelianVarietyTorsionDeckGroup A (m ^ n))) :
    letI := abelianVarietyFunctionFieldAlgebra A
    stableRangeCore (abelianVarietyMultiplicationFunctionFieldPullback A m) =
      IntermediateField.fixedField
        (abelianVarietyMultiplicationPrimaryTorsionDeckGroup A m) := by
  letI := abelianVarietyFunctionFieldAlgebra A
  rw [abelianVarietyMultiplicationPrimaryTorsionDeckGroup_eq_iSup]
  apply stableRangeCore_eq_fixedField_iSup_of_finiteDeckDegree
    (abelianVarietyMultiplicationFunctionFieldPullback A m)
    (fun n => abelianVarietyTorsionDeckGroup A (m ^ n))
    hfinite hfiniteDimensional
  · intro n sigma hsigma z
    rw [abelianVarietyMultiplicationFunctionFieldPullback_pow_apply]
    exact abelianVarietyTorsionDeckGroup_fix_multiplicationPullback
      A (m ^ n) sigma hsigma z
  · exact hdegree

end

end GaloisForLFunctions.HTGeometry
