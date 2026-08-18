import GaloisForLFunctions.HTGeometry.AbelianVariety
import GaloisForLFunctions.HTGeometry.FiniteDeckFixedField

/-!
# Each multiplication level is the torsion deck fixed field

At depth `n` the image of the function-field pullback by `[m]` is contained in the fixed field of
the translations by rational `m^n`-torsion points.  Once that deck group is finite and the
extension degree equals its cardinality, Artin's fixed-field theorem upgrades the inclusion to
equality: the `n`-th multiplication level is exactly the field of `m^n`-torsion invariants.

This is the finite Galois description of one multiplication level.  The degree data are the
classical isogeny facts and are explicit hypotheses.
-/

open CategoryTheory Limits
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry

noncomputable section

universe u

/-- Every rational `m^n`-torsion translation fixes the depth-`n` multiplication pullback. -/
theorem abelianVarietyTorsionDeckGroup_pow_fix_multiplicationPullback_pow
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (m : ℤ) [IsDominant (abelianVarietyMultiplication A m).left]
    (n : ℕ)
    (σ : letI := abelianVarietyFunctionFieldAlgebra A
      A.left.functionField ≃ₐ[K] A.left.functionField)
    (hσ : letI := abelianVarietyFunctionFieldAlgebra A
      σ ∈ abelianVarietyTorsionDeckGroup A (m ^ n))
    (z : A.left.functionField) :
    letI := abelianVarietyFunctionFieldAlgebra A
    σ (((abelianVarietyMultiplicationFunctionFieldPullback A m) ^ n) z) =
      ((abelianVarietyMultiplicationFunctionFieldPullback A m) ^ n) z := by
  letI := abelianVarietyFunctionFieldAlgebra A
  rw [abelianVarietyMultiplicationFunctionFieldPullback_pow_apply]
  exact abelianVarietyTorsionDeckGroup_fix_multiplicationPullback A (m ^ n) σ hσ z

/-- **The finite Galois description of a multiplication level.**  With finite torsion deck groups
of the expected order, the depth-`n` image of multiplication pullback is exactly the fixed field of
the `m^n`-torsion translations. -/
theorem map_abelianVarietyMultiplicationFunctionFieldPullback_pow_top_eq_fixedField
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
        Nat.card (abelianVarietyTorsionDeckGroup A (m ^ n)))
    (n : ℕ) :
    letI := abelianVarietyFunctionFieldAlgebra A
    IntermediateField.map
        ((abelianVarietyMultiplicationFunctionFieldPullback A m) ^ n) ⊤ =
      IntermediateField.fixedField (abelianVarietyTorsionDeckGroup A (m ^ n)) := by
  letI := abelianVarietyFunctionFieldAlgebra A
  exact iterateImage_eq_fixedField_of_finiteDeckDegree
    (abelianVarietyMultiplicationFunctionFieldPullback A m)
    (fun n => abelianVarietyTorsionDeckGroup A (m ^ n))
    hfinite hfiniteDimensional
    (fun n σ hσ z =>
      abelianVarietyTorsionDeckGroup_pow_fix_multiplicationPullback_pow A m n σ hσ z)
    hdegree n

end

end GaloisForLFunctions.HTGeometry
