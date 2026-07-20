import GaloisForLFunctions.HTGeometry.ProjectiveImmittanceHorizon

/-!
# Reciprocal ABCD projective HT horizon law

Reciprocal electrical two-ports and canonically normalized paraxial optical systems obey the
same transfer law `a * d - b * c = 1`.  This file uses that equality to discharge the abstract
nondegeneracy premise in the projective-immittance hypertranscendence and reciprocal jet-horizon
theorems.

This is a parent-grade connector.  Determinant one supplies reciprocity, not passivity or an
arithmetic source realization.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- The reciprocal ABCD determinant law supplies projective nondegeneracy. -/
theorem reciprocalABCD_nonDegenerate
    {F : Type*} [Field F] (a b c d : F) (hrecip : a * d - b * c = 1) :
    a * d - b * c ≠ 0 := by
  rw [hrecip]
  exact one_ne_zero

/-- **Reciprocal ABCD projective HT horizon law.**  The determinant-one law shared by reciprocal
electrical chain matrices and normalized paraxial optical ray matrices simultaneously discharges
the nondegeneracy premise for projective HT preservation and for the complete reciprocal
impedance/admittance jet-horizon classification. -/
theorem reciprocalABCD_projective_hypertranscendence_and_horizon_law
    {F E : Type*} [Field F] [CharZero F] [Field E] [CharZero E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    (x : E) (hx : HypertranscendentalOver F x)
    (a b c d : F) (hrecip : a * d - b * c = 1) :
    HypertranscendentalOver F (projectiveImmittanceChart a b c d x) ∧
      ((∀ n : ℕ,
          jetTailField F (projectiveImmittanceChart a b c d x⁻¹) n =
            jetTailField F (projectiveImmittanceChart a b c d x) n) ↔
        d ^ 2 = c ^ 2) := by
  have hdet := reciprocalABCD_nonDegenerate a b c d hrecip
  exact ⟨
    hypertranscendentalOver_projectiveImmittanceChart x hx a b c d hdet,
    projectiveImmittanceChart_inv_all_jetTailField_eq_iff x hx a b c d hdet⟩

end

end GaloisForLFunctions
