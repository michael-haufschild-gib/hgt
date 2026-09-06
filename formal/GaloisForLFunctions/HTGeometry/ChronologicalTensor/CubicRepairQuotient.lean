import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRepairAlgebra
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual normalization-defect quotients after observation repair

For every repair ideal, the outer linear coefficient descends to a linear
equivalence from the actual normalization-defect quotient to the first-mode
polynomial ring modulo that ideal. A missing-mode class vanishes exactly when
its coefficient lies in the repair ideal.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial


def cubicRepairDefectMap (I : Ideal (Polynomial ℝ)) :
    Polynomial (Polynomial ℝ) →ₗ[ℝ] Polynomial ℝ ⧸ I :=
  (Ideal.Quotient.mkₐ ℝ I).toLinearMap.comp cubicCuspDefectMap

theorem cubicRepairDefectMap_apply (I : Ideal (Polynomial ℝ)) (P : Polynomial (Polynomial ℝ)) :
    cubicRepairDefectMap I P=Ideal.Quotient.mk I (P.coeff 1) := rfl

theorem cubicRepairDefectMap_kernel (I : Ideal (Polynomial ℝ)) :
    (cubicRepairDefectMap I).ker=(cubicRepairAlgebra I).toSubmodule := by
  ext P
  change Ideal.Quotient.mk I (P.coeff 1)=0 ↔ P.coeff 1 ∈ I
  exact Ideal.Quotient.eq_zero_iff_mem

theorem cubicRepairDefectMap_surjective (I : Ideal (Polynomial ℝ)) :
    Function.Surjective (cubicRepairDefectMap I) :=
  (Ideal.Quotient.mkₐ_surjective ℝ I).comp cubicCuspDefectMap_surjective

def cubicRepairDefectEquiv (I : Ideal (Polynomial ℝ)) :
    (Polynomial (Polynomial ℝ) ⧸ (cubicRepairAlgebra I).toSubmodule) ≃ₗ[ℝ]
      Polynomial ℝ ⧸ I :=
  (Submodule.quotEquivOfEq _ _ (cubicRepairDefectMap_kernel I).symm).trans
    ((cubicRepairDefectMap I).quotKerEquivOfSurjective (cubicRepairDefectMap_surjective I))

theorem cubicRepairDefectEquiv_mk (I : Ideal (Polynomial ℝ)) (P : Polynomial (Polynomial ℝ)) :
    cubicRepairDefectEquiv I (Submodule.Quotient.mk P)=Ideal.Quotient.mk I (P.coeff 1) := rfl

theorem cubicRepairDefectEquiv_middle (I : Ideal (Polynomial ℝ)) (p : Polynomial ℝ) :
    cubicRepairDefectEquiv I (Submodule.Quotient.mk (Polynomial.C p*Polynomial.X))=
      Ideal.Quotient.mk I p := by
  rw [cubicRepairDefectEquiv_mk,Polynomial.C_mul_X_eq_monomial,Polynomial.coeff_monomial_same]

theorem cubicRepairDefect_middle_zero (I : Ideal (Polynomial ℝ)) (p : Polynomial ℝ) :
    (Submodule.Quotient.mk (Polynomial.C p*Polynomial.X) :
      Polynomial (Polynomial ℝ) ⧸ (cubicRepairAlgebra I).toSubmodule)=0 ↔ p ∈ I := by
  constructor
  · intro h
    have he := congrArg (cubicRepairDefectEquiv I) h
    rw [cubicRepairDefectEquiv_middle,map_zero] at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he
  · intro h
    apply (cubicRepairDefectEquiv I).injective
    rw [cubicRepairDefectEquiv_middle,map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
