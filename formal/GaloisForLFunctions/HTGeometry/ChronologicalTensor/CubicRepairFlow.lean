import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRepairClassification
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRepairBasis

/-!
# The physical flow on each finite observation defect

The actual repaired quotient inherits the polynomial pullback. In its proved
basis of surviving gap classes, its eigenvalues are exactly q, ..., q^k.
The coordinate formula establishes the entire induced operator, including its
identity, collapse, and composition laws.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial Module


def cubicFiniteDefectFlow (k : ℕ) (q : ℝ) :
    (Polynomial (Polynomial ℝ) ⧸ (cubicFiniteRepairAlgebra k).toSubmodule) →ₗ[ℝ]
      (Polynomial (Polynomial ℝ) ⧸ (cubicFiniteRepairAlgebra k).toSubmodule) :=
  (cubicFiniteRepairAlgebra k).toSubmodule.mapQ (cubicFiniteRepairAlgebra k).toSubmodule
    (cubicPolynomialFlow q).toLinearMap (cubicFiniteRepairAlgebra_flow q k)

theorem cubicFiniteDefectFlow_mk (k : ℕ) (q : ℝ) (P : Polynomial (Polynomial ℝ)) :
    cubicFiniteDefectFlow k q (Submodule.Quotient.mk P)=
      Submodule.Quotient.mk (cubicPolynomialFlow q P) := rfl

theorem cubicFiniteDefectFlow_coordinate (k : ℕ) (q : ℝ)
    (x : Polynomial (Polynomial ℝ) ⧸ (cubicFiniteRepairAlgebra k).toSubmodule) (i : Fin k) :
    cubicFiniteDefectEquiv k (cubicFiniteDefectFlow k q x) i=
      q^(i.val+1)*cubicFiniteDefectEquiv k x i := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro P
  rw [cubicFiniteDefectFlow_mk,cubicFiniteDefectEquiv_mk,cubicFiniteDefectEquiv_mk,
    cubicPolynomialFlow_coefficient,Polynomial.coeff_mul_C,
    cubicInnerPolynomialFlow_coefficient,pow_one,pow_succ]
  ring

theorem cubicFiniteDefectFlow_spectrum (k : ℕ) (q : ℝ) (i : Fin k) :
    cubicFiniteDefectFlow k q (cubicFiniteDefectBasis k i)=
      q^(i.val+1) • cubicFiniteDefectBasis k i := by
  apply (cubicFiniteDefectEquiv k).injective
  ext j
  rw [cubicFiniteDefectFlow_coordinate,map_smul]
  simp only [cubicFiniteDefectBasis,Basis.map_apply,LinearEquiv.apply_symm_apply,
    Pi.smul_apply,smul_eq_mul,Pi.basisFun_apply,Pi.single_apply]
  by_cases h : i=j
  · subst j; simp
  · simp [Ne.symm h]

theorem cubicFiniteDefectFlow_one (k : ℕ) : cubicFiniteDefectFlow k 1=LinearMap.id := by
  apply (cubicFiniteDefectBasis k).ext
  intro i
  simp [cubicFiniteDefectFlow_spectrum]

theorem cubicFiniteDefectFlow_zero (k : ℕ) : cubicFiniteDefectFlow k 0=0 := by
  apply (cubicFiniteDefectBasis k).ext
  intro i
  simp [cubicFiniteDefectFlow_spectrum]

theorem cubicFiniteDefectFlow_mul (k : ℕ) (q r : ℝ) :
    (cubicFiniteDefectFlow k q).comp (cubicFiniteDefectFlow k r)=
      cubicFiniteDefectFlow k (q*r) := by
  apply (cubicFiniteDefectBasis k).ext
  intro i
  simp only [LinearMap.comp_apply,cubicFiniteDefectFlow_spectrum,map_smul,
    ← mul_smul,mul_pow,mul_comm]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
