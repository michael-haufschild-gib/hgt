import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicCuspAlgebra
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The actual missing-coordinate quotient of the observation cusp

Removing the outer linear coefficient gives an exact decomposition. The
coefficient map identifies the vector-space quotient by the cusp algebra with
one real polynomial ring. Transporting its monomial basis gives precisely the
classes of u^n c. This is a vector-space quotient, not a quotient ring.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial Module


def cubicCuspRemainder (P : Polynomial (Polynomial ℝ)) : Polynomial (Polynomial ℝ) :=
  P-Polynomial.monomial 1 (P.coeff 1)

theorem cubicCuspRemainder_mem (P : Polynomial (Polynomial ℝ)) :
    cubicCuspRemainder P ∈ cubicCuspAlgebra := by
  rw [cubicCuspAlgebra_mem]
  simp [cubicCuspRemainder]

theorem cubicCuspRemainder_decomposition (P : Polynomial (Polynomial ℝ)) :
    P=cubicCuspRemainder P+Polynomial.C (P.coeff 1)*Polynomial.X := by
  rw [Polynomial.C_mul_X_eq_monomial,cubicCuspRemainder]
  ring

def cubicCuspDefectMap : Polynomial (Polynomial ℝ) →ₗ[ℝ] Polynomial ℝ :=
  (Polynomial.lcoeff (Polynomial ℝ) 1).restrictScalars ℝ

theorem cubicCuspDefectMap_apply (P : Polynomial (Polynomial ℝ)) :
    cubicCuspDefectMap P=P.coeff 1 := rfl

theorem cubicCuspDefectMap_kernel :
    cubicCuspDefectMap.ker=cubicCuspAlgebra.toSubmodule := by
  ext P
  rfl

theorem cubicCuspDefectMap_surjective : Function.Surjective cubicCuspDefectMap := by
  intro p
  refine ⟨Polynomial.monomial 1 p,?_⟩
  simp [cubicCuspDefectMap_apply]

def cubicCuspDefectEquiv :
    (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) ≃ₗ[ℝ] Polynomial ℝ :=
  cubicCuspDefectMap.quotKerEquivOfSurjective cubicCuspDefectMap_surjective

theorem cubicCuspDefectEquiv_mk (P : Polynomial (Polynomial ℝ)) :
    cubicCuspDefectEquiv (Submodule.Quotient.mk P)=P.coeff 1 := rfl

def cubicCuspDefectBasis : Basis ℕ ℝ
    (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :=
  (Polynomial.basisMonomials ℝ).map cubicCuspDefectEquiv.symm

theorem cubicCuspDefectBasis_apply (n : ℕ) :
    cubicCuspDefectBasis n=
      Submodule.Quotient.mk (Polynomial.C (Polynomial.X^n)*Polynomial.X) := by
  apply cubicCuspDefectEquiv.injective
  simp only [cubicCuspDefectBasis,Basis.map_apply,LinearEquiv.apply_symm_apply,
    Polynomial.coe_basisMonomials,cubicCuspDefectEquiv_mk]
  rw [Polynomial.C_mul_X_eq_monomial,Polynomial.coeff_monomial]
  simp only [ite_true]
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp

theorem cubicCuspDefectBasis_nonzero (n : ℕ) : cubicCuspDefectBasis n ≠ 0 :=
  cubicCuspDefectBasis.ne_zero n

theorem cubicCuspDefectBasis_observation (n : ℕ) :
    cubicPolynomialObservation (Polynomial.C (Polynomial.X^n)*Polynomial.X)=
      (fun g => (cubicDecayMode 0 g.val)^n*g.val 2) := by
  rw [map_mul,map_pow,map_pow,
    cubicPolynomialObservation_firstMode,cubicPolynomialObservation_middle]
  rfl

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
