import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRepairPower
import Mathlib.LinearAlgebra.StdBasis

/-!
# Every finite defect has its actual surviving observation basis

The first k coefficients of the missing-gap polynomial identify the repaired
normalization quotient with real k-space. Transporting the standard basis gives
exactly the classes c, u c, ..., u^(k-1) c. The dimension is k and a higher
missing-mode class vanishes exactly at the proved repair threshold.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial Module


def cubicFiniteDefectMap (k : ℕ) : Polynomial (Polynomial ℝ) →ₗ[ℝ] (Fin k → ℝ) where
  toFun P i := (P.coeff 1).coeff i.val
  map_add' P Q := by ext i; simp
  map_smul' r P := by ext i; simp

theorem cubicFiniteDefectMap_apply (k : ℕ) (P : Polynomial (Polynomial ℝ)) (i : Fin k) :
    cubicFiniteDefectMap k P i=(P.coeff 1).coeff i.val := rfl

theorem cubicFiniteDefectMap_kernel (k : ℕ) :
    (cubicFiniteDefectMap k).ker=(cubicFiniteRepairAlgebra k).toSubmodule := by
  ext P
  change cubicFiniteDefectMap k P=0 ↔ P ∈ cubicFiniteRepairAlgebra k
  rw [cubicFiniteRepairAlgebra_mem]
  constructor
  · intro h n hn
    exact congrFun h ⟨n,hn⟩
  · intro h
    ext i
    exact h i.val i.isLt

theorem cubicFiniteDefectMap_surjective (k : ℕ) : Function.Surjective (cubicFiniteDefectMap k) := by
  intro c
  refine ⟨Polynomial.monomial 1 (∑ i : Fin k,Polynomial.monomial i.val (c i)),?_⟩
  ext j
  simp [cubicFiniteDefectMap_apply,Polynomial.coeff_monomial,Fin.val_eq_val]

def cubicFiniteDefectEquiv (k : ℕ) :
    (Polynomial (Polynomial ℝ) ⧸ (cubicFiniteRepairAlgebra k).toSubmodule) ≃ₗ[ℝ] (Fin k → ℝ) :=
  (Submodule.quotEquivOfEq _ _ (cubicFiniteDefectMap_kernel k).symm).trans
    ((cubicFiniteDefectMap k).quotKerEquivOfSurjective (cubicFiniteDefectMap_surjective k))

theorem cubicFiniteDefectEquiv_mk (k : ℕ) (P : Polynomial (Polynomial ℝ)) (i : Fin k) :
    cubicFiniteDefectEquiv k (Submodule.Quotient.mk P) i=(P.coeff 1).coeff i.val := rfl

def cubicFiniteDefectBasis (k : ℕ) :
    Basis (Fin k) ℝ (Polynomial (Polynomial ℝ) ⧸ (cubicFiniteRepairAlgebra k).toSubmodule) :=
  (Pi.basisFun ℝ (Fin k)).map (cubicFiniteDefectEquiv k).symm

theorem cubicFiniteDefectBasis_apply (k : ℕ) (i : Fin k) :
    cubicFiniteDefectBasis k i=Submodule.Quotient.mk (cubicRepairPowerWitness i.val) := by
  apply (cubicFiniteDefectEquiv k).injective
  rw [cubicFiniteDefectBasis,Basis.map_apply,LinearEquiv.apply_symm_apply]
  ext j
  rw [cubicFiniteDefectEquiv_mk,cubicRepairPowerWitness,Polynomial.C_mul_X_eq_monomial,
    Polynomial.coeff_monomial_same]
  simp [Pi.basisFun_apply,Pi.single_apply,Polynomial.coeff_X_pow,Fin.val_eq_val,eq_comm]

theorem cubicFiniteDefectBasis_nonzero (k : ℕ) (i : Fin k) : cubicFiniteDefectBasis k i ≠ 0 :=
  (cubicFiniteDefectBasis k).ne_zero i

theorem cubicFiniteDefect_finrank (k : ℕ) :
    Module.finrank ℝ (Polynomial (Polynomial ℝ) ⧸ (cubicFiniteRepairAlgebra k).toSubmodule)=k := by
  simpa using Module.finrank_eq_card_basis (cubicFiniteDefectBasis k)

theorem cubicFiniteDefect_class_vanishes (k j : ℕ) :
    (Submodule.Quotient.mk (cubicRepairPowerWitness j) :
      Polynomial (Polynomial ℝ) ⧸ (cubicFiniteRepairAlgebra k).toSubmodule)=0 ↔ k ≤ j := by
  change (Submodule.Quotient.mk (cubicRepairPowerWitness j) :
      Polynomial (Polynomial ℝ) ⧸ (cubicRepairAlgebra (cubicRepairPowerIdeal k)).toSubmodule)=0 ↔ k ≤ j
  rw [cubicRepairPowerWitness,cubicRepairDefect_middle_zero]
  have h := cubicRepairPowerWitness_mem k j
  simpa only [cubicFiniteRepairAlgebra,cubicRepairAlgebra_mem,cubicRepairPowerWitness,
    Polynomial.C_mul_X_eq_monomial,Polynomial.coeff_monomial_same] using h

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
