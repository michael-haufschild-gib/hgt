import GaloisForLFunctions.HTGeometry.TensorProductDifferential
import GaloisForLFunctions.HTGeometry.DifferentialPolynomialBaseChange

/-!
# Differential finite generation under scalar extension

Extending coefficients in a differential polynomial and evaluating at the right tensor inclusions
commute exactly.  Consequently a finite differential generating family remains generating after
any differential field scalar extension.
-/

open scoped TensorProduct Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions

variable {K L E : Type*} [Field K] [Field L] [CommRing E]
  [Algebra K L] [Algebra K E]
  [Differential K] [Differential L] [Differential E]
  [DifferentialAlgebra K L] [DifferentialAlgebra K E]

/-- Differential-polynomial evaluation commutes with differential scalar extension. -/
theorem differentialPolynomialEvalOver_tensorBaseChange {ι : Type*} (y : ι → E)
    (P : DifferentialPolynomial ι K) :
    letI : Differential (L ⊗[K] E) := tensorProductDifferential
    differentialPolynomialEvalOver (K := L)
        (fun i => (1 : L) ⊗ₜ[K] y i)
        (differentialCoeffExtend (ι := ι) (F := K) (L := L) P) =
      (1 : L) ⊗ₜ[K] differentialPolynomialEvalOver (K := K) y P := by
  letI : Differential (L ⊗[K] E) := tensorProductDifferential
  let φ : E →+* (L ⊗[K] E) :=
    (Algebra.TensorProduct.includeRight : E →ₐ[K] (L ⊗[K] E)).toRingHom
  have hφδ : ∀ x : E, φ (Differential.deriv x) = Differential.deriv (φ x) := by
    intro x
    change (1 : L) ⊗ₜ[K] Differential.deriv x =
      tensorProductDerivation (K := K) ((1 : L) ⊗ₜ[K] x)
    rw [tensorProductDerivation_tmul, Derivation.map_one_eq_zero]
    simp
  have hφK : ∀ a : K, φ (algebraMap K E a) =
      algebraMap K (L ⊗[K] E) a := by
    intro a
    simp [φ]
  have hmap := map_differentialPolynomialEvalOver (F := K) φ hφδ hφK y P
  rw [differentialPolynomialEvalOver_differentialCoeffExtend]
  exact hmap.symm

/-- A finite differential generating family remains generating after differential scalar
extension. -/
theorem differentialPolynomialEvalOver_tensorBaseChange_surjective {k : ℕ} (y : Fin k → E)
    (hy : Function.Surjective (differentialPolynomialEvalOver (K := K) y)) :
    letI : Differential (L ⊗[K] E) := tensorProductDifferential
    Function.Surjective
      (differentialPolynomialEvalOver (K := L)
        (fun i => (1 : L) ⊗ₜ[K] y i)) := by
  letI : Differential (L ⊗[K] E) := tensorProductDifferential
  let Ψ := differentialPolynomialEvalOver (K := L)
    (fun i => (1 : L) ⊗ₜ[K] y i)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero Ψ⟩
  | tmul l e =>
      obtain ⟨P, rfl⟩ := hy e
      refine ⟨MvPolynomial.C l * differentialCoeffExtend
        (ι := Fin k) (F := K) (L := L) P, ?_⟩
      change Ψ (MvPolynomial.C l * differentialCoeffExtend P) = _
      rw [map_mul, differentialPolynomialEvalOver_C,
        differentialPolynomialEvalOver_tensorBaseChange]
      simp
  | add x z hx hz =>
      obtain ⟨P, rfl⟩ := hx
      obtain ⟨Q, rfl⟩ := hz
      exact ⟨P + Q, map_add Ψ P Q⟩

end

end GaloisForLFunctions.HTGeometry
