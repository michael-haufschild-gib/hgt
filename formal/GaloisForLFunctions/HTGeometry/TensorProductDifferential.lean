import GaloisForLFunctions.HTGeometry.TensorSquareDerivation

/-!
# Differential structure on an asymmetric tensor product

If two differential algebras have the same differential base, their tensor product carries the
Leibniz derivation `δ(a ⊗ b) = δa ⊗ b + a ⊗ δb`.  The balancing proof uses compatibility of both
factor derivations with the base.  The resulting structure is a differential algebra over the left
factor, as needed for differential scalar extension.
-/

open scoped TensorProduct Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K A B : Type*} [Field K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]
  [Differential K] [Differential A] [Differential B]
  [DifferentialAlgebra K A] [DifferentialAlgebra K B]

/-- Additive form of the Leibniz derivation on an asymmetric tensor product. -/
def differentialTensorProductAddHom : (A ⊗[K] B) →+ (A ⊗[K] B) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun x : A => AddMonoidHom.mk'
        (fun y : B => Differential.deriv x ⊗ₜ[K] y + x ⊗ₜ[K] Differential.deriv y)
        (fun y₁ y₂ => by
          rw [map_add, TensorProduct.tmul_add, TensorProduct.tmul_add]
          abel))
      (fun x₁ x₂ => by
        refine AddMonoidHom.ext fun y => ?_
        show Differential.deriv (x₁ + x₂) ⊗ₜ[K] y +
            (x₁ + x₂) ⊗ₜ[K] Differential.deriv y =
          (Differential.deriv x₁ ⊗ₜ[K] y + x₁ ⊗ₜ[K] Differential.deriv y) +
            (Differential.deriv x₂ ⊗ₜ[K] y + x₂ ⊗ₜ[K] Differential.deriv y)
        rw [map_add, TensorProduct.add_tmul, TensorProduct.add_tmul]
        abel))
    (by
      intro k x y
      show Differential.deriv (k • x) ⊗ₜ[K] y + (k • x) ⊗ₜ[K] Differential.deriv y =
        Differential.deriv x ⊗ₜ[K] (k • y) + x ⊗ₜ[K] Differential.deriv (k • y)
      have hA : Differential.deriv (k • x) =
          Differential.deriv (algebraMap K A k) * x +
            algebraMap K A k * Differential.deriv x := by
        rw [Algebra.smul_def, Derivation.leibniz]
        simp only [smul_eq_mul]
        ring
      have hB : Differential.deriv (k • y) =
          Differential.deriv (algebraMap K B k) * y +
            algebraMap K B k * Differential.deriv y := by
        rw [Algebra.smul_def, Derivation.leibniz]
        simp only [smul_eq_mul]
        ring
      rw [hA, hB, DifferentialAlgebra.deriv_algebraMap,
        DifferentialAlgebra.deriv_algebraMap]
      rw [← Algebra.smul_def, ← Algebra.smul_def, ← Algebra.smul_def, ← Algebra.smul_def]
      rw [TensorProduct.add_tmul, TensorProduct.tmul_add]
      simp only [TensorProduct.smul_tmul]
      abel)

@[simp]
theorem differentialTensorProductAddHom_tmul (x : A) (y : B) :
    differentialTensorProductAddHom (K := K) (x ⊗ₜ[K] y) =
      Differential.deriv x ⊗ₜ[K] y + x ⊗ₜ[K] Differential.deriv y := rfl

/-- Leibniz derivation on an asymmetric tensor product of differential algebras. -/
def tensorProductDerivation : Derivation ℤ (A ⊗[K] B) (A ⊗[K] B) :=
  Derivation.mk' (differentialTensorProductAddHom (K := K) (A := A) (B := B)).toIntLinearMap
    (by
      intro u v
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
          induction v using TensorProduct.induction_on with
          | zero => simp
          | tmul x' y' =>
              show differentialTensorProductAddHom (K := K)
                    ((x ⊗ₜ[K] y) * (x' ⊗ₜ[K] y')) =
                (x ⊗ₜ[K] y) • differentialTensorProductAddHom (K := K) (x' ⊗ₜ[K] y') +
                  (x' ⊗ₜ[K] y') • differentialTensorProductAddHom (K := K) (x ⊗ₜ[K] y)
              rw [Algebra.TensorProduct.tmul_mul_tmul, differentialTensorProductAddHom_tmul,
                differentialTensorProductAddHom_tmul, differentialTensorProductAddHom_tmul,
                Derivation.leibniz, Derivation.leibniz]
              simp only [smul_eq_mul, TensorProduct.add_tmul, TensorProduct.tmul_add,
                mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
              abel
          | add v₁ v₂ h₁ h₂ =>
              rw [mul_add, map_add, h₁, h₂, map_add, smul_add, add_smul]
              abel
      | add u₁ u₂ h₁ h₂ =>
          rw [add_mul, map_add, h₁, h₂, map_add, smul_add, add_smul]
          abel)

@[simp]
theorem tensorProductDerivation_tmul (x : A) (y : B) :
    tensorProductDerivation (K := K) (x ⊗ₜ[K] y) =
      Differential.deriv x ⊗ₜ[K] y + x ⊗ₜ[K] Differential.deriv y := rfl

/-- Differential structure induced by the tensor-product Leibniz derivation. -/
@[reducible]
def tensorProductDifferential : Differential (A ⊗[K] B) where
  deriv := tensorProductDerivation (K := K)

/-- Differential scalar extension is compatible with the left-factor algebra map. -/
theorem tensorProductDifferentialAlgebra_left :
    letI : Differential (A ⊗[K] B) := tensorProductDifferential
    DifferentialAlgebra A (A ⊗[K] B) := by
  letI : Differential (A ⊗[K] B) := tensorProductDifferential
  constructor
  intro a
  change tensorProductDerivation (K := K) (a ⊗ₜ[K] (1 : B)) =
    (Differential.deriv a) ⊗ₜ[K] (1 : B)
  rw [tensorProductDerivation_tmul, Derivation.map_one_eq_zero]
  simp

end

end GaloisForLFunctions.HTGeometry
