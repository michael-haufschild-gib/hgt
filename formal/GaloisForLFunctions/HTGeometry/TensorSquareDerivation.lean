import GaloisForLFunctions.HTGeometry.ParameterizedGaloisRepresentation
import GaloisForLFunctions.HTGeometry.DifferenceTensorTorsor

/-!
# The derivation on a tensor square

The parameterized torsor argument needs the derivation, like the difference operator, to act on
`R ⊗_K R`.  It is not `K`-linear either — it moves the base field — but the same descent works:
`δ(a·x) ⊗ y + (a·x) ⊗ δ y` and `δ x ⊗ (a·y) + x ⊗ δ(a·y)` agree because `δ` on the base is the
restriction of `δ` on `R`, so the extra terms match after moving scalars across the tensor.

Both operators therefore live on the tensor square, and they commute there because they commute on
elementary tensors.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]
  [Differential K] [Differential R] [DifferentialAlgebra K R]

/-- The additive map `x ⊗ y ↦ δx ⊗ y + x ⊗ δy` on the tensor square. -/
def differentialTensorAddHom : (R ⊗[K] R) →+ (R ⊗[K] R) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun x : R => AddMonoidHom.mk'
        (fun y : R => Differential.deriv x ⊗ₜ[K] y + x ⊗ₜ[K] Differential.deriv y)
        (fun y₁ y₂ => by
          rw [map_add, TensorProduct.tmul_add, TensorProduct.tmul_add]
          abel))
      (fun x₁ x₂ => by
        refine AddMonoidHom.ext fun y => ?_
        show Differential.deriv (x₁ + x₂) ⊗ₜ[K] y + (x₁ + x₂) ⊗ₜ[K] Differential.deriv y
          = (Differential.deriv x₁ ⊗ₜ[K] y + x₁ ⊗ₜ[K] Differential.deriv y)
            + (Differential.deriv x₂ ⊗ₜ[K] y + x₂ ⊗ₜ[K] Differential.deriv y)
        rw [map_add, TensorProduct.add_tmul, TensorProduct.add_tmul]
        abel))
    (by
      intro a x y
      show Differential.deriv (a • x) ⊗ₜ[K] y + (a • x) ⊗ₜ[K] Differential.deriv y
        = Differential.deriv x ⊗ₜ[K] (a • y) + x ⊗ₜ[K] Differential.deriv (a • y)
      have hd : ∀ z : R, Differential.deriv (a • z)
          = Differential.deriv (algebraMap K R a) * z + algebraMap K R a * Differential.deriv z := by
        intro z
        rw [Algebra.smul_def, Derivation.leibniz]
        simp only [smul_eq_mul]
        ring
      have hbase : Differential.deriv (algebraMap K R a)
          = algebraMap K R (Differential.deriv a) := DifferentialAlgebra.deriv_algebraMap a
      rw [hd x, hd y, hbase]
      rw [← Algebra.smul_def, ← Algebra.smul_def, ← Algebra.smul_def, ← Algebra.smul_def]
      rw [TensorProduct.add_tmul, TensorProduct.tmul_add]
      simp only [TensorProduct.smul_tmul]
      abel)

@[simp] theorem differentialTensorAddHom_tmul {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    [Differential K] [Differential R] [DifferentialAlgebra K R] (x y : R) :
    differentialTensorAddHom (K := K) (x ⊗ₜ[K] y)
      = Differential.deriv x ⊗ₜ[K] y + x ⊗ₜ[K] Differential.deriv y := rfl

/-- **The derivation on the tensor square.** -/
def tensorSquareDerivation : Derivation ℤ (R ⊗[K] R) (R ⊗[K] R) :=
  Derivation.mk' (differentialTensorAddHom (K := K) (R := R)).toIntLinearMap
    (by
      intro u v
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
          induction v using TensorProduct.induction_on with
          | zero => simp
          | tmul x' y' =>
              show differentialTensorAddHom (K := K) ((x ⊗ₜ[K] y) * (x' ⊗ₜ[K] y'))
                = (x ⊗ₜ[K] y) • differentialTensorAddHom (K := K) (x' ⊗ₜ[K] y')
                  + (x' ⊗ₜ[K] y') • differentialTensorAddHom (K := K) (x ⊗ₜ[K] y)
              rw [Algebra.TensorProduct.tmul_mul_tmul, differentialTensorAddHom_tmul,
                differentialTensorAddHom_tmul, differentialTensorAddHom_tmul,
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

@[simp] theorem tensorSquareDerivation_tmul {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    [Differential K] [Differential R] [DifferentialAlgebra K R] (x y : R) :
    tensorSquareDerivation (K := K) (x ⊗ₜ[K] y)
      = Differential.deriv x ⊗ₜ[K] y + x ⊗ₜ[K] Differential.deriv y := rfl

/-- **The two operators commute on the tensor square.** -/
theorem tensorSquareDerivation_commutes (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (hσ : ∀ x : R, σR (Differential.deriv x) = Differential.deriv (σR x))
    (v : R ⊗[K] R) :
    differenceTensorEquiv σK σR hcompat (tensorSquareDerivation (K := K) v)
      = tensorSquareDerivation (K := K) (differenceTensorEquiv σK σR hcompat v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [tensorSquareDerivation_tmul, map_add, differenceTensorEquiv_tmul,
        differenceTensorEquiv_tmul, differenceTensorEquiv_tmul, tensorSquareDerivation_tmul,
        hσ x, hσ y]
  | add v₁ v₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, map_add, h₁, h₂]

end

end GaloisForLFunctions.HTGeometry
