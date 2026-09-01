import GaloisForLFunctions.HTGeometry.TensorProductDifferential

/-!
# Semilinear automorphisms on asymmetric tensor products

Two algebra automorphisms inducing the same automorphism of their common scalar field act
factorwise on an asymmetric tensor product.  When both factor automorphisms commute with their
derivations, the induced tensor automorphism commutes with the Leibniz derivation.
-/

open scoped TensorProduct Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K A B : Type*} [Field K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]

theorem asymmetricDifferenceCompat_symm
    {sigmaK : K ≃+* K} {sigmaA : A ≃+* A}
    (hcompat : ∀ a : K, sigmaA (algebraMap K A a) = algebraMap K A (sigmaK a))
    (a : K) :
    sigmaA.symm (algebraMap K A a) = algebraMap K A (sigmaK.symm a) := by
  apply sigmaA.injective
  rw [sigmaA.apply_symm_apply, hcompat, sigmaK.apply_symm_apply]

/-- Additive factorwise action on an asymmetric tensor product. -/
def asymmetricDifferenceTensorAddHom
    (sigmaK : K ≃+* K) (sigmaA : A ≃+* A) (sigmaB : B ≃+* B)
    (hA : ∀ a : K, sigmaA (algebraMap K A a) = algebraMap K A (sigmaK a))
    (hB : ∀ a : K, sigmaB (algebraMap K B a) = algebraMap K B (sigmaK a)) :
    (A ⊗[K] B) →+ (A ⊗[K] B) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun x : A => AddMonoidHom.mk' (fun y : B => sigmaA x ⊗ₜ[K] sigmaB y)
        (fun y₁ y₂ => by rw [map_add, TensorProduct.tmul_add]))
      (fun x₁ x₂ => by
        refine AddMonoidHom.ext fun y => ?_
        show sigmaA (x₁ + x₂) ⊗ₜ[K] sigmaB y =
          sigmaA x₁ ⊗ₜ[K] sigmaB y + sigmaA x₂ ⊗ₜ[K] sigmaB y
        rw [map_add, TensorProduct.add_tmul]))
    (by
      intro a x y
      show sigmaA (a • x) ⊗ₜ[K] sigmaB y = sigmaA x ⊗ₜ[K] sigmaB (a • y)
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, hA, hB,
        ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul])

@[simp]
theorem asymmetricDifferenceTensorAddHom_tmul
    (sigmaK : K ≃+* K) (sigmaA : A ≃+* A) (sigmaB : B ≃+* B)
    (hA : ∀ a : K, sigmaA (algebraMap K A a) = algebraMap K A (sigmaK a))
    (hB : ∀ a : K, sigmaB (algebraMap K B a) = algebraMap K B (sigmaK a))
    (x : A) (y : B) :
    asymmetricDifferenceTensorAddHom sigmaK sigmaA sigmaB hA hB (x ⊗ₜ[K] y) =
      sigmaA x ⊗ₜ[K] sigmaB y := rfl

/-- Ring endomorphism induced factorwise by compatible semilinear automorphisms. -/
def asymmetricDifferenceTensorHom
    (sigmaK : K ≃+* K) (sigmaA : A ≃+* A) (sigmaB : B ≃+* B)
    (hA : ∀ a : K, sigmaA (algebraMap K A a) = algebraMap K A (sigmaK a))
    (hB : ∀ a : K, sigmaB (algebraMap K B a) = algebraMap K B (sigmaK a)) :
    (A ⊗[K] B) →+* (A ⊗[K] B) where
  toFun := asymmetricDifferenceTensorAddHom sigmaK sigmaA sigmaB hA hB
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    rw [Algebra.TensorProduct.one_def, asymmetricDifferenceTensorAddHom_tmul,
      map_one, map_one, ← Algebra.TensorProduct.one_def]
  map_mul' := by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        induction v using TensorProduct.induction_on with
        | zero => simp
        | tmul x' y' =>
            rw [Algebra.TensorProduct.tmul_mul_tmul,
              asymmetricDifferenceTensorAddHom_tmul,
              asymmetricDifferenceTensorAddHom_tmul,
              asymmetricDifferenceTensorAddHom_tmul, map_mul, map_mul,
              Algebra.TensorProduct.tmul_mul_tmul]
        | add v₁ v₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, mul_add]
    | add u₁ u₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]

@[simp]
theorem asymmetricDifferenceTensorHom_tmul
    (sigmaK : K ≃+* K) (sigmaA : A ≃+* A) (sigmaB : B ≃+* B)
    (hA : ∀ a : K, sigmaA (algebraMap K A a) = algebraMap K A (sigmaK a))
    (hB : ∀ a : K, sigmaB (algebraMap K B a) = algebraMap K B (sigmaK a))
    (x : A) (y : B) :
    asymmetricDifferenceTensorHom sigmaK sigmaA sigmaB hA hB (x ⊗ₜ[K] y) =
      sigmaA x ⊗ₜ[K] sigmaB y := rfl

/-- Factorwise semilinear action as a ring automorphism. -/
def asymmetricDifferenceTensorEquiv
    (sigmaK : K ≃+* K) (sigmaA : A ≃+* A) (sigmaB : B ≃+* B)
    (hA : ∀ a : K, sigmaA (algebraMap K A a) = algebraMap K A (sigmaK a))
    (hB : ∀ a : K, sigmaB (algebraMap K B a) = algebraMap K B (sigmaK a)) :
    (A ⊗[K] B) ≃+* (A ⊗[K] B) :=
  RingEquiv.ofRingHom
    (asymmetricDifferenceTensorHom sigmaK sigmaA sigmaB hA hB)
    (asymmetricDifferenceTensorHom sigmaK.symm sigmaA.symm sigmaB.symm
      (asymmetricDifferenceCompat_symm hA) (asymmetricDifferenceCompat_symm hB))
    (by
      refine RingHom.ext fun u => ?_
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
          simp only [RingHom.comp_apply, RingHom.id_apply]
          rw [asymmetricDifferenceTensorHom_tmul,
            asymmetricDifferenceTensorHom_tmul,
            sigmaA.apply_symm_apply, sigmaB.apply_symm_apply]
      | add u₁ u₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂])
    (by
      refine RingHom.ext fun u => ?_
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
          simp only [RingHom.comp_apply, RingHom.id_apply]
          rw [asymmetricDifferenceTensorHom_tmul,
            asymmetricDifferenceTensorHom_tmul,
            sigmaA.symm_apply_apply, sigmaB.symm_apply_apply]
      | add u₁ u₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂])

@[simp]
theorem asymmetricDifferenceTensorEquiv_tmul
    (sigmaK : K ≃+* K) (sigmaA : A ≃+* A) (sigmaB : B ≃+* B)
    (hA : ∀ a : K, sigmaA (algebraMap K A a) = algebraMap K A (sigmaK a))
    (hB : ∀ a : K, sigmaB (algebraMap K B a) = algebraMap K B (sigmaK a))
    (x : A) (y : B) :
    asymmetricDifferenceTensorEquiv sigmaK sigmaA sigmaB hA hB (x ⊗ₜ[K] y) =
      sigmaA x ⊗ₜ[K] sigmaB y := rfl

variable [Differential K] [Differential A] [Differential B]
  [DifferentialAlgebra K A] [DifferentialAlgebra K B]

/-- Compatible factor shifts commute with the asymmetric tensor-product derivation. -/
theorem asymmetricDifferenceTensorEquiv_deriv
    (sigmaK : K ≃+* K) (sigmaA : A ≃+* A) (sigmaB : B ≃+* B)
    (hA : ∀ a : K, sigmaA (algebraMap K A a) = algebraMap K A (sigmaK a))
    (hB : ∀ a : K, sigmaB (algebraMap K B a) = algebraMap K B (sigmaK a))
    (hAderiv : ∀ x : A, sigmaA (Differential.deriv x) = Differential.deriv (sigmaA x))
    (hBderiv : ∀ x : B, sigmaB (Differential.deriv x) = Differential.deriv (sigmaB x))
    (u : A ⊗[K] B) :
    letI : Differential (A ⊗[K] B) := tensorProductDifferential
    asymmetricDifferenceTensorEquiv sigmaK sigmaA sigmaB hA hB
        (Differential.deriv u) =
      Differential.deriv (asymmetricDifferenceTensorEquiv sigmaK sigmaA sigmaB hA hB u) := by
  letI : Differential (A ⊗[K] B) := tensorProductDifferential
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      change asymmetricDifferenceTensorEquiv sigmaK sigmaA sigmaB hA hB
          (tensorProductDerivation (K := K) (x ⊗ₜ[K] y)) =
        tensorProductDerivation (K := K)
          (asymmetricDifferenceTensorEquiv sigmaK sigmaA sigmaB hA hB (x ⊗ₜ[K] y))
      rw [tensorProductDerivation_tmul, map_add,
        asymmetricDifferenceTensorEquiv_tmul,
        asymmetricDifferenceTensorEquiv_tmul,
        asymmetricDifferenceTensorEquiv_tmul,
        tensorProductDerivation_tmul, hAderiv, hBderiv]
  | add u₁ u₂ h₁ h₂ =>
      rw [map_add, map_add, h₁, h₂]
      rw [map_add (asymmetricDifferenceTensorEquiv sigmaK sigmaA sigmaB hA hB)]
      have hadd := map_add
        (Differential.deriv : Derivation ℤ (A ⊗[K] B) (A ⊗[K] B))
        (asymmetricDifferenceTensorEquiv sigmaK sigmaA sigmaB hA hB u₁)
        (asymmetricDifferenceTensorEquiv sigmaK sigmaA sigmaB hA hB u₂)
      exact hadd.symm

end

end GaloisForLFunctions.HTGeometry
