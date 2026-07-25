import Mathlib.LinearAlgebra.TensorProduct.Basic
import GaloisForLFunctions.RHTower.KRealKernelCokernel

/-!
# Tensor product of even `KRealStructure`s

Two conjugate-linear involutions act tensorwise on a complex tensor product. The balanced
semilinear universal property makes the tensorwise action conjugate-linear, and its square is
the identity.

This is the algebraic tensor-product bridge needed to combine rational archimedean Schwartz
and finite Bruhat factors. No completion, arithmetic spectrum, positivity, or
Riemann-hypothesis premise occurs.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

variable {M N : Type*}
  [AddCommGroup M] [Module ℂ M]
  [AddCommGroup N] [Module ℂ N]

/-- Balanced conjugate-bilinear tensorwise action of two even Real structures. -/
def kRealEvenTensorBilinear
    (KM : KRealStructure false M) (KN : KRealStructure false N) :
    M →ₛₗ[starRingEnd ℂ]
      N →ₛₗ[starRingEnd ℂ] TensorProduct ℂ M N where
  toFun m :=
    { toFun := fun n => KM.sigma m ⊗ₜ[ℂ] KN.sigma n
      map_add' n₁ n₂ := by simp [TensorProduct.tmul_add]
      map_smul' z n := by
        rw [map_smulₛₗ]
        exact TensorProduct.tmul_smul _ _ _ }
  map_add' m₁ m₂ := by
    apply LinearMap.ext
    intro n
    simp [TensorProduct.add_tmul]
  map_smul' z m := by
    apply LinearMap.ext
    intro n
    rw [map_smulₛₗ]
    exact TensorProduct.smul_tmul' _ _ _

/-- Tensorwise conjugate-linear involution obtained from the tensor universal property. -/
def kRealEvenTensorSigma
    (KM : KRealStructure false M) (KN : KRealStructure false N) :
    TensorProduct ℂ M N →ₗ⋆[ℂ] TensorProduct ℂ M N :=
  TensorProduct.lift (kRealEvenTensorBilinear KM KN)

@[simp]
theorem kRealEvenTensorSigma_tmul
    (KM : KRealStructure false M) (KN : KRealStructure false N)
    (m : M) (n : N) :
    kRealEvenTensorSigma KM KN (m ⊗ₜ[ℂ] n) =
      KM.sigma m ⊗ₜ[ℂ] KN.sigma n :=
  rfl

/-- Tensorwise application of two even Real structures squares to the identity. -/
theorem kRealEvenTensorSigma_sq
    (KM : KRealStructure false M) (KN : KRealStructure false N)
    (x : TensorProduct ℂ M N) :
    kRealEvenTensorSigma KM KN (kRealEvenTensorSigma KM KN x) = x := by
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul m n =>
      simp [KM.sq, KN.sq, kRealParityAction]

/-- Even `KRealStructure` on the complex tensor product of two even objects. -/
def kRealEvenTensorProduct
    (KM : KRealStructure false M) (KN : KRealStructure false N) :
    KRealStructure false (TensorProduct ℂ M N) where
  sigma := kRealEvenTensorSigma KM KN
  sq x := by
    simpa [kRealParityAction] using kRealEvenTensorSigma_sq KM KN x

end RHTower
end GaloisForLFunctions
