import GaloisForLFunctions.HTGeometry.CDGATensorSingle
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# The Koszul product on a bidegree of a tensor product of algebras

The tensor product of two commutative differential graded algebras is graded by the total degree,
and its product pairs a bidegree with a bidegree.  On pure tensors it is
`(x₁ ⊗ y₁)(x₂ ⊗ y₂) = (−1)^{|y₁||x₂|}(x₁x₂) ⊗ (y₁y₂)`, and the whole of the sign bookkeeping of the
tensor product of algebras happens here, one bidegree at a time.

* `HTGeometry.tensorPairₗ` : the product of two bidegrees.
* `HTGeometry.tensorPair_comm` : graded commutativity.
* `HTGeometry.tensorPair_assoc` : associativity.
-/

universe u w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type w} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {Y : ℕ → Type w} [∀ n, AddCommGroup (Y n)] [∀ n, Module R (Y n)]

/-- Two powers of `−1` agree when their exponents differ by an even number. -/
theorem neg_one_pow_eq_of_even_add (m k : ℕ) (t : ℕ) (h : m + k = 2 * t) :
    ((-1 : R)) ^ m = ((-1 : R)) ^ k := by
  have h1 : ((-1 : R)) ^ m * ((-1 : R)) ^ k = 1 := by
    rw [← pow_add, h, pow_mul]
    norm_num
  have h2 : ((-1 : R)) ^ k * ((-1 : R)) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc ((-1 : R)) ^ m = ((-1 : R)) ^ m * (((-1 : R)) ^ k * ((-1 : R)) ^ k) := by rw [h2, mul_one]
    _ = (((-1 : R)) ^ m * ((-1 : R)) ^ k) * ((-1 : R)) ^ k := by ring
    _ = ((-1 : R)) ^ k := by rw [h1, one_mul]

section Pair

variable (A : CDGAStructure R X) (B : CDGAStructure R Y)

/-- The Koszul product of two bidegrees, as a map out of the tensor product of the two bidegrees. -/
noncomputable def tensorPairMap {a₁ a₂ b₁ b₂ n₁ n₂ : ℕ} (h₁ : a₁ + b₁ = n₁) (h₂ : a₂ + b₂ = n₂) :
    TensorProduct R (TensorProduct R (X a₁) (Y a₂)) (TensorProduct R (X b₁) (Y b₂)) →ₗ[R]
      TensorProduct R (X n₁) (Y n₂) :=
  ((-1 : R)) ^ (a₂ * b₁) •
    (TensorProduct.map (TensorProduct.lift (A.mulₗ h₁)) (TensorProduct.lift (B.mulₗ h₂))).comp
      (TensorProduct.tensorTensorTensorComm R (X a₁) (Y a₂) (X b₁) (Y b₂)).toLinearMap

/-- The Koszul product of two bidegrees. -/
noncomputable def tensorPairₗ {a₁ a₂ b₁ b₂ n₁ n₂ : ℕ} (h₁ : a₁ + b₁ = n₁) (h₂ : a₂ + b₂ = n₂) :
    TensorProduct R (X a₁) (Y a₂) →ₗ[R] TensorProduct R (X b₁) (Y b₂) →ₗ[R]
      TensorProduct R (X n₁) (Y n₂) :=
  TensorProduct.curry (tensorPairMap A B h₁ h₂)

@[simp] theorem tensorPairₗ_tmul {a₁ a₂ b₁ b₂ n₁ n₂ : ℕ} (h₁ : a₁ + b₁ = n₁) (h₂ : a₂ + b₂ = n₂)
    (x₁ : X a₁) (y₁ : Y a₂) (x₂ : X b₁) (y₂ : Y b₂) :
    tensorPairₗ A B h₁ h₂ (x₁ ⊗ₜ[R] y₁) (x₂ ⊗ₜ[R] y₂)
      = ((-1 : R)) ^ (a₂ * b₁) • (A.mul h₁ x₁ x₂ ⊗ₜ[R] B.mul h₂ y₁ y₂) := by
  show (((-1 : R)) ^ (a₂ * b₁) •
    (TensorProduct.map (TensorProduct.lift (A.mulₗ h₁)) (TensorProduct.lift (B.mulₗ h₂))).comp
      (TensorProduct.tensorTensorTensorComm R (X a₁) (Y a₂) (X b₁) (Y b₂)).toLinearMap)
        ((x₁ ⊗ₜ[R] y₁) ⊗ₜ[R] (x₂ ⊗ₜ[R] y₂)) = _
  rw [LinearMap.smul_apply, LinearMap.comp_apply]
  show ((-1 : R)) ^ (a₂ * b₁) • (TensorProduct.map (TensorProduct.lift (A.mulₗ h₁))
    (TensorProduct.lift (B.mulₗ h₂))) (TensorProduct.tensorTensorTensorComm R _ _ _ _
      ((x₁ ⊗ₜ[R] y₁) ⊗ₜ[R] (x₂ ⊗ₜ[R] y₂))) = _
  rw [TensorProduct.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
    TensorProduct.lift.tmul, TensorProduct.lift.tmul]
  rfl

/-- **Graded commutativity of the Koszul product**, bidegree by bidegree: the sign of the product
in the two algebras and the Koszul sign of the shuffle combine into the sign of the total degrees.
-/
theorem tensorPair_comm {a₁ a₂ b₁ b₂ n₁ n₂ : ℕ} (h₁ : a₁ + b₁ = n₁) (h₂ : a₂ + b₂ = n₂)
    (h₁' : b₁ + a₁ = n₁) (h₂' : b₂ + a₂ = n₂)
    (z : TensorProduct R (X a₁) (Y a₂)) (w : TensorProduct R (X b₁) (Y b₂)) :
    tensorPairₗ A B h₁ h₂ z w
      = ((-1 : R)) ^ ((a₁ + a₂) * (b₁ + b₂)) • tensorPairₗ A B h₁' h₂' w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x₁ y₁ =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x₂ y₂ =>
          rw [tensorPairₗ_tmul, tensorPairₗ_tmul, A.mul_comm h₁' h₁ x₂ x₁,
            B.mul_comm h₂' h₂ y₂ y₁]
          simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, ← pow_add]
          refine congrArg (fun r : R => r • (A.mul h₁ x₁ x₂ ⊗ₜ[R] B.mul h₂ y₁ y₂)) ?_
          refine neg_one_pow_eq_of_even_add _ _ (a₁ * b₁ + a₂ * b₂ + a₁ * b₂) ?_
          ring
      | add w w' hw hw' =>
          rw [map_add, map_add, hw, hw', smul_add]
  | add z z' hz hz' =>
      rw [map_add, LinearMap.add_apply, hz, hz', map_add, smul_add]

end Pair

end GaloisForLFunctions.HTGeometry
