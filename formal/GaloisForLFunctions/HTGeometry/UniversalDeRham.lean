import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-!
# Universal de Rham differential in degrees one and two

Mathlib provides Kähler one-forms as the cotangent quotient `I / I²` and the exterior
algebra on those one-forms, but not the de Rham differential between them.  This file
constructs the canonical base-linear map

`d₁ : Ω[S⁄R] →ₗ[R] ExteriorAlgebra S Ω[S⁄R]`

from the tensor-level rule `a ⊗ b ↦ da ∧ db`.  The main well-definedness proof shows
that this tensor map vanishes on products in the multiplication ideal, hence descends
through `I / I²`.  The resulting map satisfies the universal rule
`d₁ (a • db) = da ∧ db`.
-/

noncomputable section

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry.UniversalDeRham

universe u v

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Universal Kähler one-forms. -/
abbrev OneForms := KaehlerDifferential R S

/-- Universal exterior algebra of differential forms. -/
abbrev DifferentialForms := ExteriorAlgebra S (OneForms R S)

local instance : Algebra R (DifferentialForms R S) :=
  Algebra.restrictScalars R S _

local instance : IsScalarTower R S (DifferentialForms R S) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Tensor square used by the cotangent presentation of Kähler differentials. -/
abbrev TensorSquare := S ⊗[R] S

/-- Wedge multiplication on universal one-forms. -/
def wedgeBilinear :
    OneForms R S →ₗ[S] OneForms R S →ₗ[S] DifferentialForms R S :=
  (LinearMap.mul S (DifferentialForms R S)).compl₁₂
    (ExteriorAlgebra.ι S) (ExteriorAlgebra.ι S)

@[simp]
theorem wedgeBilinear_apply (x y : OneForms R S) :
    wedgeBilinear R S x y = ExteriorAlgebra.ι S x * ExteriorAlgebra.ι S y := rfl

/-- Wedge multiplication, restricted to the base ring. -/
def wedgeBilinearBase :
    OneForms R S →ₗ[R] OneForms R S →ₗ[R] DifferentialForms R S :=
  (wedgeBilinear R S).restrictScalars₁₂ R R

@[simp]
theorem wedgeBilinearBase_apply (x y : OneForms R S) :
    wedgeBilinearBase R S x y = ExteriorAlgebra.ι S x * ExteriorAlgebra.ι S y := by
  simp [wedgeBilinearBase, wedgeBilinear]

/-- Right tensor differential `a ⊗ b ↦ a db`. -/
def rightDifferential : TensorSquare R S →ₗ[R] OneForms R S :=
  (KaehlerDifferential.D R S).tensorProductTo.restrictScalars R

@[simp]
theorem rightDifferential_tmul (a b : S) :
    rightDifferential R S (a ⊗ₜ[R] b) = a • KaehlerDifferential.D R S b := rfl

/-- Left tensor differential `a ⊗ b ↦ b da`. -/
def leftDifferential : TensorSquare R S →ₗ[R] OneForms R S :=
  (rightDifferential R S).comp (TensorProduct.comm R S S).toLinearMap

@[simp]
theorem leftDifferential_tmul (a b : S) :
    leftDifferential R S (a ⊗ₜ[R] b) = b • KaehlerDifferential.D R S a := rfl

/-- Tensor representative of exterior differentiation: `a ⊗ b ↦ da ∧ db`. -/
def tensorExteriorDifferential :
    TensorSquare R S →ₗ[R] DifferentialForms R S :=
  TensorProduct.lift <|
    (wedgeBilinearBase R S).compl₁₂
      (KaehlerDifferential.D R S).toLinearMap
      (KaehlerDifferential.D R S).toLinearMap

@[simp]
theorem tensorExteriorDifferential_tmul (a b : S) :
    tensorExteriorDifferential R S (a ⊗ₜ[R] b) =
      ExteriorAlgebra.ι S (KaehlerDifferential.D R S a) *
        ExteriorAlgebra.ι S (KaehlerDifferential.D R S b) := by
  simp [tensorExteriorDifferential]

/-- Multiplication map on the tensor square, viewed as an `R`-linear map. -/
def multiplicationLinear : TensorSquare R S →ₗ[R] S :=
  (Algebra.TensorProduct.lmul' R).toLinearMap

@[simp]
theorem multiplicationLinear_tmul (a b : S) :
    multiplicationLinear R S (a ⊗ₜ[R] b) = a * b := rfl

/-- Left and right tensor differentials add to the differential of multiplication. -/
theorem left_add_right_eq_D_multiplication (x : TensorSquare R S) :
    leftDifferential R S x + rightDifferential R S x =
      KaehlerDifferential.D R S (multiplicationLinear R S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Derivation.leibniz, add_comm]
  | add x y hx hy =>
      simp only [map_add]
      rw [← hx, ← hy]
      abel

/-- Product rule for the tensor representative of the exterior differential. -/
theorem tensorExteriorDifferential_mul_formula (x y : TensorSquare R S) :
    tensorExteriorDifferential R S (x * y) =
      multiplicationLinear R S y • tensorExteriorDifferential R S x +
      multiplicationLinear R S x • tensorExteriorDifferential R S y +
      ExteriorAlgebra.ι S (leftDifferential R S x) *
        ExteriorAlgebra.ι S (rightDifferential R S y) +
      ExteriorAlgebra.ι S (leftDifferential R S y) *
        ExteriorAlgebra.ι S (rightDifferential R S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
      simp only [add_mul, map_add, hx₁, hx₂]
      simp only [add_smul, mul_add]
      module
  | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y₁ y₂ hy₁ hy₂ =>
          simp only [mul_add, map_add, hy₁, hy₂]
          simp only [add_smul, add_mul]
          module
      | tmul c d =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul,
            tensorExteriorDifferential_tmul, multiplicationLinear_tmul,
            leftDifferential_tmul, rightDifferential_tmul,
            Derivation.leibniz, map_add, map_smul]
          simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
          module

/-- Tensor exterior differential restricted to the multiplication ideal. -/
def tensorExteriorDifferentialOnIdeal :
    KaehlerDifferential.ideal R S →ₗ[R] DifferentialForms R S where
  toFun x := tensorExteriorDifferential R S x.1
  map_add' x y := by simp
  map_smul' r x := by simp

@[simp]
theorem tensorExteriorDifferentialOnIdeal_apply
    (x : KaehlerDifferential.ideal R S) :
    tensorExteriorDifferentialOnIdeal R S x = tensorExteriorDifferential R S x := rfl

/-- The tensor exterior differential kills `I²`, the well-definedness theorem for `d₁`. -/
theorem tensorExteriorDifferentialOnIdeal_mul_eq_zero
    (x y : KaehlerDifferential.ideal R S) :
    tensorExteriorDifferentialOnIdeal R S (x * y) = 0 := by
  have hμx : multiplicationLinear R S x = 0 := by
    change (Algebra.TensorProduct.lmul' (S := S) R) x.1 = 0
    exact RingHom.mem_ker.mp x.prop
  have hμy : multiplicationLinear R S y = 0 := by
    change (Algebra.TensorProduct.lmul' (S := S) R) y.1 = 0
    exact RingHom.mem_ker.mp y.prop
  have hx := left_add_right_eq_D_multiplication R S x
  have hy := left_add_right_eq_D_multiplication R S y
  rw [hμx, map_zero] at hx
  rw [hμy, map_zero] at hy
  have hlx : leftDifferential R S x = -rightDifferential R S x :=
    eq_neg_of_add_eq_zero_left hx
  have hly : leftDifferential R S y = -rightDifferential R S y :=
    eq_neg_of_add_eq_zero_left hy
  change tensorExteriorDifferential R S (x.1 * y.1) = 0
  rw [tensorExteriorDifferential_mul_formula, hμx, hμy]
  simp only [zero_smul, zero_add, hlx, hly, map_neg, neg_mul]
  rw [← neg_add]
  have h := congrArg Neg.neg
    (ExteriorAlgebra.ι_add_mul_swap (R := S)
      (rightDifferential R S x) (rightDifferential R S y))
  rw [neg_zero] at h
  exact h

/-- Universal exterior derivative from Kähler one-forms to universal two-forms. -/
def oneFormExteriorDerivative :
    OneForms R S →ₗ[R] DifferentialForms R S :=
  (Ideal.Cotangent.lift (tensorExteriorDifferentialOnIdeal R S)
    (tensorExteriorDifferentialOnIdeal_mul_eq_zero R S)).comp
      (Submodule.Quotient.restrictScalarsEquiv R _).symm.toLinearMap

@[simp]
theorem oneFormExteriorDerivative_toCotangent
    (x : KaehlerDifferential.ideal R S) :
    oneFormExteriorDerivative R S
        ((KaehlerDifferential.ideal R S).toCotangent x) =
      tensorExteriorDifferentialOnIdeal R S x := by
  rfl

/-- Universal de Rham rule `d(a db) = da ∧ db`. -/
theorem oneFormExteriorDerivative_smul_D (a b : S) :
    oneFormExteriorDerivative R S (a • KaehlerDifferential.D R S b) =
      ExteriorAlgebra.ι S (KaehlerDifferential.D R S a) *
        ExteriorAlgebra.ι S (KaehlerDifferential.D R S b) := by
  let x : KaehlerDifferential.ideal R S :=
    ⟨a ⊗ₜ[R] b - (a * b) ⊗ₜ[R] 1, by simp [RingHom.mem_ker]⟩
  have hx : (KaehlerDifferential.ideal R S).toCotangent x =
      a • KaehlerDifferential.D R S b := by
    rw [← KaehlerDifferential.D_tensorProductTo]
    simp [x, Derivation.tensorProductTo_tmul]
  rw [← hx, oneFormExteriorDerivative_toCotangent]
  simp [tensorExteriorDifferentialOnIdeal, x, tensorExteriorDifferential_tmul]

end GaloisForLFunctions.HTGeometry.UniversalDeRham
