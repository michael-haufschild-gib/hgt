import Mathlib.LinearAlgebra.TensorProduct.Map
import GaloisForLFunctions.RHTower.CCMRationalBruhatNonUnitalAlgebra

/-!
# Nonunital multiplication on the rational adelic Bruhat tensor core

The algebraic rational Bruhat--Schwartz core is the complex tensor product of the
archimedean Schwartz factor with the compactly supported locally constant finite-adele
factor.  This file constructs its multiplication from the tensor-product universal property
and proves that it is a commutative nonunital complex algebra.

On pure tensors the law is exactly

`(f ⊗ g) * (f' ⊗ g') = (f * f') ⊗ (g * g')`.

The construction introduces no completion and no surrogate function algebra.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

private abbrev Arch := CCMRationalArchimedeanSchwartz
private abbrev FinBruhat := CCMRationalFiniteBruhatSchwartz
private abbrev AdelicCore := CCMRationalAdelicBruhatSimpleTensor

/-- Left pointwise multiplication on the archimedean Schwartz factor. -/
def ccmRationalArchimedeanSchwartzMulLeft (f : Arch) : Arch →ₗ[ℂ] Arch where
  toFun g := f * g
  map_add' g h := by
    ext x
    simp [mul_add]
  map_smul' z g := by
    ext x
    simp only [ccmRationalArchimedeanSchwartz_mul_apply,
      smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Left pointwise multiplication on the finite-adele Bruhat factor. -/
def ccmRationalFiniteBruhatMulLeft (f : FinBruhat) : FinBruhat →ₗ[ℂ] FinBruhat where
  toFun g := f * g
  map_add' g h := by
    apply Subtype.ext
    ext x
    simp [mul_add]
  map_smul' z g := by
    apply Subtype.ext
    ext x
    simp only [ccmRationalFiniteBruhat_mul_apply,
      Submodule.coe_smul, LocallyConstant.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

/-- Multiplication by a pure adelic tensor, as a linear endomorphism. -/
def ccmRationalAdelicBruhatPureMulLeft (f : Arch) (g : FinBruhat) :
    AdelicCore →ₗ[ℂ] AdelicCore :=
  TensorProduct.map
    (ccmRationalArchimedeanSchwartzMulLeft f)
    (ccmRationalFiniteBruhatMulLeft g)

@[simp]
theorem ccmRationalAdelicBruhatPureMulLeft_tmul
    (f f' : Arch) (g g' : FinBruhat) :
    ccmRationalAdelicBruhatPureMulLeft f g (f' ⊗ₜ[ℂ] g') =
      (f * f') ⊗ₜ[ℂ] (g * g') :=
  rfl

/-- The pure-tensor left-multiplication construction is bilinear in its two factors. -/
def ccmRationalAdelicBruhatPureMulLeftBilinear :
    Arch →ₗ[ℂ] FinBruhat →ₗ[ℂ] Module.End ℂ AdelicCore where
  toFun f :=
    { toFun := fun g => ccmRationalAdelicBruhatPureMulLeft f g
      map_add' := fun g h => by
        apply TensorProduct.ext'
        intro f' g'
        simp only [ccmRationalAdelicBruhatPureMulLeft_tmul,
          ccmRationalFiniteBruhatMulLeft, add_mul,
          TensorProduct.tmul_add, LinearMap.add_apply]
      map_smul' := fun z g => by
        apply TensorProduct.ext'
        intro f' g'
        simp only [ccmRationalAdelicBruhatPureMulLeft_tmul,
          ccmRationalFiniteBruhatMulLeft, smul_mul_assoc,
          TensorProduct.tmul_smul, LinearMap.smul_apply,
          RingHom.id_apply] }
  map_add' f h := by
    apply LinearMap.ext
    intro g
    apply TensorProduct.ext'
    intro f' g'
    change ((f + h) * f') ⊗ₜ[ℂ] (g * g') =
      (f * f') ⊗ₜ[ℂ] (g * g') + (h * f') ⊗ₜ[ℂ] (g * g')
    rw [add_mul, TensorProduct.add_tmul]
  map_smul' z f := by
    apply LinearMap.ext
    intro g
    apply TensorProduct.ext'
    intro f' g'
    change ((z • f) * f') ⊗ₜ[ℂ] (g * g') =
      (RingHom.id ℂ) z • ((f * f') ⊗ₜ[ℂ] (g * g'))
    rw [smul_mul_assoc, TensorProduct.smul_tmul']
    rfl

/-- Left multiplication on the full algebraic adelic tensor core. -/
def ccmRationalAdelicBruhatMulLeft :
    AdelicCore →ₗ[ℂ] Module.End ℂ AdelicCore :=
  TensorProduct.lift ccmRationalAdelicBruhatPureMulLeftBilinear

/-- Product on the full algebraic adelic Bruhat--Schwartz tensor core. -/
def ccmRationalAdelicBruhatMul (x y : AdelicCore) : AdelicCore :=
  ccmRationalAdelicBruhatMulLeft x y

instance : Mul CCMRationalAdelicBruhatSimpleTensor :=
  ⟨ccmRationalAdelicBruhatMul⟩

instance : SMul CCMRationalAdelicBruhatSimpleTensor
    CCMRationalAdelicBruhatSimpleTensor :=
  ⟨ccmRationalAdelicBruhatMul⟩

@[simp]
theorem ccmRationalAdelicBruhat_tmul_mul_tmul
    (f f' : Arch) (g g' : FinBruhat) :
    (f ⊗ₜ[ℂ] g : AdelicCore) * (f' ⊗ₜ[ℂ] g') =
      (f * f') ⊗ₜ[ℂ] (g * g') :=
  rfl

@[simp]
theorem ccmRationalAdelicBruhat_zero_mul (x : AdelicCore) :
    0 * x = 0 := by
  change ccmRationalAdelicBruhatMulLeft 0 x = 0
  rw [map_zero]
  rfl

@[simp]
theorem ccmRationalAdelicBruhat_mul_zero (x : AdelicCore) :
    x * 0 = 0 :=
  map_zero (ccmRationalAdelicBruhatMulLeft x)

theorem ccmRationalAdelicBruhat_add_mul (x y z : AdelicCore) :
    (x + y) * z = x * z + y * z := by
  change ccmRationalAdelicBruhatMulLeft (x + y) z =
    ccmRationalAdelicBruhatMulLeft x z +
      ccmRationalAdelicBruhatMulLeft y z
  rw [map_add]
  rfl

theorem ccmRationalAdelicBruhat_mul_add (x y z : AdelicCore) :
    x * (y + z) = x * y + x * z :=
  map_add (ccmRationalAdelicBruhatMulLeft x) y z

theorem ccmRationalAdelicBruhat_mul_comm (x y : AdelicCore) :
    x * y = y * x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul f' g' =>
          simp [mul_comm]
      | add y₁ y₂ hy₁ hy₂ =>
          rw [ccmRationalAdelicBruhat_mul_add,
            ccmRationalAdelicBruhat_add_mul, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ =>
      rw [ccmRationalAdelicBruhat_add_mul,
        ccmRationalAdelicBruhat_mul_add, hx₁, hx₂]

theorem ccmRationalAdelicBruhat_mul_assoc (x y z : AdelicCore) :
    (x * y) * z = x * (y * z) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul f' g' =>
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul f'' g'' => simp [mul_assoc]
          | add z₁ z₂ hz₁ hz₂ =>
              rw [ccmRationalAdelicBruhat_mul_add,
                ccmRationalAdelicBruhat_mul_add,
                ccmRationalAdelicBruhat_mul_add, hz₁, hz₂]
      | add y₁ y₂ hy₁ hy₂ =>
          simp only [ccmRationalAdelicBruhat_add_mul,
            ccmRationalAdelicBruhat_mul_add, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ =>
      rw [ccmRationalAdelicBruhat_add_mul,
        ccmRationalAdelicBruhat_add_mul,
        ccmRationalAdelicBruhat_add_mul, hx₁, hx₂]

instance : NonUnitalCommRing CCMRationalAdelicBruhatSimpleTensor where
  zero_mul := ccmRationalAdelicBruhat_zero_mul
  mul_zero := ccmRationalAdelicBruhat_mul_zero
  mul_assoc := ccmRationalAdelicBruhat_mul_assoc
  left_distrib := ccmRationalAdelicBruhat_mul_add
  right_distrib := ccmRationalAdelicBruhat_add_mul
  mul_comm := ccmRationalAdelicBruhat_mul_comm

instance : SMulCommClass ℂ CCMRationalAdelicBruhatSimpleTensor
    CCMRationalAdelicBruhatSimpleTensor where
  smul_comm z x y := by
    have hr := (ccmRationalAdelicBruhatMulLeft x).map_smul z y
    exact hr.symm

instance : IsScalarTower ℂ CCMRationalAdelicBruhatSimpleTensor
    CCMRationalAdelicBruhatSimpleTensor where
  smul_assoc z x y := by
    have h := congrArg (fun F : Module.End ℂ AdelicCore => F y)
      (LinearMap.map_smul ccmRationalAdelicBruhatMulLeft z x)
    exact h

/-- Sign-conjugation on the actual adelic tensor core is multiplicative. -/
theorem ccmRationalAdelicBruhatSimpleTensor_sigma_mul
    (x y : CCMRationalAdelicBruhatSimpleTensor) :
    ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma (x * y) =
      ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma x *
        ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul f' g' =>
          simp [ccmRationalArchimedeanSchwartzReflection_mul,
            ccmRationalFiniteBruhatReflection_mul]
      | add y₁ y₂ hy₁ hy₂ =>
          rw [ccmRationalAdelicBruhat_mul_add, map_add, map_add,
            ccmRationalAdelicBruhat_mul_add, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ =>
      rw [ccmRationalAdelicBruhat_add_mul, map_add, map_add,
        ccmRationalAdelicBruhat_add_mul, hx₁, hx₂]

end RHTower
end GaloisForLFunctions
