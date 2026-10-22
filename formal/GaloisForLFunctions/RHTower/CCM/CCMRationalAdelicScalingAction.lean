import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicBruhatNonUnitalAlgebra
import GaloisForLFunctions.RHTower.CCM.CCMRationalQuaternionicMoritaFiber

/-!
# Rational scaling on the actual adelic Bruhat--Schwartz tensor core

For `k ∈ ℚˣ`, the CCM coefficient action is pullback by inverse diagonal scaling,

`(αₖ f)(x) = f(k⁻¹x)`.

This file constructs that action separately on the real Schwartz and finite-adele Bruhat
factors, tensors the two actions, and proves the group, linearity, multiplication, and Real
covariance laws on the actual algebraic adelic core.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- Scaling labels for the rational adeles-class-space action. -/
structure CCMRationalAdelicScaling where
  val : CCMRationalUnit

/-- Scaling labels are canonically equivalent to nonzero rationals. -/
def ccmRationalAdelicScalingEquiv :
    CCMRationalAdelicScaling ≃ CCMRationalUnit where
  toFun := CCMRationalAdelicScaling.val
  invFun := CCMRationalAdelicScaling.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : CommGroup CCMRationalAdelicScaling :=
  ccmRationalAdelicScalingEquiv.commGroup

@[simp]
theorem ccmRationalAdelicScaling_one_val :
    (1 : CCMRationalAdelicScaling).val = 1 :=
  rfl

@[simp]
theorem ccmRationalAdelicScaling_mul_val
    (k l : CCMRationalAdelicScaling) :
    (k * l).val = k.val * l.val :=
  rfl

@[simp]
theorem ccmRationalAdelicScaling_inv_val
    (k : CCMRationalAdelicScaling) :
    k⁻¹.val = k.val⁻¹ :=
  rfl

/-! ## Archimedean factor -/

/-- A nonzero rational, viewed as a real unit. -/
def ccmRationalUnitReal (k : CCMRationalUnit) : ℝˣ :=
  Units.map (algebraMap ℚ ℝ) k

@[simp]
theorem ccmRationalUnitReal_val (k : CCMRationalUnit) :
    (ccmRationalUnitReal k : ℝ) = ((k : ℚ) : ℝ) :=
  rfl

/-- Pullback of a real Schwartz function by inverse rational scaling. -/
def ccmRationalArchimedeanScaling
    (k : CCMRationalAdelicScaling) :
    CCMRationalArchimedeanSchwartz →ₗ[ℂ]
      CCMRationalArchimedeanSchwartz :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft
      (ccmRationalUnitReal k.val⁻¹))).toLinearMap

@[simp]
theorem ccmRationalArchimedeanScaling_apply
    (k : CCMRationalAdelicScaling)
    (f : CCMRationalArchimedeanSchwartz) (x : ℝ) :
    ccmRationalArchimedeanScaling k f x =
      f ((((k.val⁻¹ : CCMRationalUnit) : ℚ) : ℝ) * x) :=
  rfl

theorem ccmRationalArchimedeanScaling_one
    (f : CCMRationalArchimedeanSchwartz) :
    ccmRationalArchimedeanScaling 1 f = f := by
  ext x
  simp

theorem ccmRationalArchimedeanScaling_mul
    (k l : CCMRationalAdelicScaling)
    (f : CCMRationalArchimedeanSchwartz) :
    ccmRationalArchimedeanScaling (k * l) f =
      ccmRationalArchimedeanScaling k
        (ccmRationalArchimedeanScaling l f) := by
  ext x
  simp only [ccmRationalArchimedeanScaling_apply,
    ccmRationalAdelicScaling_mul_val, mul_inv_rev]
  congr 1
  push_cast
  ring

theorem ccmRationalArchimedeanScaling_map_mul
    (k : CCMRationalAdelicScaling)
    (f g : CCMRationalArchimedeanSchwartz) :
    ccmRationalArchimedeanScaling k (f * g) =
      ccmRationalArchimedeanScaling k f *
        ccmRationalArchimedeanScaling k g := by
  ext x
  simp

theorem ccmRationalArchimedeanScaling_reflection
    (k : CCMRationalAdelicScaling)
    (f : CCMRationalArchimedeanSchwartz) :
    ccmRationalArchimedeanSchwartzReflection
        (ccmRationalArchimedeanScaling k f) =
      ccmRationalArchimedeanScaling k
        (ccmRationalArchimedeanSchwartzReflection f) := by
  ext x
  simp

/-! ## Finite-adele factor -/

/-- A nonzero rational, viewed as a unit of the finite adele ring. -/
def ccmRationalUnitFiniteAdele
    (k : CCMRationalUnit) : CCMRationalFiniteAdeleˣ :=
  Units.map (algebraMap ℚ CCMRationalFiniteAdele) k

@[simp]
theorem ccmRationalUnitFiniteAdele_val (k : CCMRationalUnit) :
    (ccmRationalUnitFiniteAdele k : CCMRationalFiniteAdele) =
      algebraMap ℚ CCMRationalFiniteAdele (k : ℚ) :=
  rfl

/-- Multiplication by a unit as a homeomorphism of a topological ring. -/
def ccmRationalFiniteAdeleUnitMulHomeomorph
    (u : CCMRationalFiniteAdeleˣ) :
    CCMRationalFiniteAdele ≃ₜ CCMRationalFiniteAdele where
  toFun x := (u : CCMRationalFiniteAdele) * x
  invFun x := (↑(u⁻¹) : CCMRationalFiniteAdele) * x
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

/-- Pullback of a finite-adele Bruhat function by inverse rational scaling. -/
def ccmRationalFiniteBruhatScaling
    (k : CCMRationalAdelicScaling)
    (f : CCMRationalFiniteBruhatSchwartz) :
    CCMRationalFiniteBruhatSchwartz :=
  let h := ccmRationalFiniteAdeleUnitMulHomeomorph
    (ccmRationalUnitFiniteAdele k.val⁻¹)
  ⟨LocallyConstant.comap ⟨h, h.continuous⟩ f.1,
    f.2.comp_homeomorph h⟩

@[simp]
theorem ccmRationalFiniteBruhatScaling_apply
    (k : CCMRationalAdelicScaling)
    (f : CCMRationalFiniteBruhatSchwartz)
    (x : CCMRationalFiniteAdele) :
    (ccmRationalFiniteBruhatScaling k f).1 x =
      f.1 (algebraMap ℚ CCMRationalFiniteAdele
        ((k.val⁻¹ : CCMRationalUnit) : ℚ) * x) :=
  rfl

theorem ccmRationalFiniteBruhatScaling_zero
    (k : CCMRationalAdelicScaling) :
    ccmRationalFiniteBruhatScaling k 0 = 0 := by
  apply Subtype.ext
  ext x
  simp

theorem ccmRationalFiniteBruhatScaling_add
    (k : CCMRationalAdelicScaling)
    (f g : CCMRationalFiniteBruhatSchwartz) :
    ccmRationalFiniteBruhatScaling k (f + g) =
      ccmRationalFiniteBruhatScaling k f +
        ccmRationalFiniteBruhatScaling k g := by
  apply Subtype.ext
  ext x
  simp

theorem ccmRationalFiniteBruhatScaling_smul
    (k : CCMRationalAdelicScaling) (z : ℂ)
    (f : CCMRationalFiniteBruhatSchwartz) :
    ccmRationalFiniteBruhatScaling k (z • f) =
      z • ccmRationalFiniteBruhatScaling k f := by
  apply Subtype.ext
  ext x
  simp

/-- Finite-adele inverse scaling, bundled linearly. -/
def ccmRationalFiniteBruhatScalingLinear
    (k : CCMRationalAdelicScaling) :
    CCMRationalFiniteBruhatSchwartz →ₗ[ℂ]
      CCMRationalFiniteBruhatSchwartz where
  toFun := ccmRationalFiniteBruhatScaling k
  map_add' := ccmRationalFiniteBruhatScaling_add k
  map_smul' := ccmRationalFiniteBruhatScaling_smul k

theorem ccmRationalFiniteBruhatScaling_one
    (f : CCMRationalFiniteBruhatSchwartz) :
    ccmRationalFiniteBruhatScaling 1 f = f := by
  apply Subtype.ext
  ext x
  simp

theorem ccmRationalFiniteBruhatScaling_mul
    (k l : CCMRationalAdelicScaling)
    (f : CCMRationalFiniteBruhatSchwartz) :
    ccmRationalFiniteBruhatScaling (k * l) f =
      ccmRationalFiniteBruhatScaling k
        (ccmRationalFiniteBruhatScaling l f) := by
  apply Subtype.ext
  ext x
  simp only [ccmRationalFiniteBruhatScaling_apply,
    ccmRationalAdelicScaling_mul_val, mul_inv_rev]
  congr 1
  rw [Units.val_mul, map_mul]
  ring

theorem ccmRationalFiniteBruhatScaling_map_mul
    (k : CCMRationalAdelicScaling)
    (f g : CCMRationalFiniteBruhatSchwartz) :
    ccmRationalFiniteBruhatScaling k (f * g) =
      ccmRationalFiniteBruhatScaling k f *
        ccmRationalFiniteBruhatScaling k g := by
  apply Subtype.ext
  ext x
  simp

theorem ccmRationalFiniteBruhatScaling_reflection
    (k : CCMRationalAdelicScaling)
    (f : CCMRationalFiniteBruhatSchwartz) :
    ccmRationalFiniteBruhatReflection
        (ccmRationalFiniteBruhatScaling k f) =
      ccmRationalFiniteBruhatScaling k
        (ccmRationalFiniteBruhatReflection f) := by
  apply Subtype.ext
  ext x
  simp

/-! ## Tensor-core action -/

/-- Diagonal inverse scaling on the actual adelic tensor core. -/
def ccmRationalAdelicBruhatScaling
    (k : CCMRationalAdelicScaling) :
    CCMRationalAdelicBruhatSimpleTensor →ₗ[ℂ]
      CCMRationalAdelicBruhatSimpleTensor :=
  TensorProduct.map
    (ccmRationalArchimedeanScaling k)
    (ccmRationalFiniteBruhatScalingLinear k)

@[simp]
theorem ccmRationalAdelicBruhatScaling_tmul
    (k : CCMRationalAdelicScaling)
    (f : CCMRationalArchimedeanSchwartz)
    (g : CCMRationalFiniteBruhatSchwartz) :
    ccmRationalAdelicBruhatScaling k (f ⊗ₜ[ℂ] g) =
      ccmRationalArchimedeanScaling k f ⊗ₜ[ℂ]
        ccmRationalFiniteBruhatScaling k g :=
  rfl

instance : SMul CCMRationalAdelicScaling
    CCMRationalAdelicBruhatSimpleTensor where
  smul k x := ccmRationalAdelicBruhatScaling k x

@[simp]
theorem ccmRationalAdelicScaling_smul_tmul
    (k : CCMRationalAdelicScaling)
    (f : CCMRationalArchimedeanSchwartz)
    (g : CCMRationalFiniteBruhatSchwartz) :
    k • (f ⊗ₜ[ℂ] g : CCMRationalAdelicBruhatSimpleTensor) =
      ccmRationalArchimedeanScaling k f ⊗ₜ[ℂ]
        ccmRationalFiniteBruhatScaling k g :=
  rfl

instance : DistribMulAction CCMRationalAdelicScaling
    CCMRationalAdelicBruhatSimpleTensor where
  smul_zero k := map_zero (ccmRationalAdelicBruhatScaling k)
  smul_add k := map_add (ccmRationalAdelicBruhatScaling k)
  one_smul x := by
    change ccmRationalAdelicBruhatScaling 1 x = x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul f g =>
        rw [ccmRationalAdelicBruhatScaling_tmul,
          ccmRationalArchimedeanScaling_one,
          ccmRationalFiniteBruhatScaling_one]
    | add x y hx hy => rw [map_add, hx, hy]
  mul_smul k l x := by
    change ccmRationalAdelicBruhatScaling (k * l) x =
      ccmRationalAdelicBruhatScaling k
        (ccmRationalAdelicBruhatScaling l x)
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul f g =>
        rw [ccmRationalAdelicBruhatScaling_tmul,
          ccmRationalAdelicBruhatScaling_tmul,
          ccmRationalAdelicBruhatScaling_tmul,
          ccmRationalArchimedeanScaling_mul,
          ccmRationalFiniteBruhatScaling_mul]
    | add x y hx hy =>
        rw [map_add, map_add, map_add, hx, hy]

/-- Rational inverse scaling preserves the nonunital adelic product. -/
theorem ccmRationalAdelicBruhatScaling_map_mul
    (k : CCMRationalAdelicScaling)
    (x y : CCMRationalAdelicBruhatSimpleTensor) :
    k • (x * y) = (k • x) * (k • y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul f' g' =>
          rw [ccmRationalAdelicBruhat_tmul_mul_tmul,
            ccmRationalAdelicScaling_smul_tmul,
            ccmRationalAdelicScaling_smul_tmul,
            ccmRationalAdelicScaling_smul_tmul,
            ccmRationalAdelicBruhat_tmul_mul_tmul,
            ccmRationalArchimedeanScaling_map_mul,
            ccmRationalFiniteBruhatScaling_map_mul]
      | add y₁ y₂ hy₁ hy₂ =>
          rw [ccmRationalAdelicBruhat_mul_add, smul_add, smul_add,
            ccmRationalAdelicBruhat_mul_add, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ =>
      rw [ccmRationalAdelicBruhat_add_mul, smul_add, smul_add,
        ccmRationalAdelicBruhat_add_mul, hx₁, hx₂]

/-- Rational inverse scaling commutes with the adelic sign-conjugation Real structure. -/
theorem ccmRationalAdelicBruhatScaling_sigma
    (k : CCMRationalAdelicScaling)
    (x : CCMRationalAdelicBruhatSimpleTensor) :
    ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma (k • x) =
      k • ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      rw [ccmRationalAdelicScaling_smul_tmul,
        ccmRationalAdelicBruhatSimpleTensor_sigma_tmul,
        ccmRationalAdelicBruhatSimpleTensor_sigma_tmul,
        ccmRationalAdelicScaling_smul_tmul,
        ccmRationalArchimedeanScaling_reflection,
        ccmRationalFiniteBruhatScaling_reflection]
  | add x y hx hy => simp [hx, hy]

end RHTower
end GaloisForLFunctions
