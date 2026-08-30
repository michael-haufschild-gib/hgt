import GaloisForLFunctions.RHTower.CCMRationalAdelicCrossedProduct

/-!
# The fixed-point endpoint trace on the rational CCM source

This file constructs the first Connes--Consani--Marcolli endpoint functional on the actual
algebraic adeles-class-space crossed product.  On a coefficient tensor it is evaluation at the
zero adele; on the crossed product it reads only the coefficient of the identity scaling; and on
the minimal unitization it sends the adjoined unit to one.

The central point is the trace law.  Zero is fixed by every rational scaling, so evaluation at
zero is a scaling-invariant character of the Bruhat tensor core.  The identity coefficient of
twisted convolution therefore gives a trace even though it is not a character of the crossed
product.  No completion, Haar measure, spectral premise, or quotient surrogate is used.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

private abbrev Arch := CCMRationalArchimedeanSchwartz
private abbrev FinBruhat := CCMRationalFiniteBruhatSchwartz
private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Scale := CCMRationalAdelicScaling
private abbrev Crossed := CCMRationalAdelicAlgebraicCrossedProduct
private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra

local instance cCMRationalAdelicEpsilonZeroLocalInst1 : DecidableEq Scale := Classical.decEq _

/-! ## Evaluation at the zero adele -/

/-- Bilinear zero-adele evaluation on the two Bruhat factors. -/
def ccmRationalAdelicBruhatZeroEvalBilinear :
    Arch →ₗ[ℂ] FinBruhat →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun := fun φ ↦ f 0 * φ.1 0
      map_add' := by
        intro φ ψ
        simp [mul_add]
      map_smul' := by
        intro z φ
        simp
        ring }
  map_add' := by
    intro f g
    ext φ
    simp [add_mul]
  map_smul' := by
    intro z f
    ext φ
    simp
    ring

/-- Evaluation of an arbitrary algebraic adelic Bruhat tensor at the zero adele. -/
def ccmRationalAdelicBruhatZeroEval : Core →ₗ[ℂ] ℂ :=
  TensorProduct.lift ccmRationalAdelicBruhatZeroEvalBilinear

@[simp]
theorem ccmRationalAdelicBruhatZeroEval_tmul (f : Arch) (φ : FinBruhat) :
    ccmRationalAdelicBruhatZeroEval (f ⊗ₜ[ℂ] φ) = f 0 * φ.1 0 :=
  rfl

/-- Zero-adele evaluation is multiplicative on the genuine adelic tensor core. -/
theorem ccmRationalAdelicBruhatZeroEval_mul (x y : Core) :
    ccmRationalAdelicBruhatZeroEval (x * y) =
      ccmRationalAdelicBruhatZeroEval x *
        ccmRationalAdelicBruhatZeroEval y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f φ =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul g ψ =>
          simp only [ccmRationalAdelicBruhat_tmul_mul_tmul,
            ccmRationalAdelicBruhatZeroEval_tmul,
            ccmRationalArchimedeanSchwartz_mul_apply,
            ccmRationalFiniteBruhat_mul_apply]
          ring
      | add y₁ y₂ hy₁ hy₂ =>
          rw [ccmRationalAdelicBruhat_mul_add, map_add, map_add,
            hy₁, hy₂, mul_add]
  | add x₁ x₂ hx₁ hx₂ =>
      rw [ccmRationalAdelicBruhat_add_mul, map_add, map_add,
        hx₁, hx₂, add_mul]

/-- Every diagonal rational inverse scaling fixes zero-adele evaluation. -/
theorem ccmRationalAdelicBruhatZeroEval_smul (k : Scale) (x : Core) :
    ccmRationalAdelicBruhatZeroEval (k • x) =
      ccmRationalAdelicBruhatZeroEval x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f φ =>
      simp only [ccmRationalAdelicScaling_smul_tmul,
        ccmRationalAdelicBruhatZeroEval_tmul,
        ccmRationalArchimedeanScaling_apply,
        ccmRationalFiniteBruhatScaling_apply, mul_zero]
  | add x y hx hy =>
      rw [smul_add, map_add, map_add, hx, hy]

/-! ## Identity-coefficient trace on the crossed product -/

/-- The nonunital CCM fixed-point trace: evaluate the identity-scaling coefficient at zero. -/
def ccmRationalAdelicEpsilonZeroNonunital : Crossed →ₗ[ℂ] ℂ where
  toFun F := ccmRationalAdelicBruhatZeroEval (F 1)
  map_add' F H := by simp
  map_smul' z F := by simp

@[simp]
theorem ccmRationalAdelicEpsilonZeroNonunital_single
    (k : Scale) (a : Core) :
    ccmRationalAdelicEpsilonZeroNonunital (Finsupp.single k a) =
      if k = 1 then ccmRationalAdelicBruhatZeroEval a else 0 := by
  by_cases hk : k = 1
  · subst k
    simp [ccmRationalAdelicEpsilonZeroNonunital]
  · have hk' : (1 : Scale) ≠ k := fun h ↦ hk h.symm
    simp [ccmRationalAdelicEpsilonZeroNonunital, hk, hk']

/-- The identity-coefficient zero-evaluation functional is a trace on twisted convolution. -/
theorem ccmRationalAdelicEpsilonZeroNonunital_isTrace (F H : Crossed) :
    ccmRationalAdelicEpsilonZeroNonunital (F * H) =
      ccmRationalAdelicEpsilonZeroNonunital (H * F) := by
  classical
  have hpure (k l : Scale) (a b : Core) :
      ccmRationalAdelicEpsilonZeroNonunital
          (Finsupp.single k a * Finsupp.single l b) =
        ccmRationalAdelicEpsilonZeroNonunital
          (Finsupp.single l b * Finsupp.single k a) := by
    by_cases hkl : k * l = 1
    · have hlk : l * k = 1 := by
        calc
          l * k = l * (k * l) * l⁻¹ := by simp [mul_assoc]
          _ = 1 := by rw [hkl]; simp
      simp [ccmRationalAdelicCrossedProduct_single_mul_single,
        hkl, hlk, ccmRationalAdelicBruhatZeroEval_mul,
        ccmRationalAdelicBruhatZeroEval_smul, mul_comm]
    · have hlk : l * k ≠ 1 := by
        intro h
        apply hkl
        calc
          k * l = k * (l * k) * k⁻¹ := by simp [mul_assoc]
          _ = 1 := by rw [h]; simp
      simp [ccmRationalAdelicCrossedProduct_single_mul_single, hkl, hlk]
  have hpureLeft (k : Scale) (a : Core) (J : Crossed) :
      ccmRationalAdelicEpsilonZeroNonunital (Finsupp.single k a * J) =
        ccmRationalAdelicEpsilonZeroNonunital (J * Finsupp.single k a) := by
    induction J using Finsupp.induction with
    | zero => simp
    | @single_add l b J hl hb hJ =>
        rw [ccmRationalAdelicCrossedProduct_mul_add,
          ccmRationalAdelicCrossedProduct_add_mul, map_add, map_add,
          hpure, hJ]
  induction F using Finsupp.induction with
  | zero => simp
  | @single_add k a F hk ha hF =>
      rw [ccmRationalAdelicCrossedProduct_add_mul,
        ccmRationalAdelicCrossedProduct_mul_add, map_add, map_add,
        hpureLeft, hF]

/-! ## Normalized trace on the minimal unitization -/

/-- First CCM endpoint functional on the cyclic source algebra, normalized by `ε₀(1)=1`. -/
def ccmRationalAdelicEpsilonZero : Source →ₗ[ℂ] ℂ where
  toFun x := x.fst + ccmRationalAdelicEpsilonZeroNonunital x.snd
  map_add' x y := by
    simp only [Unitization.fst_add, Unitization.snd_add, map_add]
    ring
  map_smul' z x := by
    simp only [Unitization.fst_smul, Unitization.snd_smul, map_smul,
      smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem ccmRationalAdelicEpsilonZero_one :
    ccmRationalAdelicEpsilonZero (1 : Source) = 1 := by
  simp [ccmRationalAdelicEpsilonZero]

@[simp]
theorem ccmRationalAdelicEpsilonZero_inr (F : Crossed) :
    ccmRationalAdelicEpsilonZero (F : Source) =
      ccmRationalAdelicEpsilonZeroNonunital F := by
  simp [ccmRationalAdelicEpsilonZero]

/-- The normalized first CCM endpoint functional is a trace on the unitized source. -/
theorem ccmRationalAdelicEpsilonZero_isTrace (x y : Source) :
    ccmRationalAdelicEpsilonZero (x * y) =
      ccmRationalAdelicEpsilonZero (y * x) := by
  change (x * y).fst + ccmRationalAdelicEpsilonZeroNonunital (x * y).snd =
    (y * x).fst + ccmRationalAdelicEpsilonZeroNonunital (y * x).snd
  rw [Unitization.fst_mul, Unitization.fst_mul,
    Unitization.snd_mul, Unitization.snd_mul]
  simp only [map_add, map_smul, smul_eq_mul]
  rw [ccmRationalAdelicEpsilonZeroNonunital_isTrace x.snd y.snd]
  ring

end RHTower
end GaloisForLFunctions
