import GaloisForLFunctions.HTGeometry.GaussianSchwartz
import GaloisForLFunctions.HTGeometry.SampledSmallComplex
import GaloisForLFunctions.HTGeometry.WeylCharacterGenerator
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Archimedean spherical exponents act faithfully on Schwartz space

The real additive character `x ↦ exp (-i x)` and all its multiplicative
shifts have temperate growth.  Multiplication by the shifted phase therefore
defines a continuous endomorphism of `SchwartzMap ℝ ℂ`.

These multipliers turn addition of exponents into composition, have inverse
given by negating the exponent, and separate all real exponents.  The
faithfulness proof tests operator equality on the nowhere-zero Gaussian.

This is the archimedean component of the semilocal spherical-to-Weyl bridge.
Finite-place Bruhat--Schwartz preservation, finite-product assembly, and
`L²` unitarity remain separate theorems.
-/

open Complex Function
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry.FieldOneCore

noncomputable section

/-- Unit-modulus phase with real exponent `h`. -/
def fieldOneArchimedeanPhase (h x : ℝ) : ℂ :=
  HTGeometry.scalarWeylCharacter h (x : ℂ)

/-- Every shifted archimedean phase has temperate growth, so it acts
continuously on Schwartz space by multiplication. -/
theorem fieldOneArchimedeanPhase_hasTemperateGrowth (h : ℝ) :
    Function.HasTemperateGrowth (fieldOneArchimedeanPhase h) := by
  let c : ℂ := -Complex.I * (h : ℂ)
  let H : ℂ → ℂ := fun z => Complex.exp (c * z)
  have hH : Differentiable ℂ H := by
    dsimp only [H]
    fun_prop
  refine ⟨HTGeometry.contDiff_comp_ofReal hH, fun n => ?_⟩
  refine ⟨0, ‖c‖ ^ n, fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖iteratedDeriv n (fun y : ℝ => H (y : ℂ)) x‖ ≤ _
  rw [congrFun (HTGeometry.iteratedDeriv_comp_ofReal n hH) x]
  change
    ‖iteratedDeriv n (fun z : ℂ => Complex.exp (c * z)) (x : ℂ)‖ ≤ _
  rw [congrFun (iteratedDeriv_cexp_const_mul n c) (x : ℂ)]
  rw [norm_mul, norm_pow, Complex.norm_exp]
  simp [c]

theorem fieldOneArchimedeanPhase_add (h k : ℝ) :
    fieldOneArchimedeanPhase (h + k) =
      fieldOneArchimedeanPhase h * fieldOneArchimedeanPhase k := by
  funext x
  exact HTGeometry.scalarWeylCharacter_add_charge h k (x : ℂ)

@[simp]
theorem norm_fieldOneArchimedeanPhase (h x : ℝ) :
    ‖fieldOneArchimedeanPhase h x‖ = 1 :=
  HTGeometry.norm_scalarWeylCharacter_ofReal h x

@[simp]
theorem fieldOneArchimedeanPhase_zero :
    fieldOneArchimedeanPhase 0 = 1 := by
  funext x
  simp [fieldOneArchimedeanPhase, HTGeometry.scalarWeylCharacter]

/-- Natural multiples of an exponent become pointwise powers of its phase. -/
theorem fieldOneArchimedeanPhase_nsmul (n : ℕ) (h : ℝ) :
    fieldOneArchimedeanPhase (n • h) =
      fieldOneArchimedeanPhase h ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, fieldOneArchimedeanPhase_add, ih, pow_succ]

/-- Any specified additive root gives the exact Frobenius root law for
archimedean phases. -/
theorem fieldOneArchimedeanPhase_root
    {r h : ℝ} {n : ℕ} (hr : n • r = h) :
    fieldOneArchimedeanPhase r ^ n =
      fieldOneArchimedeanPhase h := by
  rw [← fieldOneArchimedeanPhase_nsmul, hr]

/-- Standard nontrivial archimedean additive character. -/
def fieldOneArchimedeanCharacter : AddChar ℝ ℂ where
  toFun := fieldOneArchimedeanPhase 1
  map_zero_eq_one' := by
    simp [fieldOneArchimedeanPhase, HTGeometry.scalarWeylCharacter]
  map_add_eq_mul' x y := by
    simp only [fieldOneArchimedeanPhase,
      HTGeometry.scalarWeylCharacter]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- The standard character is nontrivial, witnessed at `π`. -/
theorem fieldOneArchimedeanCharacter_ne_one :
    fieldOneArchimedeanCharacter ≠ 1 := by
  intro h
  have hpi := DFunLike.congr_fun h Real.pi
  have hpi' : Complex.exp (-Complex.I * (Real.pi : ℂ)) = 1 := by
    simpa [fieldOneArchimedeanCharacter, fieldOneArchimedeanPhase,
      HTGeometry.scalarWeylCharacter] using hpi
  have harg :
      -Complex.I * (Real.pi : ℂ) =
        -((Real.pi : ℂ) * Complex.I) := by
    ring
  rw [harg, Complex.exp_neg_pi_mul_I] at hpi'
  norm_num at hpi'

/-- Phase at exponent `h` is the multiplicative shift of the standard
additive character by `h`. -/
theorem fieldOneArchimedeanPhase_eq_mulShift (h : ℝ) :
    fieldOneArchimedeanPhase h =
      AddChar.mulShift fieldOneArchimedeanCharacter h := by
  funext x
  simp only [fieldOneArchimedeanPhase,
    HTGeometry.scalarWeylCharacter, AddChar.mulShift_apply,
    fieldOneArchimedeanCharacter]
  congr 1
  push_cast
  ring

/-- Continuous Weyl multiplier on real Schwartz space. -/
def fieldOneArchimedeanWeylMultiplier (h : ℝ) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fieldOneArchimedeanPhase h)

@[simp]
theorem fieldOneArchimedeanWeylMultiplier_apply
    (h : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    fieldOneArchimedeanWeylMultiplier h f x =
      fieldOneArchimedeanPhase h x * f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply
    (fieldOneArchimedeanPhase_hasTemperateGrowth h) f x

/-- Addition of exponents is composition of Schwartz multipliers. -/
theorem fieldOneArchimedeanWeylMultiplier_add (h k : ℝ) :
    fieldOneArchimedeanWeylMultiplier h ∘L
        fieldOneArchimedeanWeylMultiplier k =
      fieldOneArchimedeanWeylMultiplier (h + k) := by
  rw [fieldOneArchimedeanWeylMultiplier,
    fieldOneArchimedeanWeylMultiplier,
    SchwartzMap.smulLeftCLM_compL_smulLeftCLM
      (fieldOneArchimedeanPhase_hasTemperateGrowth h)
      (fieldOneArchimedeanPhase_hasTemperateGrowth k)]
  rw [fieldOneArchimedeanWeylMultiplier,
    fieldOneArchimedeanPhase_add]

@[simp]
theorem fieldOneArchimedeanWeylMultiplier_zero :
    fieldOneArchimedeanWeylMultiplier 0 =
      ContinuousLinearMap.id ℂ _ := by
  ext f x
  simp [fieldOneArchimedeanWeylMultiplier_apply,
    fieldOneArchimedeanPhase_zero]

theorem fieldOneArchimedeanWeylMultiplier_neg_left (h : ℝ) :
    fieldOneArchimedeanWeylMultiplier (-h) ∘L
        fieldOneArchimedeanWeylMultiplier h =
      ContinuousLinearMap.id ℂ _ := by
  rw [fieldOneArchimedeanWeylMultiplier_add, neg_add_cancel,
    fieldOneArchimedeanWeylMultiplier_zero]

theorem fieldOneArchimedeanWeylMultiplier_neg_right (h : ℝ) :
    fieldOneArchimedeanWeylMultiplier h ∘L
        fieldOneArchimedeanWeylMultiplier (-h) =
      ContinuousLinearMap.id ℂ _ := by
  rw [fieldOneArchimedeanWeylMultiplier_add, add_neg_cancel,
    fieldOneArchimedeanWeylMultiplier_zero]

/-- Distinct real exponents induce distinct continuous Schwartz
multipliers. -/
theorem fieldOneArchimedeanWeylMultiplier_injective :
    Function.Injective fieldOneArchimedeanWeylMultiplier := by
  intro h k heq
  have hchar :
      AddChar.mulShift fieldOneArchimedeanCharacter h =
        AddChar.mulShift fieldOneArchimedeanCharacter k := by
    apply AddChar.ext
    intro x
    rw [← congrFun (fieldOneArchimedeanPhase_eq_mulShift h) x,
      ← congrFun (fieldOneArchimedeanPhase_eq_mulShift k) x]
    have hx := congrArg
      (fun T : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ =>
        T GaloisForLFunctions.gaussianSchwartz x) heq
    simp only [fieldOneArchimedeanWeylMultiplier_apply] at hx
    have hg :
        ((GaloisForLFunctions.gaussReal x : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (GaloisForLFunctions.gaussReal_pos x).ne'
    exact mul_right_cancel₀ hg hx
  exact
    (AddChar.to_mulShift_inj_of_isPrimitive
      (AddChar.IsPrimitive.of_ne_one
        fieldOneArchimedeanCharacter_ne_one)) hchar

end

end GaloisForLFunctions.HTGeometry.FieldOneCore
