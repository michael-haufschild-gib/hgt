import GaloisForLFunctions.RHTower.Suzuki.SuzukiPrimeFreeScaledCoercivity

/-!
# Exact scaling bridge for Suzuki's restricted Weil form

This module proves the change-of-variables step behind Suzuki (4.2)--(4.5) on the literal smooth
source core.  For a prime-free aperture `a`, rescaling `u(x)` to `u(x/a)` identifies `(1/a)` times
the exact restricted Weil form with the fixed-interval prime-free numerator.  Thus the quantitative
coercivity theorem is about the actual source form, not merely a formula-shaped proxy.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Pull a unit-aperture real source core back to aperture `a`. -/
def suzukiRescaledCore (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilCore 1) : SuzukiRestrictedWeilCore a.val where
  toFun x := u (x / a.val)
  smooth := u.smooth.comp (contDiff_id.div_const a.val)
  supportRadius := a.val * u.supportRadius
  supportRadius_nonneg := mul_nonneg a.pos.le u.supportRadius_nonneg
  supportRadius_lt_aperture := by
    nlinarith [mul_lt_mul_of_pos_left u.supportRadius_lt_aperture a.pos]
  support_subset := by
    intro x hx
    have hxu : x / a.val ∈ Icc (-u.supportRadius) u.supportRadius := u.support_subset hx
    constructor
    · calc
        -(a.val * u.supportRadius) = a.val * (-u.supportRadius) := by ring
        _ ≤ a.val * (x / a.val) := mul_le_mul_of_nonneg_left hxu.1 a.pos.le
        _ = x := mul_div_cancel₀ x a.pos.ne'
    · calc
        x = a.val * (x / a.val) := (mul_div_cancel₀ x a.pos.ne').symm
        _ ≤ a.val * u.supportRadius := mul_le_mul_of_nonneg_left hxu.2 a.pos.le

@[simp] theorem suzukiRescaledCore_apply (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilCore 1) (x : ℝ) :
    suzukiRescaledCore a u x = u (x / a.val) := rfl

theorem suzukiRescaledCore_intervalEnergy (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilCore 1) :
    (∫ x in (-a.val)..a.val, (suzukiRescaledCore a u x) ^ (2 : ℕ)) =
      a.val * ∫ x in (-1 : ℝ)..1, u x ^ (2 : ℕ) := by
  have h := intervalIntegral.integral_comp_div (fun x => u x ^ (2 : ℕ)) a.pos.ne'
    (a := -a.val) (b := a.val)
  simpa [suzukiRescaledCore, smul_eq_mul, a.pos.ne'] using h

private theorem iterated_interval_scale (a : SuzukiPrimeFreeSmallAperture)
    (F : ℝ → ℝ → ℝ) :
    (∫ x in (-a.val)..a.val,
      ∫ y in (-a.val)..a.val, F (x / a.val) (y / a.val)) =
      a.val ^ (2 : ℕ) * ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, F x y := by
  have hinner : ∀ x : ℝ,
      (∫ y in (-a.val)..a.val, F (x / a.val) (y / a.val)) =
        a.val * ∫ y in (-1 : ℝ)..1, F (x / a.val) y := by
    intro x
    have h := intervalIntegral.integral_comp_div (F (x / a.val)) a.pos.ne'
      (a := -a.val) (b := a.val)
    convert h using 1
    all_goals simp [smul_eq_mul, a.pos.ne']
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul]
  have hout := intervalIntegral.integral_comp_div
    (fun x => ∫ y in (-1 : ℝ)..1, F x y) a.pos.ne'
    (a := -a.val) (b := a.val)
  rw [hout]
  simp [smul_eq_mul, a.pos.ne']
  ring

theorem suzukiRescaledDifferenceEnergy (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilCore 1) :
    suzukiFinitePartDifferenceEnergy a.val (suzukiRescaledCore a u) =
      a.val * suzukiFinitePartDifferenceEnergy 1 u := by
  let F : ℝ → ℝ → ℝ := fun x y => (u x - u y) ^ (2 : ℕ) * |x - y|⁻¹
  have hpoint : ∀ x y : ℝ,
      (suzukiRescaledCore a u x - suzukiRescaledCore a u y) ^ (2 : ℕ) * |x - y|⁻¹ =
        (1 / a.val) * F (x / a.val) (y / a.val) := by
    intro x y
    rcases eq_or_ne x y with rfl | hxy
    · simp [F]
    · dsimp [suzukiRescaledCore, F]
      rw [show x / a.val - y / a.val = (x - y) / a.val by ring,
        abs_div, abs_of_pos a.pos]
      field_simp [a.pos.ne']
  have hscale := iterated_interval_scale a F
  unfold suzukiFinitePartDifferenceEnergy
  calc
    (∫ x in (-a.val)..a.val, ∫ y in (-a.val)..a.val,
        (suzukiRescaledCore a u x - suzukiRescaledCore a u y) ^ (2 : ℕ) * |x - y|⁻¹) =
        ∫ x in (-a.val)..a.val, ∫ y in (-a.val)..a.val,
          (1 / a.val) * F (x / a.val) (y / a.val) := by
            refine intervalIntegral.integral_congr fun x _ => ?_
            exact intervalIntegral.integral_congr fun y _ => hpoint x y
    _ = (1 / a.val) *
        (∫ x in (-a.val)..a.val,
          ∫ y in (-a.val)..a.val, F (x / a.val) (y / a.val)) := by
            simp_rw [intervalIntegral.integral_const_mul]
    _ = a.val * ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, F x y := by
          rw [hscale]
          field_simp
    _ = a.val * suzukiFinitePartDifferenceEnergy 1 u := rfl

theorem suzukiRescaledLogPotential (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilCore 1) :
    suzukiFinitePartLogPotential a.val (suzukiRescaledCore a u) =
      a.val * (2 * Real.log a.val * (∫ x in (-1 : ℝ)..1, u x ^ (2 : ℕ)) +
        suzukiFinitePartLogPotential 1 u) := by
  let f : ℝ → ℝ := fun x =>
    Real.log (a.val ^ (2 : ℕ) - (a.val * x) ^ (2 : ℕ)) * u x ^ (2 : ℕ)
  have hscale := intervalIntegral.integral_comp_div f a.pos.ne'
    (a := -a.val) (b := a.val)
  have hleft : (∫ x in (-a.val)..a.val,
      Real.log (a.val ^ (2 : ℕ) - x ^ (2 : ℕ)) * (suzukiRescaledCore a u x) ^ (2 : ℕ)) =
      a.val * ∫ x in (-1 : ℝ)..1, f x := by
    convert hscale using 1
    · apply intervalIntegral.integral_congr
      intro x _
      dsimp [f, suzukiRescaledCore]
      rw [mul_div_cancel₀ x a.pos.ne']
    · simp [smul_eq_mul, a.pos.ne']
  have hpoint : ∀ x : ℝ,
      f x = 2 * Real.log a.val * u x ^ (2 : ℕ) +
        Real.log (1 - x ^ (2 : ℕ)) * u x ^ (2 : ℕ) := by
    intro x
    by_cases hux : u x = 0
    · simp [f, hux]
    · have hxap := u.support_subset_aperture hux
      have harg : 0 < 1 - x ^ (2 : ℕ) := by
        have hp : 0 < (1 - x) * (1 + x) :=
          mul_pos (by linarith [hxap.2]) (by linarith [hxap.1])
        nlinarith
      have hfactor : a.val ^ (2 : ℕ) - (a.val * x) ^ (2 : ℕ) =
          a.val ^ (2 : ℕ) * (1 - x ^ (2 : ℕ)) := by ring
      dsimp [f]
      rw [hfactor, Real.log_mul (pow_ne_zero 2 a.pos.ne') harg.ne', Real.log_pow]
      ring
  unfold suzukiFinitePartLogPotential
  rw [hleft]
  apply congrArg (fun z : ℝ => a.val * z)
  calc
    (∫ x in (-1 : ℝ)..1, f x) =
        ∫ x in (-1 : ℝ)..1,
          2 * Real.log a.val * u x ^ (2 : ℕ) + Real.log (1 - x ^ (2 : ℕ)) * u x ^ (2 : ℕ) := by
            exact intervalIntegral.integral_congr fun x _ => hpoint x
    _ = 2 * Real.log a.val * (∫ x in (-1 : ℝ)..1, u x ^ (2 : ℕ)) +
        ∫ x in (-1 : ℝ)..1, Real.log (1 - x ^ (2 : ℕ)) * u x ^ (2 : ℕ) := by
          have hlog := suzukiFinitePartLogPotential_integrable_upper
            (a := (1 : ℝ)) one_pos u.supportRadius_nonneg u.supportRadius_lt_aperture
              u.continuous u.support_subset
          have hlogI : IntervalIntegrable
              (fun x => Real.log (1 - x ^ (2 : ℕ)) * u x ^ (2 : ℕ)) volume (-1 : ℝ) 1 := by
            simpa using hlog.1
          have hfirstI : IntervalIntegrable
              (fun x => 2 * Real.log a.val * u x ^ (2 : ℕ)) volume (-1 : ℝ) 1 :=
            (continuous_const.mul (u.continuous.pow 2)).intervalIntegrable _ _
          rw [intervalIntegral.integral_add hfirstI hlogI,
            intervalIntegral.integral_const_mul]
    _ = _ := by ring

theorem suzukiRescaledFinitePartEnergy (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilCore 1) :
    suzukiFinitePartEnergy a.val (suzukiRescaledCore a u) =
      a.val * (-Real.log a.val * (∫ x in (-1 : ℝ)..1, u x ^ (2 : ℕ)) +
        suzukiFinitePartEnergy 1 u) := by
  rw [suzukiFinitePartEnergy, suzukiRescaledDifferenceEnergy, suzukiRescaledLogPotential]
  unfold suzukiFinitePartEnergy
  ring

theorem suzukiRescaledSmoothBlock (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilCore 1) :
    (1 / a.val) * weilSmoothBlock a.val suzukiOriginRemainderCurvature
        (suzukiRescaledCore a u) (suzukiRescaledCore a u) =
      -a.val * suzukiScaledRemainderQuadraticReal a u := by
  let F : ℝ → ℝ → ℝ := fun x y =>
    suzukiOriginRemainderCurvature (a.val * (x - y)) * u y * u x
  have hpoint : ∀ x y : ℝ,
      suzukiOriginRemainderCurvature (x - y) *
          suzukiRescaledCore a u y * suzukiRescaledCore a u x =
        F (x / a.val) (y / a.val) := by
    intro x y
    dsimp [F, suzukiRescaledCore]
    congr 1
    congr 1
    rw [show x / a.val - y / a.val = (x - y) / a.val by ring,
      mul_div_cancel₀ (x - y) a.pos.ne']
  have hscale := iterated_interval_scale a F
  have hquad :
      (∫ x in (-a.val)..a.val,
        (∫ y in (-a.val)..a.val,
          suzukiOriginRemainderCurvature (x - y) * suzukiRescaledCore a u y) *
            suzukiRescaledCore a u x) =
        a.val ^ (2 : ℕ) * suzukiScaledRemainderQuadraticReal a u := by
    calc
      _ = ∫ x in (-a.val)..a.val, ∫ y in (-a.val)..a.val,
          suzukiOriginRemainderCurvature (x - y) *
            suzukiRescaledCore a u y * suzukiRescaledCore a u x := by
          refine intervalIntegral.integral_congr fun x _ => ?_
          rw [intervalIntegral.integral_mul_const]
      _ = ∫ x in (-a.val)..a.val,
          ∫ y in (-a.val)..a.val, F (x / a.val) (y / a.val) := by
          refine intervalIntegral.integral_congr fun x _ => ?_
          exact intervalIntegral.integral_congr fun y _ => hpoint x y
      _ = a.val ^ (2 : ℕ) * ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, F x y := hscale
      _ = a.val ^ (2 : ℕ) * suzukiScaledRemainderQuadraticReal a u := by
        apply congrArg (fun z : ℝ => a.val ^ (2 : ℕ) * z)
        unfold suzukiScaledRemainderQuadraticReal
        refine intervalIntegral.integral_congr fun x _ => ?_
        rw [intervalIntegral.integral_mul_const]
  rw [weilSmoothBlock, hquad]
  field_simp

theorem suzukiRescaledScalarBlock (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilCore 1) :
    (1 / a.val) * weilScalarBlock a.val suzukiWeilArchimedeanConstant
        (suzukiRescaledCore a u) (suzukiRescaledCore a u) =
      -(2 * suzukiWeilArchimedeanConstant + 1) *
        ∫ x in (-1 : ℝ)..1, u x ^ (2 : ℕ) := by
  rw [weilScalarBlock]
  have henergy := suzukiRescaledCore_intervalEnergy a u
  have henergy' : (∫ x in (-a.val)..a.val,
      suzukiRescaledCore a u x * suzukiRescaledCore a u x) =
      a.val * ∫ x in (-1 : ℝ)..1, u x ^ (2 : ℕ) := by
    simpa [pow_two] using henergy
  rw [henergy']
  field_simp [a.pos.ne']

/-- Exact real scaling identity for Suzuki's literal restricted Weil source form. -/
theorem suzukiRescaledRestrictedWeilForm_eq (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilCore 1) :
    (1 / a.val) * suzukiRestrictedWeilForm a.val
        (suzukiRescaledCore a u) (suzukiRescaledCore a u) =
      suzukiPrimeFreeScaledRealForm a u := by
  let pa : RHTower.SuzukiPositiveAperture := ⟨a.val, a.pos⟩
  have hfinite := suzukiWeilFinitePartBlock_eq_energy pa (suzukiRescaledCore a u)
  have hfs := suzukiRescaledFinitePartEnergy a u
  have hscalar := suzukiRescaledScalarBlock a u
  have hsmooth := suzukiRescaledSmoothBlock a u
  rw [suzukiRestrictedWeilForm_eq_originRemainderFourBlocks,
    suzukiRestrictedWeilIndices_eq_empty, hfinite]
  simp only [weilPrimeBlock, Finset.sum_empty, neg_zero, add_zero]
  unfold suzukiPrimeFreeScaledRealForm
  rw [mul_add, mul_add, hfs, hscalar, hsmooth]
  field_simp [a.pos.ne']
  ring

/-- Literal complex source form evaluated on the rescaled real and imaginary test cores. -/
def suzukiRescaledComplexSourceForm (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilComplexTest 1) : ℝ :=
  let ur := suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.realPart
  let ui := suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.imagPart
  suzukiRestrictedWeilForm a.val (suzukiRescaledCore a ur) (suzukiRescaledCore a ur) +
    suzukiRestrictedWeilForm a.val (suzukiRescaledCore a ui) (suzukiRescaledCore a ui)

/-- Exact complex scaling identity. -/
theorem suzukiRescaledComplexSourceForm_eq (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilComplexTest 1) :
    (1 / a.val) * suzukiRescaledComplexSourceForm a u =
      suzukiPrimeFreeScaledForm a u := by
  let ur := suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.realPart
  let ui := suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.imagPart
  have hr := suzukiRescaledRestrictedWeilForm_eq a ur
  have hi := suzukiRescaledRestrictedWeilForm_eq a ui
  unfold suzukiRescaledComplexSourceForm suzukiPrimeFreeScaledForm
  change (1 / a.val) *
      (suzukiRestrictedWeilForm a.val (suzukiRescaledCore a ur) (suzukiRescaledCore a ur) +
        suzukiRestrictedWeilForm a.val (suzukiRescaledCore a ui) (suzukiRescaledCore a ui)) = _
  rw [mul_add, hr, hi]

/-- Actual-source version of quantitative small-aperture coercivity. -/
theorem suzukiRescaledComplexSourceForm_coercive
    (a : SuzukiPrimeFreeSmallAperture) (u : SuzukiRestrictedWeilComplexTest 1) :
    suzukiSmallScaleCoercivityCoefficient a.val *
        suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u ≤
      (1 / a.val) * suzukiRescaledComplexSourceForm a u := by
  rw [suzukiRescaledComplexSourceForm_eq]
  exact suzukiPrimeFreeScaledForm_coercive a u

/-- A prime-free aperture at which the uniform scaled coercivity coefficient is positive. -/
structure SuzukiCoerciveSmallAperture where
  toSmallAperture : SuzukiPrimeFreeSmallAperture
  coefficient_pos :
    0 < suzukiSmallScaleCoercivityCoefficient toSmallAperture.val

/-- Literal normalized complex test source on the fixed interval. -/
structure SuzukiNormalizedComplexTest where
  toTest : SuzukiRestrictedWeilComplexTest 1
  intervalEnergy_eq_one :
    suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture toTest = 1

/-- Closed actual-source positivity theorem in the small-aperture range.  All legality,
normalization, and smallness conditions are intrinsic structure fields, not theorem premises. -/
theorem suzukiRescaledComplexSourceForm_pos
    (a : SuzukiCoerciveSmallAperture) (u : SuzukiNormalizedComplexTest) :
    0 < (1 / a.toSmallAperture.val) *
      suzukiRescaledComplexSourceForm a.toSmallAperture u.toTest := by
  have h := suzukiRescaledComplexSourceForm_coercive a.toSmallAperture u.toTest
  rw [u.intervalEnergy_eq_one, mul_one] at h
  exact a.coefficient_pos.trans_le h

end GaloisForLFunctions.RHTower
