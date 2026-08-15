import GaloisForLFunctions.RHTower.SuzukiSmallApertureClosedFormScaling
import GaloisForLFunctions.RHTower.SuzukiLimitingLogGroundSimplicity
import GaloisForLFunctions.RHTower.FiniteTimeBandFourierCompact

open Complex MeasureTheory Set Filter Topology intervalIntegral
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- Cross-term bound for a bounded continuous kernel on Suzuki's fixed unit interval. -/
theorem iteratedUnitKernelCross_abs_le
    {C : ℝ} {k f g : ℝ → ℝ}
    (hk : Continuous k) (hf : Continuous f) (hg : Continuous g)
    (_hC0 : 0 ≤ C) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hC : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |k (x - y)| ≤ C) :
    |∫ x in (-1 : ℝ)..1, (∫ y in (-1 : ℝ)..1, k (x - y) * f y) * g x| ≤
      C * (∫ x in (-1 : ℝ)..1, f x) * (∫ x in (-1 : ℝ)..1, g x) := by
  let F : ℝ → ℝ → ℝ := fun x y => k (x - y) * f y
  let If : ℝ := ∫ x in (-1 : ℝ)..1, f x
  have hIf0 : 0 ≤ If :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => hf0 x)
  have hinnerCont : Continuous fun x => ∫ y in (-1 : ℝ)..1, F x y := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (((hk.comp (continuous_fst.sub continuous_snd)).mul
        (hf.comp continuous_snd))) continuous_const
  have hinnerAbsCont : Continuous fun x => |∫ y in (-1 : ℝ)..1, F x y| :=
    hinnerCont.abs
  have houterAbs :
      |∫ x in (-1 : ℝ)..1, (∫ y in (-1 : ℝ)..1, F x y) * g x| ≤
        ∫ x in (-1 : ℝ)..1, |(∫ y in (-1 : ℝ)..1, F x y) * g x| :=
    abs_integral_le_integral_abs (by norm_num)
  have hinner (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
      |∫ y in (-1 : ℝ)..1, F x y| ≤ C * If := by
    have habs :
        |∫ y in (-1 : ℝ)..1, F x y| ≤
          ∫ y in (-1 : ℝ)..1, |F x y| :=
      abs_integral_le_integral_abs (by norm_num)
    have hmono :
        (∫ y in (-1 : ℝ)..1, |F x y|) ≤
          ∫ y in (-1 : ℝ)..1, C * f y := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (((hk.comp (continuous_const.sub continuous_id)).mul hf).abs.intervalIntegrable _ _)
        ((hf.const_mul C).intervalIntegrable _ _)
      intro y hy
      change |k (x - y) * f y| ≤ C * f y
      rw [abs_mul, abs_of_nonneg (hf0 y)]
      exact mul_le_mul_of_nonneg_right (hC x hx y hy) (hf0 y)
    calc
      |∫ y in (-1 : ℝ)..1, F x y| ≤
          ∫ y in (-1 : ℝ)..1, |F x y| := habs
      _ ≤ ∫ y in (-1 : ℝ)..1, C * f y := hmono
      _ = C * If := by
        rw [intervalIntegral.integral_const_mul]
  have hpoint (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
      |(∫ y in (-1 : ℝ)..1, F x y) * g x| ≤ (C * If) * g x := by
    rw [abs_mul, abs_of_nonneg (hg0 x)]
    exact mul_le_mul_of_nonneg_right (hinner x hx) (hg0 x)
  have hmonoOuter :
      (∫ x in (-1 : ℝ)..1, |(∫ y in (-1 : ℝ)..1, F x y) * g x|) ≤
        ∫ x in (-1 : ℝ)..1, (C * If) * g x := by
    rw [show (fun x : ℝ => |(∫ y in (-1 : ℝ)..1, F x y) * g x|) =
        fun x => |∫ y in (-1 : ℝ)..1, F x y| * g x by
      funext x
      rw [abs_mul, abs_of_nonneg (hg0 x)]]
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((hinnerAbsCont.mul hg).intervalIntegrable _ _)
      ((hg.const_mul (C * If)).intervalIntegrable _ _)
    intro x hx
    simpa [abs_mul, abs_of_nonneg (hg0 x)] using hpoint x hx
  change |∫ x in (-1 : ℝ)..1, (∫ y in (-1 : ℝ)..1, F x y) * g x| ≤ _
  calc
    |∫ x in (-1 : ℝ)..1, (∫ y in (-1 : ℝ)..1, F x y) * g x| ≤
        ∫ x in (-1 : ℝ)..1, |(∫ y in (-1 : ℝ)..1, F x y) * g x| := houterAbs
    _ ≤ ∫ x in (-1 : ℝ)..1, (C * If) * g x := hmonoOuter
    _ = C * If * (∫ x in (-1 : ℝ)..1, g x) := by
      rw [intervalIntegral.integral_const_mul]

/-- Continuous scaled origin-remainder kernel on the fixed unit interval square. -/
def suzukiScaledRemainderKernelContinuous
    (a : SuzukiPrimeFreeSmallAperture) :
    C(SuzukiApertureInterval 1 × SuzukiApertureInterval 1, ℂ) where
  toFun z := (suzukiOriginRemainderCurvature
    (a.val * ((z.1 : ℝ) - (z.2 : ℝ))) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (continuous_suzukiOriginRemainderCurvature.comp
      (continuous_const.mul
        ((continuous_subtype_val.comp continuous_fst).sub
          (continuous_subtype_val.comp continuous_snd))))

/-- Kernel sections as a continuous family of unit-interval `L²` vectors. -/
def suzukiScaledRemainderKernelSectionL2
    (a : SuzukiPrimeFreeSmallAperture)
    (x : SuzukiApertureInterval 1) : SuzukiApertureIntervalL2 1 :=
  ContinuousMap.toLp 2 (volume : Measure (SuzukiApertureInterval 1)) ℂ
    ((suzukiScaledRemainderKernelContinuous a).curry x)

theorem continuous_suzukiScaledRemainderKernelSectionL2
    (a : SuzukiPrimeFreeSmallAperture) :
    Continuous (suzukiScaledRemainderKernelSectionL2 a) := by
  exact (ContinuousMap.toLp 2
    (volume : Measure (SuzukiApertureInterval 1)) ℂ).continuous.comp
      (suzukiScaledRemainderKernelContinuous a).curry.continuous

/-- Continuous field of kernel-section functionals. -/
def suzukiScaledRemainderFunctionalContinuous
    (a : SuzukiPrimeFreeSmallAperture) :
    C(SuzukiApertureInterval 1,
      SuzukiApertureIntervalL2 1 →L[ℂ] ℂ) where
  toFun x := (InnerProductSpace.toDual ℂ (SuzukiApertureIntervalL2 1))
    (suzukiScaledRemainderKernelSectionL2 a x)
  continuous_toFun :=
    (InnerProductSpace.toDual ℂ
      (SuzukiApertureIntervalL2 1)).continuous.comp
        (continuous_suzukiScaledRemainderKernelSectionL2 a)

def suzukiScaledRemainderFunctionalField
    (a : SuzukiPrimeFreeSmallAperture) :
    Lp (SuzukiApertureIntervalL2 1 →L[ℂ] ℂ) 2
      (volume : Measure (SuzukiApertureInterval 1)) :=
  ContinuousMap.toLp 2 (volume : Measure (SuzukiApertureInterval 1)) ℂ
    (suzukiScaledRemainderFunctionalContinuous a)

/-- Bounded complete-domain realization of Suzuki's exact scaled remainder kernel. -/
def suzukiScaledRemainderOperator
    (a : SuzukiPrimeFreeSmallAperture) :
    SuzukiApertureIntervalL2 1 →L[ℂ] SuzukiApertureIntervalL2 1 :=
  kernelOperator (volume : Measure (SuzukiApertureInterval 1))
    (suzukiScaledRemainderFunctionalField a)

theorem suzukiScaledRemainderOperator_coeFn
    (a : SuzukiPrimeFreeSmallAperture)
    (f : SuzukiApertureIntervalL2 1) :
    (suzukiScaledRemainderOperator a f :
        SuzukiApertureInterval 1 → ℂ) =ᵐ[volume]
      fun x => ∫ y : SuzukiApertureInterval 1,
        (suzukiOriginRemainderCurvature
          (a.val * ((x : ℝ) - (y : ℝ))) : ℂ) * f y := by
  filter_upwards [
    (evalBilinear (𝕜 := ℂ) (E := SuzukiApertureIntervalL2 1)).coeFn_holder
      (r := (2 : ENNReal)) (suzukiScaledRemainderFunctionalField a)
      (Lp.const ∞ (volume : Measure (SuzukiApertureInterval 1)) f),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure (SuzukiApertureInterval 1)))
      (suzukiScaledRemainderFunctionalContinuous a),
    Lp.coeFn_const (p := ∞)
      (volume : Measure (SuzukiApertureInterval 1)) f] with x hholder hfield hconst
  rw [suzukiScaledRemainderOperator, kernelOperator, kernelOperatorMap_apply,
    hholder, suzukiScaledRemainderFunctionalField, hfield, hconst]
  change inner ℂ (suzukiScaledRemainderKernelSectionL2 a x) f = _
  rw [MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
    (μ := (volume : Measure (SuzukiApertureInterval 1)))
    ((suzukiScaledRemainderKernelContinuous a).curry x)] with y hy
  change inner ℂ
      ((ContinuousMap.toLp 2 (volume : Measure (SuzukiApertureInterval 1)) ℂ
        ((suzukiScaledRemainderKernelContinuous a).curry x) :
          SuzukiApertureInterval 1 → ℂ) y)
      (f y) = _
  rw [hy]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  simp [suzukiScaledRemainderKernelContinuous]
  ring

theorem integral_subtype_unitIcc_eq_intervalIntegral_complex
    (F : ℝ → ℂ) :
    (∫ x : SuzukiApertureInterval 1, F (x : ℝ) ∂volume) =
      ∫ x in (-1 : ℝ)..1, F x := by
  calc
    (∫ x : SuzukiApertureInterval 1, F (x : ℝ) ∂volume) =
        ∫ x in Icc (-1 : ℝ) 1, F x := by
      exact MeasureTheory.integral_subtype measurableSet_Icc F
    _ = ∫ x in Ioc (-1 : ℝ) 1, F x :=
      MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ x in (-1 : ℝ)..1, F x := by
      rw [intervalIntegral.integral_of_le (by norm_num)]

/-- Mixed real core matrix coefficients of the completed remainder are literal real integrals. -/
theorem inner_suzukiScaledRemainderOperator_core_mixed_eq
    (a : SuzukiPrimeFreeSmallAperture)
    (u v : SuzukiRestrictedWeilCore 1) :
    inner ℂ
        (suzukiScaledRemainderOperator a (suzukiLimitingCoreIntervalVector u))
        (suzukiLimitingCoreIntervalVector v) =
      ((∫ x in (-1 : ℝ)..1,
        (∫ y in (-1 : ℝ)..1,
          suzukiOriginRemainderCurvature (a.val * (x - y)) * u y) * v x : ℝ) : ℂ) := by
  rw [MeasureTheory.L2.inner_def]
  have hop := suzukiScaledRemainderOperator_coeFn a
    (suzukiLimitingCoreIntervalVector u)
  have hcoreU := suzukiLimitingCoreIntervalVector_coeFn u
  have hcoreV := suzukiLimitingCoreIntervalVector_coeFn v
  calc
    (∫ x : SuzukiApertureInterval 1,
        inner ℂ
          ((suzukiScaledRemainderOperator a
            (suzukiLimitingCoreIntervalVector u)) x)
          ((suzukiLimitingCoreIntervalVector v) x)) =
      ∫ x : SuzukiApertureInterval 1,
        (∫ y : SuzukiApertureInterval 1,
          (suzukiOriginRemainderCurvature
            (a.val * ((x : ℝ) - (y : ℝ))) : ℂ) * (u (y : ℝ) : ℂ)) *
          (v (x : ℝ) : ℂ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hop, hcoreV] with x hx hvx
      rw [hx, hvx]
      simp only [RCLike.inner_apply, starRingEnd_apply]
      have hrealint :
          star (∫ y : SuzukiApertureInterval 1,
            (suzukiOriginRemainderCurvature
              (a.val * ((x : ℝ) - (y : ℝ))) : ℂ) *
                (suzukiLimitingCoreIntervalVector u) y) =
            ∫ y : SuzukiApertureInterval 1,
              (suzukiOriginRemainderCurvature
                (a.val * ((x : ℝ) - (y : ℝ))) : ℂ) * (u (y : ℝ) : ℂ) := by
        change (starRingEnd ℂ) (∫ y : SuzukiApertureInterval 1,
            (suzukiOriginRemainderCurvature
              (a.val * ((x : ℝ) - (y : ℝ))) : ℂ) *
                (suzukiLimitingCoreIntervalVector u) y) = _
        rw [← integral_conj]
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hcoreU] with y huy
        rw [huy]
        simp
      rw [hrealint]
      ring
    _ = ∫ x in (-1 : ℝ)..1,
        (∫ y in (-1 : ℝ)..1,
          (suzukiOriginRemainderCurvature (a.val * (x - y)) : ℂ) *
            (u y : ℂ)) * (v x : ℂ) := by
      let H : ℝ → ℂ := fun x =>
        (∫ y : SuzukiApertureInterval 1,
          (suzukiOriginRemainderCurvature
            (a.val * (x - (y : ℝ))) : ℂ) * (u (y : ℝ) : ℂ)) *
          (v x : ℂ)
      change (∫ x : SuzukiApertureInterval 1, H (x : ℝ) ∂volume) = _
      rw [integral_subtype_unitIcc_eq_intervalIntegral_complex]
      apply intervalIntegral.integral_congr
      intro x _
      unfold H
      congr 1
      exact integral_subtype_unitIcc_eq_intervalIntegral_complex
        (fun y => (suzukiOriginRemainderCurvature
          (a.val * (x - y)) : ℂ) * (u y : ℂ))
    _ = ((∫ x in (-1 : ℝ)..1,
        (∫ y in (-1 : ℝ)..1,
          suzukiOriginRemainderCurvature (a.val * (x - y)) * u y) * v x : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      push_cast
      have hinnerReal :
          (∫ y in (-1 : ℝ)..1,
            (suzukiOriginRemainderCurvature (a.val * (x - y)) : ℂ) *
              (u y : ℂ)) =
            ((∫ y in (-1 : ℝ)..1,
              suzukiOriginRemainderCurvature (a.val * (x - y)) * u y : ℝ) : ℂ) := by
        rw [← intervalIntegral.integral_ofReal]
        push_cast
        rfl
      rw [hinnerReal]

/-- The bounded complete-domain operator agrees with Suzuki's literal smooth-core remainder. -/
theorem inner_suzukiScaledRemainderOperator_core_eq
    (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilCore 1) :
    inner ℂ
        (suzukiScaledRemainderOperator a (suzukiLimitingCoreIntervalVector u))
        (suzukiLimitingCoreIntervalVector u) =
      (suzukiScaledRemainderQuadraticReal a u : ℂ) := by
  rw [inner_suzukiScaledRemainderOperator_core_mixed_eq]
  rfl

theorem inner_suzukiScaledRemainderOperator_core_mixed_im_eq_zero
    (a : SuzukiPrimeFreeSmallAperture)
    (u v : SuzukiRestrictedWeilCore 1) :
    (inner ℂ
      (suzukiScaledRemainderOperator a (suzukiLimitingCoreIntervalVector u))
      (suzukiLimitingCoreIntervalVector v)).im = 0 := by
  rw [inner_suzukiScaledRemainderOperator_core_mixed_eq]
  simp

/-- Complexification of a real interval `L²` class. -/
def suzukiIntervalL2OfReal
    (f : Lp ℝ 2 (volume : Measure (SuzukiApertureInterval 1))) :
    SuzukiApertureIntervalL2 1 :=
  (MeasureTheory.Lp.memLp f).ofReal.toLp (fun x => (f x : ℂ))

theorem suzukiIntervalL2OfReal_coeFn
    (f : Lp ℝ 2 (volume : Measure (SuzukiApertureInterval 1))) :
    (suzukiIntervalL2OfReal f : SuzukiApertureInterval 1 → ℂ) =ᵐ[volume]
      fun x => (f x : ℂ) := by
  exact (MeasureTheory.Lp.memLp f).ofReal.coeFn_toLp

theorem suzukiOriginCurvature_scaled_unit_bound
    (a : SuzukiPrimeFreeSmallAperture)
    (x y : SuzukiApertureInterval 1) :
    |suzukiOriginRemainderCurvature
      (a.val * ((x : ℝ) - (y : ℝ)))| ≤ suzukiOriginCurvatureUnitBound := by
  apply suzukiOriginCurvatureUnitBound_spec.2
  have hxy : |(x : ℝ) - (y : ℝ)| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [x.property.1, x.property.2, y.property.1, y.property.2]
  rw [abs_mul, abs_of_pos a.pos]
  nlinarith [a.two_mul_le_one, abs_nonneg ((x : ℝ) - (y : ℝ))]

/-- Exact `L¹ × L¹` cross bound for the completed scaled remainder operator. -/
theorem norm_inner_suzukiScaledRemainderOperator_ofReal_le
    (a : SuzukiPrimeFreeSmallAperture)
    (f g : Lp ℝ 2 (volume : Measure (SuzukiApertureInterval 1)))
    (hf0 : 0 ≤ᵐ[volume] (f : SuzukiApertureInterval 1 → ℝ))
    (hg0 : 0 ≤ᵐ[volume] (g : SuzukiApertureInterval 1 → ℝ)) :
    ‖inner ℂ
        (suzukiScaledRemainderOperator a (suzukiIntervalL2OfReal f))
        (suzukiIntervalL2OfReal g)‖ ≤
      suzukiOriginCurvatureUnitBound *
        (∫ x : SuzukiApertureInterval 1, f x) *
          (∫ x : SuzukiApertureInterval 1, g x) := by
  let C := suzukiOriginCurvatureUnitBound
  let If : ℝ := ∫ x : SuzukiApertureInterval 1, f x
  let Ig : ℝ := ∫ x : SuzukiApertureInterval 1, g x
  have hC0 : 0 ≤ C := suzukiOriginCurvatureUnitBound_spec.1
  have hfint : Integrable (fun x : SuzukiApertureInterval 1 => f x) :=
    (MeasureTheory.Lp.memLp f).integrable (by norm_num)
  have hgint : Integrable (fun x : SuzukiApertureInterval 1 => g x) :=
    (MeasureTheory.Lp.memLp g).integrable (by norm_num)
  have hIf0 : 0 ≤ If := integral_nonneg_of_ae hf0
  have hIg0 : 0 ≤ Ig := integral_nonneg_of_ae hg0
  have hinner (x : SuzukiApertureInterval 1) :
      ‖∫ y : SuzukiApertureInterval 1,
        (suzukiOriginRemainderCurvature
          (a.val * ((x : ℝ) - (y : ℝ))) : ℂ) * (f y : ℂ)‖ ≤ C * If := by
    have hdom : Integrable (fun y : SuzukiApertureInterval 1 => C * f y) :=
      hfint.const_mul C
    have hpoint : ∀ᵐ y : SuzukiApertureInterval 1 ∂volume,
        ‖(suzukiOriginRemainderCurvature
          (a.val * ((x : ℝ) - (y : ℝ))) : ℂ) * (f y : ℂ)‖ ≤ C * f y := by
      filter_upwards [hf0] with y hfy
      rw [norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hfy]
      exact mul_le_mul_of_nonneg_right
        (suzukiOriginCurvature_scaled_unit_bound a x y) hfy
    calc
      ‖∫ y : SuzukiApertureInterval 1,
          (suzukiOriginRemainderCurvature
            (a.val * ((x : ℝ) - (y : ℝ))) : ℂ) * (f y : ℂ)‖ ≤
          ∫ y : SuzukiApertureInterval 1, C * f y :=
        MeasureTheory.norm_integral_le_of_norm_le hdom hpoint
      _ = C * If := by rw [MeasureTheory.integral_const_mul]
  have hop := suzukiScaledRemainderOperator_coeFn a (suzukiIntervalL2OfReal f)
  have hfcoe := suzukiIntervalL2OfReal_coeFn f
  have hgcoe := suzukiIntervalL2OfReal_coeFn g
  rw [MeasureTheory.L2.inner_def]
  have hdomOuter : Integrable
      (fun x : SuzukiApertureInterval 1 => (C * If) * g x) :=
    hgint.const_mul (C * If)
  have hpointOuter : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
      ‖inner ℂ
        ((suzukiScaledRemainderOperator a (suzukiIntervalL2OfReal f)) x)
        ((suzukiIntervalL2OfReal g) x)‖ ≤ (C * If) * g x := by
    filter_upwards [hop, hfcoe, hgcoe, hg0] with x hopx hfx hgx hgx0
    rw [hopx, hgx]
    simp only [RCLike.inner_apply, starRingEnd_apply]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgx0]
    have heq :
        (∫ y : SuzukiApertureInterval 1,
          (suzukiOriginRemainderCurvature
            (a.val * ((x : ℝ) - (y : ℝ))) : ℂ) *
              (suzukiIntervalL2OfReal f) y) =
          ∫ y : SuzukiApertureInterval 1,
            (suzukiOriginRemainderCurvature
              (a.val * ((x : ℝ) - (y : ℝ))) : ℂ) * (f y : ℂ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hfcoe] with y hfy
      rw [hfy]
    rw [heq, norm_star]
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_right (hinner x) hgx0)
  calc
    ‖∫ x : SuzukiApertureInterval 1,
        inner ℂ
          ((suzukiScaledRemainderOperator a (suzukiIntervalL2OfReal f)) x)
          ((suzukiIntervalL2OfReal g) x)‖ ≤
        ∫ x : SuzukiApertureInterval 1, (C * If) * g x :=
      MeasureTheory.norm_integral_le_of_norm_le hdomOuter hpointOuter
    _ = C * If * Ig := by rw [MeasureTheory.integral_const_mul]

theorem suzukiIntervalL2OfReal_realPart_eq_of_im_zero
    (f : SuzukiApertureIntervalL2 1)
    (him : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume, (f x).im = 0) :
    suzukiIntervalL2OfReal (suzukiIntervalL2RealPart f) = f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [suzukiIntervalL2OfReal_coeFn (suzukiIntervalL2RealPart f),
    suzukiIntervalL2RealPart_coeFn f, him] with x hof hre himx
  rw [hof, hre]
  apply Complex.ext
  · simp
  · simp [himx]

theorem suzukiIntervalL2OfReal_pos_sub_neg_eq_of_im_zero
    (f : SuzukiApertureIntervalL2 1)
    (him : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume, (f x).im = 0) :
    suzukiIntervalL2OfReal (suzukiIntervalL2RealPositivePart f) -
        suzukiIntervalL2OfReal (suzukiIntervalL2RealNegativePart f) = f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub
      (suzukiIntervalL2OfReal (suzukiIntervalL2RealPositivePart f))
      (suzukiIntervalL2OfReal (suzukiIntervalL2RealNegativePart f)),
    suzukiIntervalL2OfReal_coeFn (suzukiIntervalL2RealPositivePart f),
    suzukiIntervalL2OfReal_coeFn (suzukiIntervalL2RealNegativePart f),
    suzukiIntervalL2RealPart_coeFn f,
    Lp.coeFn_posPart (suzukiIntervalL2RealPart f),
    Lp.coeFn_negPart_eq_max (suzukiIntervalL2RealPart f), him] with
      x hsub hp hn hre hpos hneg himx
  rw [hsub, Pi.sub_apply, hp, hn]
  change ((Lp.posPart (suzukiIntervalL2RealPart f) x : ℝ) : ℂ) -
      ((Lp.negPart (suzukiIntervalL2RealPart f) x : ℝ) : ℂ) = f x
  rw [hpos, hneg, hre]
  apply Complex.ext
  · exact posPart_sub_negPart (f x).re
  · simp [himx]

theorem suzukiIntervalL2OfReal_pos_add_neg_eq_modulus_of_im_zero
    (f : SuzukiApertureIntervalL2 1)
    (him : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume, (f x).im = 0) :
    suzukiIntervalL2OfReal (suzukiIntervalL2RealPositivePart f) +
        suzukiIntervalL2OfReal (suzukiIntervalL2RealNegativePart f) =
      suzukiIntervalL2Modulus f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    MeasureTheory.Lp.coeFn_add
      (suzukiIntervalL2OfReal (suzukiIntervalL2RealPositivePart f))
      (suzukiIntervalL2OfReal (suzukiIntervalL2RealNegativePart f)),
    suzukiIntervalL2OfReal_coeFn (suzukiIntervalL2RealPositivePart f),
    suzukiIntervalL2OfReal_coeFn (suzukiIntervalL2RealNegativePart f),
    suzukiIntervalL2RealPart_coeFn f,
    Lp.coeFn_posPart (suzukiIntervalL2RealPart f),
    Lp.coeFn_negPart_eq_max (suzukiIntervalL2RealPart f),
    suzukiIntervalL2Modulus_coeFn f, him] with
      x hadd hp hn hre hpos hneg hmod himx
  rw [hadd, Pi.add_apply, hp, hn]
  change ((Lp.posPart (suzukiIntervalL2RealPart f) x : ℝ) : ℂ) +
      ((Lp.negPart (suzukiIntervalL2RealPart f) x : ℝ) : ℂ) =
    suzukiIntervalL2Modulus f x
  rw [hpos, hneg, hre, hmod]
  norm_cast
  rw [Complex.norm_def]
  simp only [Complex.normSq_apply, himx, mul_zero, add_zero]
  rw [← pow_two, Real.sqrt_sq_eq_abs]
  exact posPart_add_negPart (f x).re

/-- Completed quadratic form of Suzuki's scaled origin-remainder kernel. -/
def suzukiScaledRemainderClosedQuadratic
    (a : SuzukiPrimeFreeSmallAperture)
    (f : SuzukiApertureIntervalL2 1) : ℝ :=
  (inner ℂ (suzukiScaledRemainderOperator a f) f).re

theorem suzukiScaledRemainderClosedQuadratic_core
    (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilCore 1) :
    suzukiScaledRemainderClosedQuadratic a
        (suzukiLimitingCoreIntervalVector u) =
      suzukiScaledRemainderQuadraticReal a u := by
  unfold suzukiScaledRemainderClosedQuadratic
  rw [inner_suzukiScaledRemainderOperator_core_eq]
  rfl

/-- Modulus changes the completed bounded remainder only through positive-negative cross terms. -/
theorem abs_suzukiScaledRemainderClosedQuadratic_modulus_sub_le
    (a : SuzukiPrimeFreeSmallAperture)
    (f : SuzukiApertureIntervalL2 1)
    (him : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume, (f x).im = 0) :
    |suzukiScaledRemainderClosedQuadratic a (suzukiIntervalL2Modulus f) -
        suzukiScaledRemainderClosedQuadratic a f| ≤
      4 * suzukiOriginCurvatureUnitBound *
        suzukiIntervalPositiveMass f * suzukiIntervalNegativeMass f := by
  let pr := suzukiIntervalL2RealPositivePart f
  let nr := suzukiIntervalL2RealNegativePart f
  let p := suzukiIntervalL2OfReal pr
  let n := suzukiIntervalL2OfReal nr
  have hp0 : 0 ≤ᵐ[volume] (pr : SuzukiApertureInterval 1 → ℝ) := by
    filter_upwards [Lp.coeFn_posPart (suzukiIntervalL2RealPart f)] with x hx
    change (0 : ℝ) ≤ (Lp.posPart (suzukiIntervalL2RealPart f)) x
    rw [hx]
    exact le_max_right _ _
  have hn0 : 0 ≤ᵐ[volume] (nr : SuzukiApertureInterval 1 → ℝ) := by
    filter_upwards [Lp.coeFn_negPart_eq_max (suzukiIntervalL2RealPart f)] with x hx
    change (0 : ℝ) ≤ (Lp.negPart (suzukiIntervalL2RealPart f)) x
    rw [hx]
    exact le_max_right _ _
  have hpSub : p - n = f := by
    exact suzukiIntervalL2OfReal_pos_sub_neg_eq_of_im_zero f him
  have hpAdd : p + n = suzukiIntervalL2Modulus f := by
    exact suzukiIntervalL2OfReal_pos_add_neg_eq_modulus_of_im_zero f him
  let A : ℂ := inner ℂ (suzukiScaledRemainderOperator a p) n
  let B : ℂ := inner ℂ (suzukiScaledRemainderOperator a n) p
  have hdiff :
      suzukiScaledRemainderClosedQuadratic a (suzukiIntervalL2Modulus f) -
          suzukiScaledRemainderClosedQuadratic a f =
        2 * (A.re + B.re) := by
    rw [← hpAdd, ← hpSub]
    unfold suzukiScaledRemainderClosedQuadratic A B
    simp only [map_add, map_sub, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, Complex.add_re, Complex.sub_re]
    ring
  have hA := norm_inner_suzukiScaledRemainderOperator_ofReal_le a pr nr hp0 hn0
  have hB := norm_inner_suzukiScaledRemainderOperator_ofReal_le a nr pr hn0 hp0
  have hmassP : (∫ x : SuzukiApertureInterval 1, pr x) =
      suzukiIntervalPositiveMass f := by
    exact (suzukiIntervalPositiveMass_eq_integral f).symm
  have hmassN : (∫ x : SuzukiApertureInterval 1, nr x) =
      suzukiIntervalNegativeMass f := by
    exact (suzukiIntervalNegativeMass_eq_integral f).symm
  rw [hmassP, hmassN] at hA
  rw [hmassN, hmassP] at hB
  have hAre : |A.re| ≤ ‖A‖ := RCLike.abs_re_le_norm A
  have hBre : |B.re| ≤ ‖B‖ := RCLike.abs_re_le_norm B
  have hP := suzukiIntervalPositiveMass_nonneg f
  have hN := suzukiIntervalNegativeMass_nonneg f
  have hC := suzukiOriginCurvatureUnitBound_spec.1
  rw [hdiff, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hadd : |A.re + B.re| ≤ |A.re| + |B.re| := abs_add_le _ _
  calc
    2 * |A.re + B.re| ≤ 2 * (|A.re| + |B.re|) :=
      mul_le_mul_of_nonneg_left hadd (by norm_num)
    _ ≤ 2 * (‖A‖ + ‖B‖) := by nlinarith
    _ ≤ 4 * suzukiOriginCurvatureUnitBound *
        suzukiIntervalPositiveMass f * suzukiIntervalNegativeMass f := by
      dsimp only [A, B]
      nlinarith

theorem suzukiLimitingLogFormEmbedding_complexCore_eq_real_add_I_imag
    (u : SuzukiRestrictedWeilComplexTest 1) :
    suzukiLimitingLogFormEmbedding
        (suzukiLimitingComplexCoreFormVector u) =
      suzukiLimitingCoreIntervalVector
          (suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.realPart) +
        I • suzukiLimitingCoreIntervalVector
          (suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.imagPart) := by
  rw [suzukiLimitingComplexCoreFormVector_eq_real_add_I_imag]
  simp only [map_add, map_smul]
  rw [suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding,
    suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding]

/-- The completed bounded remainder is exactly Suzuki's complex smooth-core remainder. -/
theorem suzukiScaledRemainderClosedQuadratic_complexCore
    (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilComplexTest 1) :
    suzukiScaledRemainderClosedQuadratic a
        (suzukiLimitingLogFormEmbedding
          (suzukiLimitingComplexCoreFormVector u)) =
      suzukiScaledComplexRemainderQuadratic a u := by
  let ur : SuzukiRestrictedWeilCore 1 :=
    suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.realPart
  let ui : SuzukiRestrictedWeilCore 1 :=
    suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.imagPart
  let r := suzukiLimitingCoreIntervalVector ur
  let i := suzukiLimitingCoreIntervalVector ui
  have hri :
      (inner ℂ (suzukiScaledRemainderOperator a r) i).im = 0 :=
    inner_suzukiScaledRemainderOperator_core_mixed_im_eq_zero a ur ui
  have hir :
      (inner ℂ (suzukiScaledRemainderOperator a i) r).im = 0 :=
    inner_suzukiScaledRemainderOperator_core_mixed_im_eq_zero a ui ur
  have hrr :
      inner ℂ (suzukiScaledRemainderOperator a r) r =
        (suzukiScaledRemainderQuadraticReal a ur : ℂ) :=
    inner_suzukiScaledRemainderOperator_core_eq a ur
  have hii :
      inner ℂ (suzukiScaledRemainderOperator a i) i =
        (suzukiScaledRemainderQuadraticReal a ui : ℂ) :=
    inner_suzukiScaledRemainderOperator_core_eq a ui
  rw [suzukiLimitingLogFormEmbedding_complexCore_eq_real_add_I_imag]
  unfold suzukiScaledRemainderClosedQuadratic
    suzukiScaledComplexRemainderQuadratic
  change (inner ℂ
      (suzukiScaledRemainderOperator a (r + I • i)) (r + I • i)).re =
    suzukiScaledRemainderQuadraticReal a ur +
      suzukiScaledRemainderQuadraticReal a ui
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, Complex.add_re, Complex.mul_re,
    Complex.conj_I, Complex.I_re, Complex.I_im, zero_mul, one_mul, neg_mul]
  rw [hrr, hii]
  simp [Complex.mul_re, hri, hir]

end RHTower
