import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Causal Fourier bridges

This module supplies the classical Fourier infrastructure needed to construct half-plane Hardy
readers from source-side functions rather than from an existence proposition.  It proves the
Fourier convolution identity for arbitrary integrable functions, evaluates the Fourier transform
of the normalized one-sided exponential, and packages one right-half-plane Blaschke factor as a
causality-preserving source-side convolution step.
-/

open Complex Real Set Filter Topology MeasureTheory FourierTransform
open scoped Convolution

noncomputable section

namespace RHTower

/-- The classical Fourier transform converts convolution into multiplication for arbitrary
integrable complex functions.  The usual continuity assumptions on the functions are unnecessary:
absolute integrability on the product supplies the Fubini step directly. -/
theorem fourier_mul_convolution_eq_of_integrable
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    𝓕 (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) ξ = (𝓕 f ξ) * (𝓕 g ξ) := by
  rw [Real.fourier_real_eq]
  rw [Real.fourier_real_eq]
  rw [Real.fourier_real_eq]
  simp only [MeasureTheory.convolution_def]
  have hbase : Integrable (fun p : ℝ × ℝ => f p.2 * g (p.1 - p.2))
      (volume.prod volume) := by
    simpa using hf.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hg
  have hphase : Integrable
      (fun p : ℝ × ℝ => 𝐞 (-(p.1 * ξ)) • (f p.2 * g (p.1 - p.2)))
      (volume.prod volume) := by
    rw [← integrable_norm_iff]
    · simpa only [Circle.norm_smul] using hbase.norm
    · exact (Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable.smul
        hbase.aestronglyMeasurable
  calc
    (∫ v : ℝ, 𝐞 (-(v * ξ)) • ∫ t : ℝ, f t * g (v - t)) =
        ∫ v : ℝ, ∫ t : ℝ, 𝐞 (-(v * ξ)) • (f t * g (v - t)) := by
          congr with v
          simp only [Circle.smul_def, smul_eq_mul]
          rw [MeasureTheory.integral_const_mul]
    _ = ∫ t : ℝ, ∫ v : ℝ, 𝐞 (-(v * ξ)) • (f t * g (v - t)) := by
      exact integral_integral_swap hphase
    _ = ∫ t : ℝ, ∫ y : ℝ, 𝐞 (-((y + t) * ξ)) • (f t * g y) := by
      congr with t
      convert integral_sub_right_eq_self (μ := volume)
        (fun y : ℝ => 𝐞 (-((y + t) * ξ)) • (f t * g y)) t using 1
      congr with v
      ring_nf
    _ = ∫ t : ℝ, ∫ y : ℝ,
        𝐞 (-(t * ξ)) • 𝐞 (-(y * ξ)) • (f t * g y) := by
      congr with t
      congr with y
      rw [smul_smul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = ∫ t : ℝ, (𝐞 (-(t * ξ)) • f t) *
        (∫ y : ℝ, 𝐞 (-(y * ξ)) • g y) := by
      congr with t
      rw [← MeasureTheory.integral_const_mul]
      congr with y
      simp only [Circle.smul_def, smul_eq_mul]
      ring
    _ = (∫ t : ℝ, 𝐞 (-(t * ξ)) • f t) *
        ∫ y : ℝ, 𝐞 (-(y * ξ)) • g y := by
      rw [MeasureTheory.integral_mul_const]

/-- The normalized causal exponential whose Fourier transform is the right-half-plane resolvent
`(a + 2 i ξ)⁻¹`. -/
def causalFourierExponential (a : ℝ) (y : ℝ) : ℂ :=
  Set.indicator (Set.Ioi (0 : ℝ))
    (fun y : ℝ => (Real.pi : ℂ) * Complex.exp (-(Real.pi * a : ℝ) * y)) y

theorem causalFourierExponential_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (causalFourierExponential a) := by
  unfold causalFourierExponential
  rw [integrable_indicator_iff measurableSet_Ioi]
  have h := (integrableOn_exp_mul_complex_Ioi (a := (-(Real.pi * a) : ℝ))
    (by simpa using neg_lt_zero.mpr (mul_pos Real.pi_pos ha)) 0).const_mul (Real.pi : ℂ)
  apply h.congr
  filter_upwards with y
  congr 2
  push_cast
  ring

/-- An integrable convolution kernel maps a pointwise bounded function to a pointwise bounded
convolution, with the elementary `L¹ × L∞` bound. -/
theorem norm_convolution_le_of_bound
    {k f : ℝ → ℂ} (hk : Integrable k) {C : ℝ}
    (hf : ∀ y, ‖f y‖ ≤ C) (y : ℝ) :
    ‖(k ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y‖ ≤
      (∫ t : ℝ, ‖k t‖) * C := by
  rw [MeasureTheory.convolution_def]
  calc
    ‖∫ t : ℝ, ((ContinuousLinearMap.mul ℂ ℂ) (k t)) (f (y - t))‖ ≤
        ∫ t : ℝ, ‖k t‖ * C := by
      apply norm_integral_le_of_norm_le (hk.norm.mul_const C)
      filter_upwards [] with t
      rw [show ((ContinuousLinearMap.mul ℂ ℂ) (k t)) (f (y - t)) =
        k t * f (y - t) by rfl, norm_mul]
      exact mul_le_mul_of_nonneg_left (hf (y - t)) (norm_nonneg _)
    _ = (∫ t : ℝ, ‖k t‖) * C := by rw [integral_mul_const]

/-- An integrable, pointwise bounded complex function belongs to `L²`. -/
theorem memLp_two_of_integrable_of_norm_le
    {f : ℝ → ℂ} (hf : Integrable f) {C : ℝ}
    (hbound : ∀ y, ‖f y‖ ≤ C) :
    MemLp f 2 volume := by
  have hdom : Integrable (fun y => C * ‖f y‖) := hf.norm.const_mul C
  have hsq : Integrable (fun y => ‖f y‖ ^ 2) := by
    apply hdom.mono' (hf.aestronglyMeasurable.norm.pow 2)
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖f y‖ ^ 2 ≤ C * ‖f y‖
    nlinarith [norm_nonneg (f y), hbound y]
  exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).2 hsq

/-- The normalized causal exponential is uniformly bounded by `π` for nonnegative rate. -/
theorem norm_causalFourierExponential_le {a : ℝ} (ha : 0 ≤ a) (y : ℝ) :
    ‖causalFourierExponential a y‖ ≤ Real.pi := by
  unfold causalFourierExponential
  by_cases hy : y ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hy, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_exp]
    have hexp : Real.exp (-((Real.pi * a : ℝ) : ℂ) * (y : ℂ)).re ≤ 1 := by
      rw [Real.exp_le_one_iff]
      norm_num [Complex.mul_re]
      exact mul_nonneg (mul_nonneg Real.pi_pos.le ha) hy.le
    calc
      Real.pi * Real.exp (-((Real.pi * a : ℝ) : ℂ) * (y : ℂ)).re ≤
          Real.pi * 1 := mul_le_mul_of_nonneg_left hexp Real.pi_pos.le
      _ = Real.pi := mul_one _
  · rw [Set.indicator_of_notMem hy, norm_zero]
    exact Real.pi_pos.le

theorem fourier_causalFourierExponential {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (causalFourierExponential a) ξ = ((a : ℂ) + 2 * I * ξ)⁻¹ := by
  rw [Real.fourier_real_eq]
  unfold causalFourierExponential
  have heq :
      (fun v : ℝ => 𝐞 (-(v * ξ)) •
        (Set.Ioi (0 : ℝ)).indicator
          (fun y : ℝ => (Real.pi : ℂ) * Complex.exp (-(Real.pi * a : ℝ) * y)) v) =
      (Set.Ioi (0 : ℝ)).indicator (fun v : ℝ => 𝐞 (-(v * ξ)) •
        ((Real.pi : ℂ) * Complex.exp (-(Real.pi * a : ℝ) * v))) := by
    funext v
    by_cases hv : v ∈ Set.Ioi (0 : ℝ) <;> simp [hv]
  rw [heq, MeasureTheory.integral_indicator measurableSet_Ioi]
  let c : ℂ := (-(Real.pi * a : ℝ) : ℂ) - ((2 * Real.pi * ξ : ℝ) : ℂ) * I
  have hc : c.re < 0 := by
    dsimp [c]
    norm_num
    exact mul_pos Real.pi_pos ha
  have hint :
      (fun v : ℝ => 𝐞 (-(v * ξ)) •
        ((Real.pi : ℂ) * Complex.exp (-(Real.pi * a : ℝ) * v))) =
      fun v : ℝ => (Real.pi : ℂ) * Complex.exp (c * v) := by
    funext v
    simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
    calc
      Complex.exp ((2 * Real.pi * (-(v * ξ)) : ℝ) * I) *
          ((Real.pi : ℂ) * Complex.exp (-(Real.pi * a : ℝ) * v)) =
          (Real.pi : ℂ) *
            (Complex.exp ((2 * Real.pi * (-(v * ξ)) : ℝ) * I) *
              Complex.exp (-(Real.pi * a : ℝ) * v)) := by ring
      _ = (Real.pi : ℂ) * Complex.exp
          (((2 * Real.pi * (-(v * ξ)) : ℝ) : ℂ) * I +
            (-(Real.pi * a : ℝ) : ℂ) * v) := by rw [Complex.exp_add]
      _ = (Real.pi : ℂ) * Complex.exp (c * v) := by
        congr 2
        dsimp [c]
        push_cast
        ring
  rw [hint, MeasureTheory.integral_const_mul,
    integral_exp_mul_complex_Ioi hc 0]
  dsimp [c]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [mul_zero, Complex.exp_zero]
  have hden :
      -((Real.pi * a : ℝ) : ℂ) - ((2 * Real.pi * ξ : ℝ) : ℂ) * I =
        -(Real.pi : ℂ) * ((a : ℂ) + 2 * I * ξ) := by
    push_cast
    ring
  rw [hden]
  have hz : (a : ℂ) + 2 * I * ξ ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    exact ha.ne' hre
  field_simp [hpi, hz]

/-- One Blaschke factor `(a-z)/(a+z)` acting on a causal source. -/
def causalBlaschkeStep (a : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  -f y + (2 * a : ℂ) *
    (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y

theorem causalBlaschkeStep_integrable {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (causalBlaschkeStep a f) := by
  have hc := causalFourierExponential_integrable ha
  have hconv := hc.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf
  exact hf.neg.add (hconv.const_mul (2 * a : ℂ))

/-- A causal Blaschke step multiplies the Fourier transform by exactly one right-half-plane inner
factor. -/
theorem fourier_causalBlaschkeStep {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    𝓕 (causalBlaschkeStep a f) ξ =
      (((a : ℂ) - 2 * I * ξ) / ((a : ℂ) + 2 * I * ξ)) * 𝓕 f ξ := by
  let conv : ℝ → ℂ := causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f
  have hconv : Integrable conv :=
    (causalFourierExponential_integrable ha).integrable_convolution
      (ContinuousLinearMap.mul ℂ ℂ) hf
  unfold causalBlaschkeStep
  rw [show (fun y : ℝ => -f y + (2 * a : ℂ) *
      (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y) =
      (-1 : ℂ) • f + (2 * a : ℂ) • conv by
        funext y
        simp [conv]]
  change VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
      (((-1 : ℂ) • f) + ((2 * a : ℂ) • conv)) ξ = _
  change VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
      ((fun x => (-1 : ℂ) * f x) + (fun x => (2 * a : ℂ) * conv x)) ξ = _
  have hadd := congrFun (VectorFourier.fourierIntegral_add
    (e := 𝐞) (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner
    (hf.const_mul (-1 : ℂ)) (hconv.const_mul (2 * a : ℂ))) ξ
  rw [hadd]
  have hneg := congrFun (VectorFourier.fourierIntegral_const_smul
    𝐞 volume (innerₗ ℝ) f (-1 : ℂ)) ξ
  have hmul := congrFun (VectorFourier.fourierIntegral_const_smul
    𝐞 volume (innerₗ ℝ) conv (2 * a : ℂ)) ξ
  have hneg' :
      VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) (fun x => (-1 : ℂ) * f x) ξ =
        (-1 : ℂ) * VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) f ξ := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hneg
  have hmul' :
      VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) (fun x => (2 * a : ℂ) * conv x) ξ =
        (2 * a : ℂ) * VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) conv ξ := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hmul
  simp only [Pi.add_apply]
  rw [hneg', hmul']
  change (-1 : ℂ) * 𝓕 f ξ + (2 * a : ℂ) * 𝓕 conv ξ = _
  change (-1 : ℂ) * 𝓕 f ξ + (2 * a : ℂ) *
      𝓕 (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) ξ = _
  rw [fourier_mul_convolution_eq_of_integrable
      (causalFourierExponential_integrable ha) hf ξ,
    fourier_causalFourierExponential ha ξ]
  have hz : (a : ℂ) + 2 * I * ξ ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    exact ha.ne' hre
  field_simp [hz]
  ring

/-- Convolution of two pointwise causal functions is pointwise causal. -/
theorem convolution_eq_zero_of_neg
    {f g : ℝ → ℂ} (hf : ∀ y < 0, f y = 0) (hg : ∀ y < 0, g y = 0)
    {y : ℝ} (hy : y < 0) :
    (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) y = 0 := by
  rw [MeasureTheory.convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  by_cases ht : t < 0
  · rw [hf t ht]
    simp
  · rw [hg (y - t) (by linarith)]
    simp

theorem causalFourierExponential_eq_zero_of_neg (a : ℝ) {y : ℝ} (hy : y < 0) :
    causalFourierExponential a y = 0 := by
  unfold causalFourierExponential
  rw [Set.indicator_of_notMem]
  simpa only [Set.mem_Ioi, not_lt] using hy.le

/-- The source-side implementation of a Blaschke factor preserves pointwise causal support. -/
theorem causalBlaschkeStep_eq_zero_of_neg {a : ℝ} {f : ℝ → ℂ}
    (hf : ∀ y < 0, f y = 0) {y : ℝ} (hy : y < 0) :
    causalBlaschkeStep a f y = 0 := by
  have hconv := convolution_eq_zero_of_neg
    (f := causalFourierExponential a) (g := f)
    (fun y hy => causalFourierExponential_eq_zero_of_neg a hy) hf hy
  rw [causalBlaschkeStep, hf y hy, hconv]
  simp

end RHTower
