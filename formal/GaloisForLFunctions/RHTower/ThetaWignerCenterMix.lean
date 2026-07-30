import GaloisForLFunctions.RHTower.PrimeArchThetaFirstMoment
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Center mixing of a Wigner distribution

The Hedenmalm orientation current first mixes the Wigner center variable against the positive
radial weight `r sinh (a r)`.  This file isolates the exact Fubini bridge: the radial Wigner
current is the Fourier transform of one center-mixed density.

The general theorem takes the absolute-integrability condition required by Fubini explicitly.
Discharging that condition for the actual theta-cusp source is a separate analytic step.  No
positivity or Riemann-hypothesis assumption occurs here.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- Fourier phase in the difference variable, with the normalization used by the theta Wigner
distribution. -/
def thetaWignerDifferencePhase (b t : ℝ) : ℂ :=
  Complex.exp ((((2 * b * t : ℝ) : ℂ) * I))

/-- Wigner distribution of a complex source, using the center coordinate `y` and difference
frequency `b`. -/
def thetaWignerDistribution (k : ℝ → ℂ) (y b : ℝ) : ℂ :=
  ∫ t : ℝ,
    k (y + t) * (starRingEnd ℂ) (k (y - t)) * thetaWignerDifferencePhase b t

/-- The density obtained by mixing positive Wigner centers against `r sinh (a r)`. -/
def thetaWignerCenterMixedDensity (k : ℝ → ℂ) (a t : ℝ) : ℂ :=
  ∫ r : ℝ in Ioi 0,
    (r * Real.sinh (a * r) : ℝ) *
      (k (r / 2 + t) * (starRingEnd ℂ) (k (r / 2 - t)))

/-- Product-space kernel whose two iterated integrals are respectively the Fourier transform of
the center-mixed density and the radial Wigner current. -/
def thetaWignerCenterMixKernel
    (k : ℝ → ℂ) (a b : ℝ) (p : ℝ × ℝ) : ℂ :=
  (p.1 * Real.sinh (a * p.1) : ℝ) *
    (k (p.1 / 2 + p.2) * (starRingEnd ℂ) (k (p.1 / 2 - p.2))) *
      thetaWignerDifferencePhase b p.2

/-- **Center-mixing Fubini identity.**  Whenever the natural product kernel is absolutely
integrable, the Fourier transform of the center-mixed density is exactly the radial Wigner
current. -/
theorem integral_thetaWignerCenterMixedDensity_mul_phase
    (k : ℝ → ℂ) (a b : ℝ)
    (hInt : Integrable (thetaWignerCenterMixKernel k a b)
      ((volume.restrict (Ioi 0)).prod volume)) :
    (∫ t : ℝ,
        thetaWignerCenterMixedDensity k a t * thetaWignerDifferencePhase b t) =
      ∫ r : ℝ in Ioi 0,
        (r * Real.sinh (a * r) : ℝ) * thetaWignerDistribution k (r / 2) b := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  have hInt' : Integrable
      (Function.uncurry fun r t => thetaWignerCenterMixKernel k a b (r, t))
      (mu.prod volume) := hInt
  have hswap := MeasureTheory.integral_integral_swap hInt'
  change (∫ t : ℝ, (∫ r : ℝ, _ ∂mu) * thetaWignerDifferencePhase b t) =
    ∫ r : ℝ, _ ∂mu
  rw [show (fun t : ℝ => (∫ r : ℝ,
      (r * Real.sinh (a * r) : ℝ) *
        (k (r / 2 + t) * (starRingEnd ℂ) (k (r / 2 - t))) ∂mu) *
        thetaWignerDifferencePhase b t) =
      fun t => ∫ r : ℝ, thetaWignerCenterMixKernel k a b (r, t) ∂mu by
    funext t
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with r
    simp [thetaWignerCenterMixKernel]]
  rw [← hswap]
  apply integral_congr_ae
  filter_upwards with r
  rw [thetaWignerDistribution, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [thetaWignerCenterMixKernel]
  push_cast
  ring

/-! ## Absolute convergence for the actual theta source -/

/-- The real theta-cusp source regarded as a complex-valued function. -/
def thetaCuspComplexSource (x : ℝ) : ℂ := (thetaCuspFullSource x : ℂ)

/-- Global exponential bound for the actual theta-cusp source. -/
theorem abs_thetaCuspFullSource_le_exp_neg_abs (x : ℝ) :
    |thetaCuspFullSource x| ≤
      thetaCuspDerivativeExpConstant 0 * Real.exp (-|x|) := by
  by_cases hx : 0 ≤ x
  · simpa [abs_of_nonneg hx] using
      (abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg 0 hx)
  · have hx' : 0 ≤ -x := by linarith
    have h := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg 0 hx'
    rw [iteratedDeriv_zero, thetaCuspFullSource_neg] at h
    simpa [abs_of_neg (lt_of_not_ge hx)] using h

/-- The two theta arguments jointly retain at least half the radial decay and all the difference
decay. -/
theorem abs_add_half_add_abs_half_sub_ge_mix (r t : ℝ) (hr : 0 ≤ r) :
    r / 2 + |t| ≤ |r / 2 + t| + |r / 2 - t| := by
  have hr' : r ≤ |r / 2 + t| + |r / 2 - t| := by
    calc
      r = |(r / 2 + t) + (r / 2 - t)| := by simp [abs_of_nonneg hr]
      _ ≤ |r / 2 + t| + |r / 2 - t| := abs_add_le _ _
  have ht' : 2 * |t| ≤ |r / 2 + t| + |r / 2 - t| := by
    calc
      2 * |t| = |(r / 2 + t) - (r / 2 - t)| := by
        rw [show (r / 2 + t) - (r / 2 - t) = 2 * t by ring, abs_mul]
        norm_num
      _ ≤ |r / 2 + t| + |r / 2 - t| := abs_sub _ _
  linarith

/-- Pointwise product majorant for the actual theta center-mixing kernel. -/
theorem norm_thetaWignerCenterMixKernel_le
    {a r t b : ℝ} (hr : 0 < r) (ha0 : 0 ≤ a) :
    ‖thetaWignerCenterMixKernel thetaCuspComplexSource a b (r, t)‖ ≤
      (thetaCuspDerivativeExpConstant 0) ^ 2 * r *
        Real.exp (-(1 / 2 - a) * r) * Real.exp (-|t|) := by
  let C := thetaCuspDerivativeExpConstant 0
  have hC : 0 ≤ C := thetaCuspDerivativeExpConstant_nonneg 0
  have hsinh0 : 0 ≤ Real.sinh (a * r) :=
    Real.sinh_nonneg_iff.mpr (mul_nonneg ha0 hr.le)
  have hsinh : Real.sinh (a * r) ≤ Real.exp (a * r) := by
    rw [Real.sinh_eq]
    have he : 0 < Real.exp (-(a * r)) := Real.exp_pos _
    nlinarith [Real.exp_pos (a * r)]
  have hk1 := abs_thetaCuspFullSource_le_exp_neg_abs (r / 2 + t)
  have hk2 := abs_thetaCuspFullSource_le_exp_neg_abs (r / 2 - t)
  have hmix := abs_add_half_add_abs_half_sub_ge_mix r t hr.le
  have hexp :
      Real.exp (-|r / 2 + t|) * Real.exp (-|r / 2 - t|) ≤
        Real.exp (-r / 2) * Real.exp (-|t|) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  change ‖((r * Real.sinh (a * r) : ℝ) : ℂ) *
      (thetaCuspComplexSource (r / 2 + t) *
        (starRingEnd ℂ) (thetaCuspComplexSource (r / 2 - t))) *
        thetaWignerDifferencePhase b t‖ ≤ _
  simp only [thetaCuspComplexSource]
  rw [norm_mul, norm_mul, norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos hr, abs_of_nonneg hsinh0,
    norm_mul, RCLike.norm_conj,
    norm_real, Real.norm_eq_abs, norm_real, Real.norm_eq_abs,
    thetaWignerDifferencePhase, Complex.norm_exp]
  simp only [mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
    sub_self, Real.exp_zero, mul_one]
  change r * Real.sinh (a * r) *
      (|thetaCuspFullSource (r / 2 + t)| *
        |thetaCuspFullSource (r / 2 - t)|) ≤ _
  calc
    _ ≤ r * Real.exp (a * r) *
        ((C * Real.exp (-|r / 2 + t|)) *
          (C * Real.exp (-|r / 2 - t|))) := by
      gcongr
    _ = C ^ 2 * r * Real.exp (a * r) *
        (Real.exp (-|r / 2 + t|) * Real.exp (-|r / 2 - t|)) := by ring
    _ ≤ C ^ 2 * r * Real.exp (a * r) *
        (Real.exp (-r / 2) * Real.exp (-|t|)) := by
      gcongr
    _ = C ^ 2 * r * Real.exp (-(1 / 2 - a) * r) * Real.exp (-|t|) := by
      have he : Real.exp (a * r) * Real.exp (-r / 2) =
          Real.exp (-(1 / 2 - a) * r) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [show C ^ 2 * r * Real.exp (a * r) *
          (Real.exp (-r / 2) * Real.exp (-|t|)) =
          C ^ 2 * r * (Real.exp (a * r) * Real.exp (-r / 2)) *
            Real.exp (-|t|) by ring, he]

/-- The elementary difference-variable majorant is integrable on the real line. -/
theorem integrable_exp_neg_abs :
    Integrable (fun t : ℝ => Real.exp (-|t|)) := by
  have hpos : IntegrableOn (fun t : ℝ => Real.exp (-|t|)) (Ioi 0) := by
    have h := integrableOn_exp_neg_Ioi 0
    exact h.congr_fun
      (fun (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) => by
        have hx' : 0 < x := hx
        simp only [abs_of_pos hx'])
      measurableSet_Ioi
  have hneg : IntegrableOn (fun t : ℝ => Real.exp (-|t|)) (Iic 0) := by
    have h := integrableOn_exp_Iic 0
    exact h.congr_fun
      (fun (x : ℝ) (hx : x ∈ Iic (0 : ℝ)) => by
        have hx' : x ≤ 0 := hx
        simp only [abs_of_nonpos hx', neg_neg])
      measurableSet_Iic
  simpa [Ioi_union_Iic] using hpos.union hneg

/-- The actual theta center-mixing kernel is absolutely integrable throughout the critical
aperture. -/
theorem integrable_thetaWignerCenterMixKernel
    {a b : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    Integrable (thetaWignerCenterMixKernel thetaCuspComplexSource a b)
      ((volume.restrict (Ioi 0)).prod volume) := by
  let C := thetaCuspDerivativeExpConstant 0
  let c : ℝ := 1 / 2 - a
  let outer : ℝ → ℝ := fun r =>
    C ^ 2 * (r ^ (1 : ℝ) * Real.exp (-c * r ^ (1 : ℝ)))
  let inner : ℝ → ℝ := fun t => Real.exp (-|t|)
  have hc : 0 < c := by dsimp [c]; linarith
  have houter0 : IntegrableOn
      (fun r : ℝ => r ^ (1 : ℝ) * Real.exp (-c * r ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 1) (b := c) (by norm_num) (by norm_num) hc
  have houter : Integrable outer (volume.restrict (Ioi 0)) := by
    exact houter0.const_mul (C ^ 2)
  have hinner : Integrable inner volume := integrable_exp_neg_abs
  have hmajor : Integrable (fun p : ℝ × ℝ => outer p.1 * inner p.2)
      ((volume.restrict (Ioi 0)).prod volume) :=
    houter.mul_prod hinner
  have hresult : Integrable
      (thetaWignerCenterMixKernel thetaCuspComplexSource a b)
      ((volume.restrict (Ioi 0)).prod volume) := by
    apply hmajor.mono
    · have hk : Continuous thetaCuspFullSource :=
        contDiff_thetaCuspFullSource.continuous
      unfold thetaWignerCenterMixKernel thetaCuspComplexSource
        thetaWignerDifferencePhase
      exact (by fun_prop (disch := aesop) : Continuous (fun p : ℝ × ℝ =>
        ((p.1 * Real.sinh (a * p.1) : ℝ) : ℂ) *
          (((thetaCuspFullSource (p.1 / 2 + p.2) : ℝ) : ℂ) *
            (starRingEnd ℂ) (((thetaCuspFullSource (p.1 / 2 - p.2) : ℝ) : ℂ))) *
              Complex.exp ((((2 * b * p.2 : ℝ) : ℂ) * I)))).aestronglyMeasurable
    · rw [show volume = volume.restrict (Set.univ : Set ℝ) by simp,
        MeasureTheory.Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp
      have hr : 0 < p.1 := hp.1
      have h := norm_thetaWignerCenterMixKernel_le (b := b) (t := p.2) hr ha0
      have hmajor0 : 0 ≤ outer p.1 * inner p.2 := by
        dsimp [outer, inner]
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hmajor0]
      dsimp [outer, inner, c, C]
      simpa [Real.rpow_one, mul_assoc] using h
  simpa using hresult

/-- **Premise-free theta specialization.**  Throughout the critical aperture, the Fourier
transform of the actual center-mixed theta density is exactly its radial Wigner current. -/
theorem integral_thetaWignerCenterMixedDensity_mul_phase_thetaCusp
    {a b : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    (∫ t : ℝ,
        thetaWignerCenterMixedDensity thetaCuspComplexSource a t *
          thetaWignerDifferencePhase b t) =
      ∫ r : ℝ in Ioi 0,
        (r * Real.sinh (a * r) : ℝ) *
          thetaWignerDistribution thetaCuspComplexSource (r / 2) b :=
  integral_thetaWignerCenterMixedDensity_mul_phase
    thetaCuspComplexSource a b (integrable_thetaWignerCenterMixKernel ha0 ha)

/-! ## Pointwise-positive real center density -/

/-- The real center-mixed density associated with the theta-cusp source. -/
def thetaCuspCenterMixedDensity (a t : ℝ) : ℝ :=
  ∫ r : ℝ in Ioi 0,
    r * Real.sinh (a * r) *
      (thetaCuspFullSource (r / 2 + t) * thetaCuspFullSource (r / 2 - t))

/-- The actual theta-cusp source is nonnegative on the whole logarithmic line. -/
theorem thetaCuspFullSource_nonneg (x : ℝ) : 0 ≤ thetaCuspFullSource x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [← thetaCuspFullSource_neg x]
    exact (thetaCuspFullSource_pos_of_pos (by linarith)).le
  · have hlim : Tendsto (fun n : ℕ =>
        thetaCuspFullSource (1 / ((n : ℝ) + 1))) atTop
        (𝓝 (thetaCuspFullSource 0)) :=
      contDiff_thetaCuspFullSource.continuous.continuousAt.tendsto.comp
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact ge_of_tendsto' hlim fun n =>
      (thetaCuspFullSource_pos_of_pos (by positivity :
        0 < 1 / ((n : ℝ) + 1))).le
  · exact (thetaCuspFullSource_pos_of_pos hx).le

/-- Center mixing produces an even density before any orientation theorem is used. -/
theorem thetaCuspCenterMixedDensity_even (a t : ℝ) :
    thetaCuspCenterMixedDensity a (-t) = thetaCuspCenterMixedDensity a t := by
  unfold thetaCuspCenterMixedDensity
  apply integral_congr_ae
  filter_upwards with r
  ring

/-- Center mixing produces a pointwise nonnegative density for every nonnegative aperture. -/
theorem thetaCuspCenterMixedDensity_nonneg {a t : ℝ} (ha : 0 ≤ a) :
    0 ≤ thetaCuspCenterMixedDensity a t := by
  unfold thetaCuspCenterMixedDensity
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact mul_nonneg
    (mul_nonneg hr.le (Real.sinh_nonneg_iff.mpr (mul_nonneg ha hr.le)))
    (mul_nonneg (thetaCuspFullSource_nonneg _) (thetaCuspFullSource_nonneg _))

/-- The complex center density used in the Fourier identity is exactly the real positive theta
density embedded in `ℂ`. -/
theorem thetaWignerCenterMixedDensity_thetaCusp_eq_ofReal (a t : ℝ) :
    thetaWignerCenterMixedDensity thetaCuspComplexSource a t =
      (thetaCuspCenterMixedDensity a t : ℂ) := by
  rw [thetaWignerCenterMixedDensity, thetaCuspCenterMixedDensity,
    ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with r
  simp only [thetaCuspComplexSource, Complex.conj_ofReal]
  norm_cast

/-- The pointwise-positive theta center density is integrable throughout the critical aperture. -/
theorem integrable_thetaCuspCenterMixedDensity
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    Integrable (thetaCuspCenterMixedDensity a) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  have hprod := integrable_thetaWignerCenterMixKernel (b := 0) ha0 ha
  have hiter : Integrable (fun t : ℝ => ∫ r : ℝ,
      thetaWignerCenterMixKernel thetaCuspComplexSource a 0 (r, t) ∂mu) volume :=
    hprod.integral_prod_right
  have heq : (fun t : ℝ => ∫ r : ℝ,
      thetaWignerCenterMixKernel thetaCuspComplexSource a 0 (r, t) ∂mu) =
      fun t => thetaWignerCenterMixedDensity thetaCuspComplexSource a t := by
    funext t
    rw [thetaWignerCenterMixedDensity]
    apply integral_congr_ae
    filter_upwards with r
    simp [thetaWignerCenterMixKernel, thetaWignerDifferencePhase]
  rw [heq] at hiter
  rw [show (fun t => thetaWignerCenterMixedDensity thetaCuspComplexSource a t) =
      fun t => (thetaCuspCenterMixedDensity a t : ℂ) by
    funext t
    exact thetaWignerCenterMixedDensity_thetaCusp_eq_ofReal a t] at hiter
  simpa using hiter.re

/-- The center-mixed theta density is continuous throughout the critical aperture. -/
theorem continuous_thetaCuspCenterMixedDensity
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    Continuous (thetaCuspCenterMixedDensity a) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let C := thetaCuspDerivativeExpConstant 0
  let c : ℝ := 1 / 2 - a
  let bound : ℝ → ℝ := fun r =>
    C ^ 2 * (r ^ (1 : ℝ) * Real.exp (-c * r ^ (1 : ℝ)))
  let F : ℝ → ℝ → ℝ := fun t r =>
    r * Real.sinh (a * r) *
      (thetaCuspFullSource (r / 2 + t) * thetaCuspFullSource (r / 2 - t))
  have hc : 0 < c := by dsimp [c]; linarith
  have hbound : Integrable bound mu := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 1) (b := c) (by norm_num) (by norm_num) hc
    exact h.const_mul (C ^ 2)
  have hFmeas : ∀ t, AEStronglyMeasurable (F t) mu := by
    intro t
    have hk : Continuous thetaCuspFullSource :=
      contDiff_thetaCuspFullSource.continuous
    dsimp [F]
    exact (by fun_prop (disch := aesop) : Continuous (fun r : ℝ =>
      r * Real.sinh (a * r) *
        (thetaCuspFullSource (r / 2 + t) *
          thetaCuspFullSource (r / 2 - t)))).aestronglyMeasurable
  have hle : ∀ t, ∀ᵐ r ∂mu, ‖F t r‖ ≤ bound r := by
    intro t
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hk := norm_thetaWignerCenterMixKernel_le (b := 0) (t := t) hr ha0
    have hphase : thetaWignerDifferencePhase 0 t = 1 := by
      simp [thetaWignerDifferencePhase]
    have heq : ‖F t r‖ =
        ‖thetaWignerCenterMixKernel thetaCuspComplexSource a 0 (r, t)‖ := by
      rw [thetaWignerCenterMixKernel, hphase]
      simp only [mul_one, F, thetaCuspComplexSource, Complex.conj_ofReal]
      norm_cast
    rw [heq]
    calc
      _ ≤ C ^ 2 * r * Real.exp (-(1 / 2 - a) * r) * Real.exp (-|t|) := hk
      _ ≤ C ^ 2 * r * Real.exp (-(1 / 2 - a) * r) := by
        exact mul_le_of_le_one_right
          (mul_nonneg (mul_nonneg (sq_nonneg C) hr.le) (Real.exp_pos _).le)
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg t)))
      _ = bound r := by simp [bound, c, Real.rpow_one, mul_assoc]
  have hcont : ∀ᵐ r ∂mu, Continuous fun t => F t r := by
    filter_upwards with r
    have hk : Continuous thetaCuspFullSource :=
      contDiff_thetaCuspFullSource.continuous
    dsimp [F]
    fun_prop (disch := aesop)
  have h := MeasureTheory.continuous_of_dominated hFmeas hle hbound hcont
  change Continuous (fun t : ℝ =>
    ∫ r : ℝ in Ioi 0,
      r * Real.sinh (a * r) *
        (thetaCuspFullSource (r / 2 + t) * thetaCuspFullSource (r / 2 - t)))
  simpa [F, mu] using h

/-- At every positive aperture below the critical boundary, the theta center-mixed density is
strictly positive at every center.  The proof is genuinely analytic: domination supplies radial
integrability, while a single positive radial point and openness of the support force a positive
integral. -/
theorem thetaCuspCenterMixedDensity_pos
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (t : ℝ) :
    0 < thetaCuspCenterMixedDensity a t := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let C := thetaCuspDerivativeExpConstant 0
  let c : ℝ := 1 / 2 - a
  let f : ℝ → ℝ := fun r =>
    r * Real.sinh (a * r) *
      (thetaCuspFullSource (r / 2 + t) * thetaCuspFullSource (r / 2 - t))
  let bound : ℝ → ℝ := fun r =>
    C ^ 2 * (r ^ (1 : ℝ) * Real.exp (-c * r ^ (1 : ℝ)))
  have hc : 0 < c := by dsimp [c]; linarith
  have hbound : Integrable bound mu := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 1) (b := c) (by norm_num) (by norm_num) hc
    exact h.const_mul (C ^ 2)
  have hfint : Integrable f mu := by
    apply hbound.mono
    · have hk : Continuous thetaCuspFullSource :=
        contDiff_thetaCuspFullSource.continuous
      dsimp [f]
      exact (by fun_prop (disch := aesop) : Continuous (fun r : ℝ =>
        r * Real.sinh (a * r) *
          (thetaCuspFullSource (r / 2 + t) *
            thetaCuspFullSource (r / 2 - t)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hk := norm_thetaWignerCenterMixKernel_le (b := 0) (t := t) hr ha0.le
      have hphase : thetaWignerDifferencePhase 0 t = 1 := by
        simp [thetaWignerDifferencePhase]
      have heq : ‖f r‖ =
          ‖thetaWignerCenterMixKernel thetaCuspComplexSource a 0 (r, t)‖ := by
        rw [thetaWignerCenterMixKernel, hphase]
        simp only [mul_one, f, thetaCuspComplexSource, Complex.conj_ofReal]
        norm_cast
      rw [heq]
      calc
        _ ≤ C ^ 2 * r * Real.exp (-(1 / 2 - a) * r) * Real.exp (-|t|) := hk
        _ ≤ C ^ 2 * r * Real.exp (-(1 / 2 - a) * r) := by
          exact mul_le_of_le_one_right
            (mul_nonneg (mul_nonneg (sq_nonneg C) hr.le) (Real.exp_pos _).le)
            (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg t)))
        _ = ‖bound r‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          · simp [bound, c, Real.rpow_one, mul_assoc]
          · dsimp [bound]
            exact mul_nonneg (sq_nonneg C)
              (mul_nonneg (Real.rpow_nonneg hr.le _)
                (Real.exp_pos _).le)
  have hfnn : 0 ≤ᵐ[mu] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg
      (mul_nonneg hr.le (Real.sinh_nonneg_iff.mpr (mul_nonneg ha0.le hr.le)))
      (mul_nonneg (thetaCuspFullSource_nonneg _) (thetaCuspFullSource_nonneg _))
  rw [thetaCuspCenterMixedDensity]
  apply (setIntegral_pos_iff_support_of_nonneg_ae hfnn hfint).2
  have hfcont : Continuous f := by
    have hk : Continuous thetaCuspFullSource :=
      contDiff_thetaCuspFullSource.continuous
    dsimp [f]
    fun_prop (disch := aesop)
  have hopen : IsOpen (Function.support f ∩ Ioi (0 : ℝ)) :=
    hfcont.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  let r₀ : ℝ := 2 * |t| + 2
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  refine ⟨r₀, ?_, hr₀⟩
  change f r₀ ≠ 0
  have hplus : 0 < r₀ / 2 + t := by
    dsimp [r₀]
    nlinarith [neg_le_abs t]
  have hminus : 0 < r₀ / 2 - t := by
    dsimp [r₀]
    nlinarith [le_abs_self t]
  dsimp [f]
  exact mul_ne_zero
    (mul_ne_zero hr₀.ne' (Real.sinh_ne_zero.mpr (mul_ne_zero ha0.ne' hr₀.ne')))
    (mul_ne_zero (thetaCuspFullSource_pos_of_pos hplus).ne'
      (thetaCuspFullSource_pos_of_pos hminus).ne')

end RHTower
