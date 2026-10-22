import GaloisForLFunctions.RHTower.CCM.CCMFUCompactAutocorrelationDeningerAmplification
import GaloisForLFunctions.RHTower.Suzuki.SuzukiFirstMomentContinuousCriticalErrorClassification
import GaloisForLFunctions.RHTower.XiMassCriticalErrorFlux
import GaloisForLFunctions.RHTower.CCM.CCMSawtoothDilationMean
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszFUCurvatureTransport
import GaloisForLFunctions.HTGeometry.BanachIntervalIntegralAbsoluteContinuity
import GaloisForLFunctions.HTGeometry.ContactOrderDefectLimit
import GaloisForLFunctions.RHTower.HermiteGaussianEnvelope
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCCMExactSourceIdentification

/-!
# CCM--FU Littlewood no-go

Reciprocal compact autocorrelation packets give an exact arithmetic--spectral weld.
A square-root Chebyshev remainder bound uniformly bounds their critical pairing,
while RH forces the same Deninger spectral response to escape at arbitrarily small
scales.  Hence RH excludes the square-root remainder bound, and the classified
CCM--FU first-moment and central unit-Riesz producers are both impossible.
-/

open Complex Filter MeasureTheory Set TopologicalSpace
open scoped FourierTransform

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

noncomputable section

def ccmFuTranslatedAutocorrelationDeriv (δ t x : ℝ) : ℝ :=
  deriv ccmFuAutocorrelationProfile ((x - t) / δ) / δ

theorem hasDerivAt_ccmFuTranslatedAutocorrelation
    {δ t : ℝ} (x : ℝ) :
    HasDerivAt (ccmFuTranslatedAutocorrelation δ t)
      (ccmFuTranslatedAutocorrelationDeriv δ t x) x := by
  have hprofile : HasDerivAt ccmFuAutocorrelationProfile
      (deriv ccmFuAutocorrelationProfile ((x - t) / δ)) ((x - t) / δ) :=
    (contDiff_ccmFuAutocorrelationProfile.differentiable (by simp) _).hasDerivAt
  have harg : HasDerivAt (fun x : ℝ => (x - t) / δ) (1 / δ) x := by
    simpa [one_div] using ((hasDerivAt_id x).sub_const t).div_const δ
  have hcomp := hprofile.comp x harg
  change HasDerivAt
    (fun x : ℝ => ccmFuAutocorrelationProfile ((x - t) / δ))
    (deriv ccmFuAutocorrelationProfile ((x - t) / δ) / δ) x
  simpa only [Function.comp_def, div_eq_mul_inv, one_mul] using hcomp

theorem continuous_ccmFuTranslatedAutocorrelationDeriv (δ t : ℝ) :
    Continuous (ccmFuTranslatedAutocorrelationDeriv δ t) := by
  unfold ccmFuTranslatedAutocorrelationDeriv
  have hderiv : Continuous (deriv ccmFuAutocorrelationProfile) :=
    contDiff_ccmFuAutocorrelationProfile.continuous_deriv (by simp)
  fun_prop

theorem ccmFuTranslatedAutocorrelation_zero_on_compl
    {δ t : ℝ} (hδ : 0 < δ) :
    Set.EqOn (ccmFuTranslatedAutocorrelation δ t) (fun _ : ℝ => 0)
      (ccmFuDeningerSupport δ t : Set ℝ)ᶜ := by
  intro x hx
  have hz := ccmFuDeningerProfile_zero_on_compl hδ hx
  rw [ccmFuDeningerProfile] at hz
  exact (mul_eq_zero.mp hz).resolve_left (Real.exp_ne_zero _)

theorem hasCompactSupport_ccmFuTranslatedAutocorrelation
    {δ t : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (ccmFuTranslatedAutocorrelation δ t) := by
  exact HasCompactSupport.intro (ccmFuDeningerSupport δ t).isCompact
    (ccmFuTranslatedAutocorrelation_zero_on_compl hδ)

theorem continuous_ccmFuTranslatedAutocorrelation (δ t : ℝ) :
    Continuous (ccmFuTranslatedAutocorrelation δ t) :=
  (contDiff_ccmFuAutocorrelationProfile.comp (by fun_prop)).continuous

theorem integrable_ccmFuTranslatedAutocorrelation
    {δ t : ℝ} (hδ : 0 < δ) :
    Integrable (ccmFuTranslatedAutocorrelation δ t) :=
  (continuous_ccmFuTranslatedAutocorrelation δ t).integrable_of_hasCompactSupport
    (hasCompactSupport_ccmFuTranslatedAutocorrelation hδ)

theorem ccmFuTranslatedAutocorrelationDeriv_eq_deriv
    (δ t x : ℝ) :
    ccmFuTranslatedAutocorrelationDeriv δ t x =
      deriv (ccmFuTranslatedAutocorrelation δ t) x := by
  exact (hasDerivAt_ccmFuTranslatedAutocorrelation x).deriv.symm

theorem hasCompactSupport_ccmFuTranslatedAutocorrelationDeriv
    {δ t : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (ccmFuTranslatedAutocorrelationDeriv δ t) := by
  rw [funext (ccmFuTranslatedAutocorrelationDeriv_eq_deriv δ t)]
  exact (hasCompactSupport_ccmFuTranslatedAutocorrelation hδ).deriv

theorem integrable_ccmFuTranslatedAutocorrelationDeriv
    {δ t : ℝ} (hδ : 0 < δ) :
    Integrable (ccmFuTranslatedAutocorrelationDeriv δ t) :=
  (continuous_ccmFuTranslatedAutocorrelationDeriv δ t).integrable_of_hasCompactSupport
    (hasCompactSupport_ccmFuTranslatedAutocorrelationDeriv hδ)

theorem ccmFuTranslatedAutocorrelation_eq_zero_of_lt_lower
    {δ t x : ℝ} (hδ : 0 < δ)
    (hx : x < t - δ * ccmFuAutocorrelationTest.radius) :
    ccmFuTranslatedAutocorrelation δ t x = 0 := by
  apply ccmFuTranslatedAutocorrelation_zero_on_compl hδ
  change x ∉ Icc (t - δ * ccmFuAutocorrelationTest.radius)
    (t + δ * ccmFuAutocorrelationTest.radius)
  exact fun h => (not_le_of_gt hx) h.1

theorem ccmFuTranslatedAutocorrelationDeriv_eq_zero_of_lt_lower
    {δ t x : ℝ} (hδ : 0 < δ)
    (hx : x < t - δ * ccmFuAutocorrelationTest.radius) :
    ccmFuTranslatedAutocorrelationDeriv δ t x = 0 := by
  rw [ccmFuTranslatedAutocorrelationDeriv_eq_deriv]
  have heq : ccmFuTranslatedAutocorrelation δ t =ᶠ[nhds x] fun _ : ℝ => 0 := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact ccmFuTranslatedAutocorrelation_eq_zero_of_lt_lower hδ hy
  rw [heq.deriv_eq]
  simp

theorem ccmFuTranslatedAutocorrelation_eq_zero_of_upper_lt
    {δ t x : ℝ} (hδ : 0 < δ)
    (hx : t + δ * ccmFuAutocorrelationTest.radius < x) :
    ccmFuTranslatedAutocorrelation δ t x = 0 := by
  apply ccmFuTranslatedAutocorrelation_zero_on_compl hδ
  change x ∉ Icc (t - δ * ccmFuAutocorrelationTest.radius)
    (t + δ * ccmFuAutocorrelationTest.radius)
  exact fun h => (not_le_of_gt hx) h.2

theorem ccmFuTranslatedAutocorrelation_two_mul_eq_zero
    {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    ccmFuTranslatedAutocorrelation δ t (2 * t) = 0 := by
  apply ccmFuTranslatedAutocorrelation_eq_zero_of_upper_lt hδ
  linarith

theorem criticalMellinStieltjesPairing_ccmFu_re_eq_errorFlux
    {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    (criticalMellinStieltjesPairing t
      (fun x => (ccmFuTranslatedAutocorrelation δ t x : ℂ))).re =
      -(∫ x in (0 : ℝ)..2 * t,
        criticalMellinCompletedError x *
          ccmFuTranslatedAutocorrelationDeriv δ t x) := by
  have ht0 : 0 ≤ t := by
    have hR : 0 ≤ ccmFuAutocorrelationTest.radius := by
      linarith [ccmFuAutocorrelationTest.one_lt_radius]
    nlinarith
  have hH : 0 ≤ 2 * t := by linarith
  have hderiv : ∀ x ∈ Icc (0 : ℝ) (2 * t),
      HasDerivAt
        (fun y => (ccmFuTranslatedAutocorrelation δ t y : ℂ))
        (ccmFuTranslatedAutocorrelationDeriv δ t x : ℂ) x := by
    intro x hx
    exact (hasDerivAt_ccmFuTranslatedAutocorrelation x).ofReal_comp
  have hderivInt : IntervalIntegrable
      (fun x => (ccmFuTranslatedAutocorrelationDeriv δ t x : ℂ))
      volume 0 (2 * t) := by
    exact (Complex.continuous_ofReal.comp
      (continuous_ccmFuTranslatedAutocorrelationDeriv δ t)).intervalIntegrable _ _
  rw [criticalMellinStieltjesPairing_integrationByParts ht0 hderiv hderivInt
    (by exact_mod_cast ccmFuTranslatedAutocorrelation_two_mul_eq_zero hδ ht),
    Complex.neg_re]
  rw [← intervalIntegral.integral_of_le hH]
  have hrealInt : IntervalIntegrable
      (fun x => criticalMellinCompletedError x *
        ccmFuTranslatedAutocorrelationDeriv δ t x) volume 0 (2 * t) :=
    by simpa only [mul_comm] using
      (intervalIntegrable_criticalMellinCompletedError_on_Icc hH).continuousOn_mul
        (continuous_ccmFuTranslatedAutocorrelationDeriv δ t).continuousOn
  have hcast := Complex.ofRealCLM.intervalIntegral_comp_comm hrealInt
  have hre :
      (∫ x in (0 : ℝ)..2 * t,
        (criticalMellinCompletedError x : ℂ) *
          (ccmFuTranslatedAutocorrelationDeriv δ t x : ℂ)).re =
        ∫ x in (0 : ℝ)..2 * t,
          criticalMellinCompletedError x *
            ccmFuTranslatedAutocorrelationDeriv δ t x := by
    simpa [Complex.ofRealCLM_apply, Complex.ofReal_mul] using congrArg Complex.re hcast
  rw [hre]

theorem integral_ccmFuTranslatedAutocorrelationDeriv_mul_cutoffPrimitive
    {H δ t : ℝ} (hH : 0 ≤ H) :
    (∫ u in (0 : ℝ)..H,
      ccmFuTranslatedAutocorrelationDeriv δ t u *
        (∫ x in (0 : ℝ)..u, criticalMellinNormalizedErrorCutoff H x)) =
      ccmFuTranslatedAutocorrelation δ t H *
          (∫ x in (0 : ℝ)..H, criticalMellinNormalizedErrorCutoff H x) -
        ∫ x in (0 : ℝ)..H,
          ccmFuTranslatedAutocorrelation δ t x *
            criticalMellinNormalizedErrorCutoff H x := by
  let Cg : ℝ :=
    criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp H) +
      Real.exp H
  have hg := measurable_criticalMellinNormalizedErrorCutoff H
  have hgb : ∀ x : ℝ, |criticalMellinNormalizedErrorCutoff H x| ≤ Cg :=
    fun x => abs_criticalMellinNormalizedErrorCutoff_le H x
  have hφ'meas : Measurable (ccmFuTranslatedAutocorrelationDeriv δ t) :=
    (continuous_ccmFuTranslatedAutocorrelationDeriv δ t).measurable
  have hφ : ∀ u ∈ Icc (0 : ℝ) H,
      HasDerivAt (ccmFuTranslatedAutocorrelation δ t)
        (ccmFuTranslatedAutocorrelationDeriv δ t u) u :=
    fun u _ => hasDerivAt_ccmFuTranslatedAutocorrelation u
  have hbdd := (isCompact_Icc : IsCompact (Icc (0 : ℝ) H)).bddAbove_image
    ((continuous_ccmFuTranslatedAutocorrelationDeriv δ t).abs.continuousOn)
  obtain ⟨Cd, hCd⟩ := hbdd
  have hφ'b : ∀ u ∈ Icc (0 : ℝ) H,
      |ccmFuTranslatedAutocorrelationDeriv δ t u| ≤ Cd := by
    intro u hu
    exact hCd ⟨u, hu, rfl⟩
  exact integral_deriv_mul_primitive hH hg hgb hφ'meas hφ hφ'b

theorem intervalIntegrable_criticalMellinNormalizedErrorCutoff
    (H a b : ℝ) :
    IntervalIntegrable (criticalMellinNormalizedErrorCutoff H) volume a b := by
  exact intervalIntegrable_of_bound
    (measurable_criticalMellinNormalizedErrorCutoff H)
    (fun x => abs_criticalMellinNormalizedErrorCutoff_le H x) a b

theorem integral_criticalMellinCompletedError_mul_ccmFuDeriv_decomposition
    {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    (∫ x in (0 : ℝ)..2 * t,
      criticalMellinCompletedError x *
        ccmFuTranslatedAutocorrelationDeriv δ t x) =
      (∫ x in (0 : ℝ)..2 * t,
        (1 - 2 * Real.exp (-x / 2)) *
          ccmFuTranslatedAutocorrelationDeriv δ t x) -
      (∫ x in (0 : ℝ)..2 * t,
        criticalMellinNormalizedErrorCutoff (2 * t) x *
          ccmFuTranslatedAutocorrelationDeriv δ t x) +
      (1 / 2 : ℝ) *
        ∫ x in (0 : ℝ)..2 * t,
          ccmFuTranslatedAutocorrelation δ t x *
            criticalMellinNormalizedErrorCutoff (2 * t) x := by
  let H : ℝ := 2 * t
  let D : ℝ → ℝ := ccmFuTranslatedAutocorrelationDeriv δ t
  let F : ℝ → ℝ := ccmFuTranslatedAutocorrelation δ t
  let E : ℝ → ℝ := criticalMellinNormalizedErrorCutoff H
  let P : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, E u
  let B : ℝ → ℝ := fun x => 1 - 2 * Real.exp (-x / 2)
  have hH : 0 ≤ H := by
    dsimp only [H]
    have hR : 0 ≤ ccmFuAutocorrelationTest.radius := by
      linarith [ccmFuAutocorrelationTest.one_lt_radius]
    nlinarith
  have hEint : IntervalIntegrable E volume 0 H := by
    exact intervalIntegrable_criticalMellinNormalizedErrorCutoff H 0 H
  have hPcont : ContinuousOn P (uIcc (0 : ℝ) H) := by
    exact (hEint.absolutelyContinuousOnInterval_intervalIntegral_normed
      (left_mem_uIcc)).continuousOn
  have hDcont : Continuous D := continuous_ccmFuTranslatedAutocorrelationDeriv δ t
  have hFcont : Continuous F := continuous_ccmFuTranslatedAutocorrelation δ t
  have hBcont : Continuous B := by
    dsimp only [B]
    fun_prop
  have hDint : IntervalIntegrable D volume 0 H := hDcont.intervalIntegrable _ _
  have hCDint : IntervalIntegrable
      (fun x => criticalMellinCompletedError x * D x) volume 0 H := by
    simpa only [mul_comm] using
      (intervalIntegrable_criticalMellinCompletedError_on_Icc hH).continuousOn_mul
        hDcont.continuousOn
  have hBDint : IntervalIntegrable (fun x => B x * D x) volume 0 H :=
    (hBcont.mul hDcont).intervalIntegrable _ _
  have hEDint : IntervalIntegrable (fun x => E x * D x) volume 0 H := by
    simpa only [mul_comm] using hEint.continuousOn_mul hDcont.continuousOn
  have hPDint : IntervalIntegrable (fun x => P x * D x) volume 0 H := by
    simpa only [mul_comm] using hDint.continuousOn_mul hPcont
  have hFEint : IntervalIntegrable (fun x => F x * E x) volume 0 H := by
    simpa only [mul_comm] using hEint.continuousOn_mul hFcont.continuousOn
  have hpoint : ∀ x ∈ Icc (0 : ℝ) H,
      criticalMellinCompletedError x * D x =
        B x * D x - E x * D x - (1 / 2 : ℝ) * (P x * D x) := by
    intro x hx
    rw [criticalMellinCompletedError_eq_cutoff_volterra hx]
    dsimp only [B, E, P]
    ring
  have hdecomp :
      (∫ x in (0 : ℝ)..H, criticalMellinCompletedError x * D x) =
        (∫ x in (0 : ℝ)..H, B x * D x) -
          (∫ x in (0 : ℝ)..H, E x * D x) -
            (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..H, P x * D x := by
    calc
      (∫ x in (0 : ℝ)..H, criticalMellinCompletedError x * D x) =
          ∫ x in (0 : ℝ)..H,
            (B x * D x - E x * D x) - (1 / 2 : ℝ) * (P x * D x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hpoint x (by simpa only [uIcc_of_le hH] using hx)
      _ = _ := by
        rw [intervalIntegral.integral_sub (hBDint.sub hEDint)
            (hPDint.const_mul (1 / 2 : ℝ)),
          intervalIntegral.integral_sub hBDint hEDint,
          intervalIntegral.integral_const_mul]
  have hfub := integral_ccmFuTranslatedAutocorrelationDeriv_mul_cutoffPrimitive
    (H := H) (δ := δ) (t := t) hH
  have hFend : ccmFuTranslatedAutocorrelation δ t H = 0 := by
    simpa only [H] using ccmFuTranslatedAutocorrelation_two_mul_eq_zero hδ ht
  have hPD : (∫ x in (0 : ℝ)..H, P x * D x) =
      -(∫ x in (0 : ℝ)..H, F x * E x) := by
    rw [show (fun x => P x * D x) = fun x => D x * P x by
      funext x; ring]
    dsimp only [D, P, E, F]
    rw [hfub, hFend, zero_mul, zero_sub]
  dsimp only [H, D, F, E, B] at hdecomp hPD ⊢
  rw [hdecomp, hPD]
  ring

theorem criticalMellinStieltjesPairing_ccmFu_re_decomposition
    {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    (criticalMellinStieltjesPairing t
      (fun x => (ccmFuTranslatedAutocorrelation δ t x : ℂ))).re =
      -(∫ x in (0 : ℝ)..2 * t,
        (1 - 2 * Real.exp (-x / 2)) *
          ccmFuTranslatedAutocorrelationDeriv δ t x) +
      (∫ x in (0 : ℝ)..2 * t,
        criticalMellinNormalizedErrorCutoff (2 * t) x *
          ccmFuTranslatedAutocorrelationDeriv δ t x) -
      (1 / 2 : ℝ) *
        ∫ x in (0 : ℝ)..2 * t,
          ccmFuTranslatedAutocorrelation δ t x *
            criticalMellinNormalizedErrorCutoff (2 * t) x := by
  rw [criticalMellinStieltjesPairing_ccmFu_re_eq_errorFlux hδ ht,
    integral_criticalMellinCompletedError_mul_ccmFuDeriv_decomposition hδ ht]
  ring

theorem integral_abs_comp_div_sub (f : ℝ → ℝ) {δ t : ℝ} (hδ : 0 < δ) :
    (∫ x : ℝ, |f ((x - t) / δ)|) =
      δ * ∫ x : ℝ, |f x| := by
  have h := integral_comp_affine
    (fun x : ℝ => |f ((x - t) / δ)|) t δ hδ
  have hleft : (fun s : ℝ => |f (((t + δ * s) - t) / δ)|) =
      fun s : ℝ => |f s| := by
    funext s
    congr 2
    field_simp [hδ.ne']
    ring
  rw [hleft] at h
  calc
    (∫ x : ℝ, |f ((x - t) / δ)|) =
        δ * (δ⁻¹ * ∫ x : ℝ, |f ((x - t) / δ)|) := by
      field_simp [hδ.ne']
    _ = δ * ∫ x : ℝ, |f x| := by rw [← h]

theorem integral_abs_ccmFuTranslatedAutocorrelation
    {δ t : ℝ} (hδ : 0 < δ) :
    (∫ x : ℝ, |ccmFuTranslatedAutocorrelation δ t x|) =
      δ * ∫ x : ℝ, |ccmFuAutocorrelationProfile x| := by
  exact integral_abs_comp_div_sub ccmFuAutocorrelationProfile hδ

theorem integral_abs_ccmFuTranslatedAutocorrelationDeriv
    {δ t : ℝ} (hδ : 0 < δ) :
    (∫ x : ℝ, |ccmFuTranslatedAutocorrelationDeriv δ t x|) =
      ∫ x : ℝ, |deriv ccmFuAutocorrelationProfile x| := by
  rw [show (fun x : ℝ => |ccmFuTranslatedAutocorrelationDeriv δ t x|) =
      fun x : ℝ => |deriv ccmFuAutocorrelationProfile ((x - t) / δ)| / δ by
    funext x
    rw [ccmFuTranslatedAutocorrelationDeriv, abs_div, abs_of_pos hδ]]
  rw [MeasureTheory.integral_div,
    integral_abs_comp_div_sub (deriv ccmFuAutocorrelationProfile) hδ]
  field_simp [hδ.ne']

theorem abs_integral_cutoff_mul_le_late_l1
    {H C : ℝ} (hC : 0 ≤ C)
    (herror : ∀ x : ℝ, Real.log 3 ≤ x →
      |criticalMellinNormalizedChebyshevError x| ≤ C)
    {K : ℝ → ℝ} (hK : Integrable K)
    (hsupport : ∀ x : ℝ, x < Real.log 3 → K x = 0) :
    |∫ x in (0 : ℝ)..H,
        criticalMellinNormalizedErrorCutoff H x * K x| ≤
      C * ∫ x : ℝ, |K x| := by
  have hpoint : ∀ x : ℝ,
      |criticalMellinNormalizedErrorCutoff H x * K x| ≤ C * |K x| := by
    intro x
    rw [criticalMellinNormalizedErrorCutoff]
    split_ifs with hx
    · by_cases hlate : Real.log 3 ≤ x
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (herror x hlate) (abs_nonneg _)
      · rw [hsupport x (lt_of_not_ge hlate), mul_zero, abs_zero, mul_zero]
    · rw [zero_mul, abs_zero]
      positivity
  have hmajor : Integrable (fun x : ℝ => C * |K x|) := hK.abs.const_mul C
  have hprodMeas : AEStronglyMeasurable
      (fun x : ℝ => criticalMellinNormalizedErrorCutoff H x * K x) :=
    (measurable_criticalMellinNormalizedErrorCutoff H).aestronglyMeasurable.mul
      hK.aestronglyMeasurable
  have hprod : Integrable
      (fun x : ℝ => criticalMellinNormalizedErrorCutoff H x * K x) := by
    refine hmajor.mono' hprodMeas ?_
    filter_upwards with x
    exact hpoint x
  calc
    |∫ x in (0 : ℝ)..H,
        criticalMellinNormalizedErrorCutoff H x * K x| ≤
        ∫ x : ℝ, |criticalMellinNormalizedErrorCutoff H x * K x| :=
      abs_intervalIntegral_le_integral_abs hprod 0 H
    _ ≤ ∫ x : ℝ, C * |K x| := by
      exact integral_mono_ae hprod.abs hmajor (ae_of_all _ hpoint)
    _ = C * ∫ x : ℝ, |K x| := MeasureTheory.integral_const_mul C _

theorem abs_one_sub_two_exp_neg_half_le_one {x : ℝ} (hx : 0 ≤ x) :
    |1 - 2 * Real.exp (-x / 2)| ≤ 1 := by
  have hexp0 : 0 ≤ Real.exp (-x / 2) := (Real.exp_pos _).le
  have hexp1 : Real.exp (-x / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def ccmFuPolarFluxIntegrand (δ t x : ℝ) : ℝ :=
  (1 - 2 * Real.exp (-x / 2)) *
    ccmFuTranslatedAutocorrelationDeriv δ t x

theorem continuous_ccmFuPolarFluxIntegrand (δ t : ℝ) :
    Continuous (ccmFuPolarFluxIntegrand δ t) := by
  have hinner : Continuous (fun x : ℝ => -x / 2) :=
    continuous_id.neg.div_const 2
  exact (continuous_const.sub
    (continuous_const.mul (Real.continuous_exp.comp hinner))).mul
      (continuous_ccmFuTranslatedAutocorrelationDeriv δ t)

theorem norm_ccmFuPolarFluxIntegrand_le_abs_deriv
    {δ t x : ℝ} (hx : 0 ≤ x) :
    ‖ccmFuPolarFluxIntegrand δ t x‖ ≤
      ‖ccmFuTranslatedAutocorrelationDeriv δ t x‖ := by
  have hf : ‖1 - 2 * Real.exp (-x / 2)‖ ≤ 1 :=
    (Real.norm_eq_abs _).trans_le
      (abs_one_sub_two_exp_neg_half_le_one hx)
  calc
    ‖ccmFuPolarFluxIntegrand δ t x‖ =
        ‖(1 - 2 * Real.exp (-x / 2)) *
          ccmFuTranslatedAutocorrelationDeriv δ t x‖ := rfl
    _ =
        ‖1 - 2 * Real.exp (-x / 2)‖ *
          ‖ccmFuTranslatedAutocorrelationDeriv δ t x‖ :=
      norm_mul _ _
    _ ≤ 1 * ‖ccmFuTranslatedAutocorrelationDeriv δ t x‖ :=
      mul_le_mul_of_nonneg_right hf (norm_nonneg _)
    _ = ‖ccmFuTranslatedAutocorrelationDeriv δ t x‖ := one_mul _

theorem abs_integral_polarFlux_mul_ccmFuDeriv_le
    {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    ‖∫ x in (0 : ℝ)..2 * t,
        ccmFuPolarFluxIntegrand δ t x ∂volume‖ ≤
      ∫ x : ℝ, ‖deriv ccmFuAutocorrelationProfile x‖ ∂volume := by
  have hH : 0 ≤ 2 * t := by linarith
  have hD := integrable_ccmFuTranslatedAutocorrelationDeriv
    (δ := δ) (t := t) hδ
  have hprod : IntegrableOn
      (ccmFuPolarFluxIntegrand δ t)
      (Ioc 0 (2 * t)) := by
    refine hD.norm.integrableOn.mono' ?_ ?_
    · apply AEMeasurable.aestronglyMeasurable
      exact (continuous_ccmFuPolarFluxIntegrand δ t).aemeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact norm_ccmFuPolarFluxIntegrand_le_abs_deriv hx.1.le
  rw [intervalIntegral.integral_of_le hH]
  calc
    ‖∫ x in Ioc (0 : ℝ) (2 * t),
        ccmFuPolarFluxIntegrand δ t x‖ =
        ‖∫ x in Ioc (0 : ℝ) (2 * t),
          ccmFuPolarFluxIntegrand δ t x‖ := by
      rfl
    _ ≤ ∫ x in Ioc (0 : ℝ) (2 * t),
        ‖ccmFuPolarFluxIntegrand δ t x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioc (0 : ℝ) (2 * t),
        ‖ccmFuTranslatedAutocorrelationDeriv δ t x‖ := by
      exact integral_mono_ae hprod.norm hD.norm.integrableOn (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact norm_ccmFuPolarFluxIntegrand_le_abs_deriv hx.1.le)
    _ ≤ ∫ x : ℝ, ‖ccmFuTranslatedAutocorrelationDeriv δ t x‖ :=
      setIntegral_le_integral hD.norm
        (Filter.Eventually.of_forall fun x => norm_nonneg _)
    _ = ∫ x : ℝ, ‖deriv ccmFuAutocorrelationProfile x‖ := by
      calc
        (∫ x : ℝ, ‖ccmFuTranslatedAutocorrelationDeriv δ t x‖) =
            ∫ x : ℝ, |ccmFuTranslatedAutocorrelationDeriv δ t x| :=
          integral_congr_ae (Filter.Eventually.of_forall fun x =>
            Real.norm_eq_abs _)
        _ = ∫ x : ℝ, |deriv ccmFuAutocorrelationProfile x| :=
          integral_abs_ccmFuTranslatedAutocorrelationDeriv hδ
        _ = ∫ x : ℝ, ‖deriv ccmFuAutocorrelationProfile x‖ :=
          integral_congr_ae (Filter.Eventually.of_forall fun x =>
            (Real.norm_eq_abs _).symm)

theorem exists_uniform_criticalMellinStieltjesPairing_ccmFu_re_upper_of_psi
    (hpsi : PsiRemainderSquareRootBounded) :
    ∃ M : ℝ, ∀ δ t : ℝ, 0 < δ → δ ≤ 1 →
      Real.log 3 ≤ t - δ * ccmFuAutocorrelationTest.radius →
      δ * ccmFuAutocorrelationTest.radius < t →
      (criticalMellinStieltjesPairing t
        (fun x => (ccmFuTranslatedAutocorrelation δ t x : ℂ))).re ≤ M := by
  obtain ⟨C, hC, herror⟩ :=
    criticalMellinNormalizedChebyshevErrorEventuallyBounded_of_psiRemainderSquareRootBounded
      hpsi
  let ID : ℝ := ∫ x : ℝ, |deriv ccmFuAutocorrelationProfile x|
  let IF : ℝ := ∫ x : ℝ, |ccmFuAutocorrelationProfile x|
  refine ⟨ID + C * ID + (1 / 2 : ℝ) * (C * IF), ?_⟩
  intro δ t hδ hδ1 hlate ht
  have ht0 : 0 ≤ t := by
    have hR : 0 ≤ ccmFuAutocorrelationTest.radius := by
      linarith [ccmFuAutocorrelationTest.one_lt_radius]
    nlinarith
  have hDsupport : ∀ x : ℝ, x < Real.log 3 →
      ccmFuTranslatedAutocorrelationDeriv δ t x = 0 := by
    intro x hx
    apply ccmFuTranslatedAutocorrelationDeriv_eq_zero_of_lt_lower hδ
    exact lt_of_lt_of_le hx hlate
  have hFsupport : ∀ x : ℝ, x < Real.log 3 →
      ccmFuTranslatedAutocorrelation δ t x = 0 := by
    intro x hx
    apply ccmFuTranslatedAutocorrelation_eq_zero_of_lt_lower hδ
    exact lt_of_lt_of_le hx hlate
  have hpolar := abs_integral_polarFlux_mul_ccmFuDeriv_le hδ ht0
  have hpolarAbs :
      |∫ x in (0 : ℝ)..2 * t,
          ccmFuPolarFluxIntegrand δ t x| ≤ ID := by
    calc
      |∫ x in (0 : ℝ)..2 * t,
          ccmFuPolarFluxIntegrand δ t x| =
          ‖∫ x in (0 : ℝ)..2 * t,
            ccmFuPolarFluxIntegrand δ t x‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ∫ x : ℝ, ‖deriv ccmFuAutocorrelationProfile x‖ := hpolar
      _ = ID := by
        dsimp only [ID]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
          Real.norm_eq_abs _)
  have hED := abs_integral_cutoff_mul_le_late_l1 hC herror
    (integrable_ccmFuTranslatedAutocorrelationDeriv (δ := δ) (t := t) hδ)
    hDsupport (H := 2 * t)
  rw [integral_abs_ccmFuTranslatedAutocorrelationDeriv hδ] at hED
  have hEF := abs_integral_cutoff_mul_le_late_l1 hC herror
    (integrable_ccmFuTranslatedAutocorrelation (δ := δ) (t := t) hδ)
    hFsupport (H := 2 * t)
  rw [integral_abs_ccmFuTranslatedAutocorrelation hδ] at hEF
  have hIF0 : 0 ≤ IF := by
    dsimp only [IF]
    exact integral_nonneg (fun x => abs_nonneg _)
  have hδIF : δ * IF ≤ IF := by
    nlinarith
  have hEF' :
      |∫ x in (0 : ℝ)..2 * t,
        criticalMellinNormalizedErrorCutoff (2 * t) x *
          ccmFuTranslatedAutocorrelation δ t x| ≤ C * IF := by
    exact hEF.trans (by
      dsimp only [IF] at hδIF ⊢
      exact mul_le_mul_of_nonneg_left hδIF hC)
  have hEF'' :
      |∫ x in (0 : ℝ)..2 * t,
        ccmFuTranslatedAutocorrelation δ t x *
          criticalMellinNormalizedErrorCutoff (2 * t) x| ≤ C * IF := by
    simpa only [mul_comm] using hEF'
  rw [criticalMellinStieltjesPairing_ccmFu_re_decomposition hδ ht]
  have hpolarExpandedAbs :
      |∫ x in (0 : ℝ)..2 * t,
          (1 - 2 * Real.exp (-x / 2)) *
            ccmFuTranslatedAutocorrelationDeriv δ t x| ≤ ID := by
    change |∫ x in (0 : ℝ)..2 * t,
      ccmFuPolarFluxIntegrand δ t x| ≤ ID
    exact hpolarAbs
  dsimp only [ID, IF] at hpolarExpandedAbs hED hEF' ⊢
  have hA := neg_le_abs
    (∫ x in (0 : ℝ)..2 * t,
      (1 - 2 * Real.exp (-x / 2)) *
        ccmFuTranslatedAutocorrelationDeriv δ t x)
  have hB := le_abs_self
    (∫ x in (0 : ℝ)..2 * t,
      criticalMellinNormalizedErrorCutoff (2 * t) x *
        ccmFuTranslatedAutocorrelationDeriv δ t x)
  have hFneg := neg_le_abs
    (∫ x in (0 : ℝ)..2 * t,
      ccmFuTranslatedAutocorrelation δ t x *
        criticalMellinNormalizedErrorCutoff (2 * t) x)
  nlinarith [hpolarExpandedAbs]

theorem ccmFuDeningerProfile_endpoint_sum (δ t x : ℝ) :
    ccmFuDeningerProfile δ t x +
        ccmFuDeningerProfile δ t x * Real.exp x =
      ccmFuTranslatedAutocorrelation δ t x * (2 * Real.cosh (x / 2)) := by
  rw [ccmFuDeningerProfile]
  have hexp : Real.exp (-x / 2) * Real.exp x = Real.exp (x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hneg : -(x / 2) = -x / 2 := by ring
  rw [Real.cosh_eq]
  calc
    Real.exp (-x / 2) * ccmFuTranslatedAutocorrelation δ t x +
        Real.exp (-x / 2) * ccmFuTranslatedAutocorrelation δ t x * Real.exp x =
      ccmFuTranslatedAutocorrelation δ t x *
        (Real.exp (-x / 2) + Real.exp (-x / 2) * Real.exp x) := by ring
    _ = ccmFuTranslatedAutocorrelation δ t x *
        (Real.exp (-x / 2) + Real.exp (x / 2)) := by rw [hexp]
    _ = ccmFuTranslatedAutocorrelation δ t x *
        (2 * ((Real.exp (x / 2) + Real.exp (-(x / 2))) / 2)) := by
      rw [hneg]
      ring

theorem deningerTimeTestLaplace_zero_add_one_ccmFu_eq_polarIntegral
    {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    deningerTimeTestLaplace (ccmFuDeningerTest δ t hδ ht) 0 +
        deningerTimeTestLaplace (ccmFuDeningerTest δ t hδ ht) 1 =
      ∫ x in Ioc (0 : ℝ) (2 * t),
        (ccmFuTranslatedAutocorrelation δ t x : ℂ) *
          (2 * Real.cosh (x / 2) : ℂ) := by
  let φ : ℝ → ℝ := ccmFuDeningerProfile δ t
  let G : ℝ → ℂ := fun x =>
    (ccmFuTranslatedAutocorrelation δ t x : ℂ) *
      (2 * Real.cosh (x / 2) : ℂ)
  have hφcpt : HasCompactSupport φ := by
    exact HasCompactSupport.intro (ccmFuDeningerSupport δ t).isCompact
      (ccmFuDeningerProfile_zero_on_compl hδ)
  have hφcont : Continuous φ := (contDiff_ccmFuDeningerProfile δ t).continuous
  have hφcomplex : Continuous (fun x : ℝ => (φ x : ℂ)) :=
    Complex.continuous_ofReal.comp hφcont
  have hφint : Integrable (fun x : ℝ => (φ x : ℂ)) :=
    hφcomplex.integrable_of_hasCompactSupport
      (hφcpt.comp_left (g := fun r : ℝ => (r : ℂ)) rfl)
  have hφexpint : Integrable
      (fun x : ℝ => (φ x : ℂ) * Complex.exp (x : ℂ)) := by
    have hc : Continuous (fun x : ℝ => (φ x : ℂ) * Complex.exp (x : ℂ)) := by
      exact hφcomplex.mul (Complex.continuous_exp.comp Complex.continuous_ofReal)
    have hs : HasCompactSupport
        (fun x : ℝ => (φ x : ℂ) * Complex.exp (x : ℂ)) := by
      exact (hφcpt.comp_left (g := fun r : ℝ => (r : ℂ)) rfl).mul_right
    exact hc.integrable_of_hasCompactSupport hs
  have hpoint : ∀ x : ℝ,
      (φ x : ℂ) + (φ x : ℂ) * Complex.exp (x : ℂ) = G x := by
    intro x
    dsimp only [φ, G]
    rw [← Complex.ofReal_exp]
    exact_mod_cast ccmFuDeningerProfile_endpoint_sum δ t x
  have hwhole :
      (∫ x : ℝ, (φ x : ℂ)) +
          ∫ x : ℝ, (φ x : ℂ) * Complex.exp (x : ℂ) =
        ∫ x : ℝ, G x := by
    rw [← MeasureTheory.integral_add hφint hφexpint]
    exact integral_congr_ae (ae_of_all _ hpoint)
  have hGsupp : Function.support G ⊆ Icc (0 : ℝ) (2 * t) := by
    intro x hx
    have hxS : x ∈ (ccmFuDeningerSupport δ t : Set ℝ) := by
      by_contra hnot
      exact hx (by
        dsimp only [G]
        rw [ccmFuTranslatedAutocorrelation_zero_on_compl hδ hnot, ofReal_zero,
          zero_mul])
    change x ∈ Icc (t - δ * ccmFuAutocorrelationTest.radius)
      (t + δ * ccmFuAutocorrelationTest.radius) at hxS
    constructor <;> linarith [hxS.1, hxS.2]
  have hH : 0 ≤ 2 * t := by
    have hR : 0 ≤ ccmFuAutocorrelationTest.radius := by
      linarith [ccmFuAutocorrelationTest.one_lt_radius]
    nlinarith
  have hrestrict := IntervalIntegral.integral_eq_integral_of_support_subset_Icc
    (μ := volume) hGsupp
  rw [intervalIntegral.integral_of_le hH] at hrestrict
  rw [deningerTimeTestLaplace_zero, deningerTimeTestLaplace_one]
  change (∫ x : ℝ, (φ x : ℂ)) +
      (∫ x : ℝ, (φ x : ℂ) * Complex.exp (x : ℂ)) = _
  rw [hwhole]
  exact hrestrict.symm

theorem deningerPrimeSum_ccmFu_eq_criticalMellinPrimeSum
    {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    (∑' n : DeningerPrimePowerIndex,
      (deningerPrimePowerWeight n : ℂ) *
        (ccmFuDeningerTest δ t hδ ht (deningerPrimePowerTime n) : ℂ)) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * t)⌋₊,
        (criticalMellinAtomWeight n : ℂ) *
          (ccmFuTranslatedAutocorrelation δ t (Real.log n) : ℂ) := by
  rw [← tsum_vonMangoldt_timeTest_eq_deningerPrimePower]
  rw [tsum_eq_sum (s := Finset.Icc 2 ⌊Real.exp (2 * t)⌋₊)]
  · apply Finset.sum_congr rfl
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnposR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn2)
    have hrpow : ((n : ℝ) ^ (-1 / 2 : ℝ)) = Real.exp (-Real.log n / 2) := by
      rw [Real.rpow_def_of_pos hnposR]
      congr 1
      ring
    rw [ccmFuDeningerTest_apply, ccmFuDeningerProfile,
      criticalMellinAtomWeight, hrpow]
    push_cast
    ring
  · intro n hn
    by_cases hn2 : 2 ≤ n
    · have hupper : ⌊Real.exp (2 * t)⌋₊ < n := by
        by_contra hnot
        exact hn (Finset.mem_Icc.mpr ⟨hn2, le_of_not_gt hnot⟩)
      have hnposR : (0 : ℝ) < n := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn2)
      have hexp : Real.exp (2 * t) < (n : ℝ) := Nat.lt_of_floor_lt hupper
      have hlog : 2 * t < Real.log n :=
        (Real.lt_log_iff_exp_lt hnposR).mpr hexp
      have hz := ccmFuTranslatedAutocorrelation_eq_zero_of_upper_lt
        (δ := δ) (t := t) (x := Real.log n) hδ (by linarith)
      rw [ccmFuDeningerTest_apply, ccmFuDeningerProfile, hz, mul_zero,
        ofReal_zero, mul_zero]
    · have hnle : n ≤ 1 := by omega
      interval_cases n <;> simp

theorem deningerSpectralSum_ccmFu_eq_criticalMellinPairing_sub_arch
    {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    (∑' q : XiZeroCopy,
      deningerTimeTestLaplace (ccmFuDeningerTest δ t hδ ht)
        (deningerRawThetaEigen q)) =
      criticalMellinStieltjesPairing t
        (fun x => (ccmFuTranslatedAutocorrelation δ t x : ℂ)) -
      ∫ x : ℝ, (ccmFuDeningerTest δ t hδ ht x : ℂ) *
        deningerArchimedeanLefschetzDensity x := by
  let φ := ccmFuDeningerTest δ t hδ ht
  have hexplicit := deningerArithmeticScalarExplicitFormula_proved φ
  have hpair :
      deningerTimeTestLaplace φ 0 + deningerTimeTestLaplace φ 1 -
          (∑' n : DeningerPrimePowerIndex,
            (deningerPrimePowerWeight n : ℂ) *
              (φ (deningerPrimePowerTime n) : ℂ)) =
        criticalMellinStieltjesPairing t
          (fun x => (ccmFuTranslatedAutocorrelation δ t x : ℂ)) := by
    rw [criticalMellinStieltjesPairing,
      deningerTimeTestLaplace_zero_add_one_ccmFu_eq_polarIntegral hδ ht,
      deningerPrimeSum_ccmFu_eq_criticalMellinPrimeSum hδ ht]
  dsimp only [φ] at hexplicit hpair ⊢
  linear_combination hpair - hexplicit

theorem ccmFuAutocorrelationProfile_nonneg (x : ℝ) :
    0 ≤ ccmFuAutocorrelationProfile x := by
  rw [ccmFuAutocorrelationProfile, ccmFuAutocorrelationTest,
    suzukiRestrictedWeilCoreAutocorrelationTest_apply_eq_ofReal]
  simp only [Complex.ofReal_re]
  unfold suzukiCoreAutocorrelation screwCrossCorr
  apply integral_nonneg
  intro y
  exact mul_nonneg (suzukiMollifier_nonneg (by norm_num) y)
    (suzukiMollifier_nonneg (by norm_num) (x + y))

theorem ccmFuDeningerTest_nonneg
    {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) (x : ℝ) :
    0 ≤ ccmFuDeningerTest δ t hδ ht x := by
  rw [ccmFuDeningerTest_apply, ccmFuDeningerProfile]
  exact mul_nonneg (Real.exp_pos _).le
    (ccmFuAutocorrelationProfile_nonneg _)

theorem deningerArchimedeanIntegral_ccmFu_re_nonneg
    {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t)
    (hlate : Real.log 3 ≤ t - δ * ccmFuAutocorrelationTest.radius) :
    0 ≤ (∫ x : ℝ, (ccmFuDeningerTest δ t hδ ht x : ℂ) *
      deningerArchimedeanLefschetzDensity x).re := by
  let φ := ccmFuDeningerTest δ t hδ ht
  let A : ℝ := (1 - Real.exp (-2 * Real.log 3))⁻¹
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hd0 : 0 < 1 - Real.exp (-2 * Real.log 3) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hA0 : 0 ≤ A := (inv_pos.mpr hd0).le
  have hdensity : ∀ x : ℝ, Real.log 3 ≤ x →
      ‖deningerArchimedeanLefschetzDensity x‖ ≤ A := by
    intro x hx
    have hexp : Real.exp (-2 * x) ≤ Real.exp (-2 * Real.log 3) :=
      Real.exp_le_exp.mpr (by linarith)
    have hden : 1 - Real.exp (-2 * Real.log 3) ≤
        1 - Real.exp (-2 * x) := by linarith
    have hdenx : 0 < 1 - Real.exp (-2 * x) := hd0.trans_le hden
    rw [deningerArchimedeanLefschetzDensity, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdenx)]
    dsimp only [A]
    exact inv_anti₀ hd0 hden
  have hφcpt : HasCompactSupport (fun x : ℝ => (φ x : ℂ)) := by
    have hreal : HasCompactSupport (fun x : ℝ => φ x) := φ.hasCompactSupport
    exact hreal.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  have hφcont : Continuous (fun x : ℝ => (φ x : ℂ)) := by
    exact Complex.continuous_ofReal.comp φ.contDiff.continuous
  have hφint : Integrable (fun x : ℝ => (φ x : ℂ)) :=
    hφcont.integrable_of_hasCompactSupport hφcpt
  have hmajor : Integrable (fun x : ℝ => A * ‖(φ x : ℂ)‖) :=
    hφint.norm.const_mul A
  have hpoint : ∀ x : ℝ,
      ‖(φ x : ℂ) * deningerArchimedeanLefschetzDensity x‖ ≤
        A * ‖(φ x : ℂ)‖ := by
    intro x
    by_cases hφx : φ x = 0
    · simp [hφx]
    · have hxS : x ∈ (ccmFuDeningerSupport δ t : Set ℝ) := by
        by_contra hnot
        exact hφx (by
          change ccmFuDeningerProfile δ t x = 0
          exact ccmFuDeningerProfile_zero_on_compl hδ hnot)
      change x ∈ Icc (t - δ * ccmFuAutocorrelationTest.radius)
        (t + δ * ccmFuAutocorrelationTest.radius) at hxS
      rw [norm_mul]
      calc
        ‖(φ x : ℂ)‖ * ‖deningerArchimedeanLefschetzDensity x‖ ≤
            ‖(φ x : ℂ)‖ * A :=
          mul_le_mul_of_nonneg_left (hdensity x (hlate.trans hxS.1))
            (norm_nonneg _)
        _ = A * ‖(φ x : ℂ)‖ := by ring
  have hprodMeas : AEStronglyMeasurable
      (fun x : ℝ => (φ x : ℂ) * deningerArchimedeanLefschetzDensity x) := by
    have hdensityMeas : Measurable deningerArchimedeanLefschetzDensity := by
      unfold deningerArchimedeanLefschetzDensity
      exact Complex.measurable_ofReal.comp
        ((measurable_const.sub
          (Real.measurable_exp.comp
            (measurable_const.mul measurable_id))).inv)
    apply AEMeasurable.aestronglyMeasurable
    exact (hφcont.measurable.mul hdensityMeas).aemeasurable
  have hprod : Integrable
      (fun x : ℝ => (φ x : ℂ) * deningerArchimedeanLefschetzDensity x) := by
    refine hmajor.mono' hprodMeas ?_
    exact ae_of_all _ hpoint
  have hre := (Complex.reCLM.integral_comp_comm hprod).symm
  change 0 ≤ (∫ x : ℝ, (φ x : ℂ) *
    deningerArchimedeanLefschetzDensity x).re
  rw [← Complex.reCLM_apply, hre]
  apply integral_nonneg
  intro x
  by_cases hφx : φ x = 0
  · simp [hφx]
  · have hxS : x ∈ (ccmFuDeningerSupport δ t : Set ℝ) := by
      by_contra hnot
      exact hφx (by
        change ccmFuDeningerProfile δ t x = 0
        exact ccmFuDeningerProfile_zero_on_compl hδ hnot)
    change x ∈ Icc (t - δ * ccmFuAutocorrelationTest.radius)
      (t + δ * ccmFuAutocorrelationTest.radius) at hxS
    have hx0 : 0 < x := hlog3.trans_le (hlate.trans hxS.1)
    have hdenx : 0 ≤ 1 - Real.exp (-2 * x) := by
      rw [sub_nonneg]
      exact Real.exp_le_one_iff.mpr (by linarith)
    have hprofile : 0 ≤ ccmFuDeningerProfile δ t x := by
      rw [ccmFuDeningerProfile]
      exact mul_nonneg (Real.exp_pos _).le
        (ccmFuAutocorrelationProfile_nonneg _)
    have hmul : 0 ≤ ccmFuDeningerProfile δ t x *
        (1 - Real.exp (-2 * x))⁻¹ :=
      mul_nonneg hprofile (inv_nonneg.mpr hdenx)
    simpa only [Pi.zero_apply, Complex.reCLM_apply, φ,
      ccmFuDeningerTest_apply,
      deningerArchimedeanLefschetzDensity, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using hmul

theorem exists_uniform_deningerSpectralSum_ccmFu_re_upper_of_psi
    (hpsi : PsiRemainderSquareRootBounded) :
    ∃ M : ℝ, ∀ δ t : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 →
      Real.log 3 ≤ t - δ * ccmFuAutocorrelationTest.radius →
      ∀ ht : δ * ccmFuAutocorrelationTest.radius < t,
      (∑' q : XiZeroCopy,
        deningerTimeTestLaplace (ccmFuDeningerTest δ t hδ ht)
          (deningerRawThetaEigen q)).re ≤ M := by
  obtain ⟨M, hM⟩ :=
    exists_uniform_criticalMellinStieltjesPairing_ccmFu_re_upper_of_psi hpsi
  refine ⟨M, ?_⟩
  intro δ t hδ hδ1 hlate ht
  have hpair := hM δ t hδ hδ1 hlate ht
  have harch := deningerArchimedeanIntegral_ccmFu_re_nonneg hδ ht hlate
  rw [deningerSpectralSum_ccmFu_eq_criticalMellinPairing_sub_arch hδ ht,
    Complex.sub_re]
  linarith

theorem deningerSpectralSum_ccmFu_cofinally_unbounded_smallScale
    (hRH : RiemannHypothesis) :
    ∀ C L : ℝ, ∃ δ t : ℝ,
      ∃ hδ : 0 < δ,
      ∃ ht : δ * ccmFuAutocorrelationTest.radius < t,
      δ ≤ 1 ∧ L ≤ t ∧ C <
        (∑' q : XiZeroCopy,
          deningerTimeTestLaplace (ccmFuDeningerTest δ t hδ ht)
            (deningerRawThetaEigen q)).re := by
  obtain ⟨η, hη, hmassEventually⟩ :=
    exists_eventually_ccmFuDeningerMass_log_lower hRH
  intro C L
  have hlog : ∀ᶠ T : ℝ in atTop,
      64 * |C| / η + 1 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually_ge_atTop (64 * |C| / η + 1)
  have hlarge : ∀ᶠ T : ℝ in atTop,
      0 < T ∧
      0 < ccmFuDeningerMass (ccmFuDeningerDyadicScale η T) ∧
      2 * C < ccmFuDeningerMass (ccmFuDeningerDyadicScale η T) ∧
      Real.pi * η / 2 ≤ T := by
    filter_upwards [hmassEventually, hlog, eventually_ge_atTop (4 : ℝ),
      eventually_ge_atTop (Real.pi * η / 2)] with T hmass hlogT hT4 hTscale
    have hT : 0 < T := by linarith
    have hlog0 : 0 < Real.log T := Real.log_pos (by linarith)
    have hscale0 : 0 < (η / 32) * Real.log T := by positivity
    have hmass0 :
        0 < ccmFuDeningerMass (ccmFuDeningerDyadicScale η T) :=
      hscale0.trans_le hmass
    have hcoef : 0 < η / 32 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hlogT hcoef.le
    have heq :
        (η / 32) * (64 * |C| / η + 1) =
          2 * |C| + η / 32 := by
      field_simp [hη.ne']
      ring
    rw [heq] at hscaled
    have hClower : 2 * C < (η / 32) * Real.log T := by
      have habsC : C ≤ |C| := le_abs_self C
      nlinarith
    exact ⟨hT, hmass0, hClower.trans_le hmass, hTscale⟩
  obtain ⟨T, hT, hmass0, hmassC, hTscale⟩ := hlarge.exists
  have hδ : 0 < ccmFuDeningerDyadicScale η T := by
    unfold ccmFuDeningerDyadicScale
    positivity
  have hδ1 : ccmFuDeningerDyadicScale η T ≤ 1 := by
    unfold ccmFuDeningerDyadicScale
    apply (div_le_one (by positivity : 0 < 2 * T)).mpr
    nlinarith
  obtain ⟨t, htLate, htPhase⟩ :=
    exists_ccmFuDeningerRealPhase_gt_half_mass hRH hδ hmass0
      (max L (ccmFuDeningerDyadicScale η T *
        ccmFuAutocorrelationTest.radius + 1))
  have htSupport : ccmFuDeningerDyadicScale η T *
      ccmFuAutocorrelationTest.radius < t := by
    have h := (le_max_right L (ccmFuDeningerDyadicScale η T *
      ccmFuAutocorrelationTest.radius + 1)).trans htLate
    linarith
  have htL : L ≤ t :=
    (le_max_left L (ccmFuDeningerDyadicScale η T *
      ccmFuAutocorrelationTest.radius + 1)).trans htLate
  refine ⟨ccmFuDeningerDyadicScale η T, t, hδ, htSupport,
    hδ1, htL, ?_⟩
  rw [deningerSpectralSum_ccmFuDeningerTest_re_eq_realPhase
    hRH hδ htSupport]
  linarith

theorem not_psiRemainderSquareRootBounded_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ¬ PsiRemainderSquareRootBounded := by
  intro hpsi
  obtain ⟨M, hupper⟩ :=
    exists_uniform_deningerSpectralSum_ccmFu_re_upper_of_psi hpsi
  obtain ⟨δ, t, hδ, ht, hδ1, htLate, hescape⟩ :=
    deningerSpectralSum_ccmFu_cofinally_unbounded_smallScale hRH M
      (Real.log 3 + ccmFuAutocorrelationTest.radius)
  have hR0 : 0 ≤ ccmFuAutocorrelationTest.radius :=
    (le_of_lt ccmFuAutocorrelationTest.one_lt_radius).trans' zero_le_one
  have hδR : δ * ccmFuAutocorrelationTest.radius ≤
      ccmFuAutocorrelationTest.radius := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hδ1 hR0
  have hlate : Real.log 3 ≤
      t - δ * ccmFuAutocorrelationTest.radius := by
    linarith
  have hbounded := hupper δ t hδ hδ1 hlate ht
  linarith

theorem not_ccmFUSuzukiWeightedCurvatureFirstMomentLinearBound :
    ¬ CCMFUSuzukiWeightedCurvatureFirstMomentLinearBound := by
  intro hfirst
  obtain ⟨hRH, hpsi⟩ :=
    weightedFirstMomentLinearBound_iff_rh_and_psiRemainderSquareRootBounded.mp
      hfirst
  exact not_psiRemainderSquareRootBounded_of_riemannHypothesis hRH hpsi

theorem not_ccmUnitRieszCentralBarycenterNaturalBound :
    ¬ CCMUnitRieszCentralBarycenterNaturalBound := by
  intro hcentral
  exact not_ccmFUSuzukiWeightedCurvatureFirstMomentLinearBound
    (weightedFirstMomentLinearBound_iff_unitRieszCentralBarycenterNaturalBound.mpr
      hcentral)

end

end RHTower
