import GaloisForLFunctions.RHTower.Suzuki.SuzukiCCMSourceFormBridge
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaMollifiedEquation
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticLefschetz
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
import GaloisForLFunctions.RHTower.ConstrainedProlateEvaluationIdentity
import GaloisForLFunctions.RHTower.XiDyadicBandReciprocalPhaseAmplification
import GaloisForLFunctions.HTGeometry.FourierIntegralDilation
import GaloisForLFunctions.HTGeometry.FourierFirstOrderWeight
import GaloisForLFunctions.HTGeometry.ScheffeCounting

/-!
# CCM-FU compact-autocorrelation Deninger amplification

A fixed normalized Suzuki bump produces translated, dilated positive-time Deninger tests whose
critical-line transforms are nonnegative Fourier-square weights.  Under RH these weights are the
complete multiplicity-exact Xi spectral coefficients.  Riemann--von Mangoldt gives logarithmic
coherent mass at the reciprocal dyadic scale; absolute convergence and simultaneous recurrence
then force arbitrarily large spectral responses at arbitrarily late translations.

This discharges the spectral-growth half of the CCM-FU Littlewood no-go.  The remaining weld is
purely arithmetic: bound the same Deninger explicit-formula response from
`PsiRemainderSquareRootBounded`.
-/

open Complex Filter MeasureTheory Set TopologicalSpace
open scoped FourierTransform

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

noncomputable section

def ccmFuBumpCore : SuzukiRestrictedWeilCore 1 where
  toFun := suzukiMollifier (1 / 8)
  smooth := contDiff_suzukiMollifier (1 / 8)
  supportRadius := 1 / 8
  supportRadius_nonneg := by norm_num
  supportRadius_lt_aperture := by norm_num
  support_subset := by
    intro x hx
    have habs : |x| ≤ (1 / 8 : ℝ) := by
      by_contra h
      exact hx (suzukiMollifier_eq_zero (by norm_num) (lt_of_not_ge h))
    exact (abs_le.mp habs)

def ccmFuAutocorrelationTest : CCMCompactSchwartzLogTest :=
  suzukiRestrictedWeilCoreAutocorrelationTest ccmFuBumpCore

def ccmFuAutocorrelationProfile (x : ℝ) : ℝ :=
  (ccmFuAutocorrelationTest x).re

theorem ccmFuAutocorrelationProfile_ofReal (x : ℝ) :
    (ccmFuAutocorrelationProfile x : ℂ) = ccmFuAutocorrelationTest x := by
  apply Complex.ext
  · rfl
  · simp [ccmFuAutocorrelationProfile, ccmFuAutocorrelationTest]

theorem contDiff_ccmFuAutocorrelationProfile :
    ContDiff ℝ (⊤ : ℕ∞) ccmFuAutocorrelationProfile := by
  exact Complex.reCLM.contDiff.comp
    (ccmFuAutocorrelationTest.toSchwartzMap.smooth (⊤ : ℕ∞))

theorem ccmFuAutocorrelationProfile_eq_zero_of_radius_le_abs {x : ℝ}
    (hx : ccmFuAutocorrelationTest.radius ≤ |x|) :
    ccmFuAutocorrelationProfile x = 0 := by
  rw [ccmFuAutocorrelationProfile,
    ccmFuAutocorrelationTest.eq_zero_of_radius_le_abs x hx]
  rfl

def ccmFuTranslatedAutocorrelation (δ t x : ℝ) : ℝ :=
  ccmFuAutocorrelationProfile ((x - t) / δ)

def ccmFuDeningerProfile (δ t x : ℝ) : ℝ :=
  Real.exp (-x / 2) * ccmFuTranslatedAutocorrelation δ t x

def ccmFuDeningerSupport (δ t : ℝ) : Compacts ℝ :=
  ⟨Icc (t - δ * ccmFuAutocorrelationTest.radius)
      (t + δ * ccmFuAutocorrelationTest.radius), isCompact_Icc⟩

theorem contDiff_ccmFuDeningerProfile (δ t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (ccmFuDeningerProfile δ t) := by
  unfold ccmFuDeningerProfile ccmFuTranslatedAutocorrelation
  have harg : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (x - t) / δ) := by fun_prop
  exact (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => Real.exp (-x / 2))).mul
    (contDiff_ccmFuAutocorrelationProfile.comp harg)

theorem ccmFuDeningerProfile_zero_on_compl {δ t : ℝ} (hδ : 0 < δ) :
    Set.EqOn (ccmFuDeningerProfile δ t) (fun _ : ℝ => 0)
      (ccmFuDeningerSupport δ t : Set ℝ)ᶜ := by
  intro x hx
  have hout : x < t - δ * ccmFuAutocorrelationTest.radius ∨
      t + δ * ccmFuAutocorrelationTest.radius < x := by
    change x ∉ Icc (t - δ * ccmFuAutocorrelationTest.radius)
      (t + δ * ccmFuAutocorrelationTest.radius) at hx
    by_cases hleft : t - δ * ccmFuAutocorrelationTest.radius ≤ x
    · right
      exact lt_of_not_ge (fun hright => hx ⟨hleft, hright⟩)
    · exact Or.inl (lt_of_not_ge hleft)
  have hradius : ccmFuAutocorrelationTest.radius ≤ |(x - t) / δ| := by
    rcases hout with hleft | hright
    · have hq : (x - t) / δ < -ccmFuAutocorrelationTest.radius := by
        rw [div_lt_iff₀ hδ]
        nlinarith
      have hR : ccmFuAutocorrelationTest.radius ≤ -((x - t) / δ) := by
        linarith
      exact hR.trans (neg_le_abs ((x - t) / δ))
    · have hq : ccmFuAutocorrelationTest.radius < (x - t) / δ := by
        rw [lt_div_iff₀ hδ]
        nlinarith
      exact (le_of_lt hq).trans (le_abs_self ((x - t) / δ))
  rw [ccmFuDeningerProfile, ccmFuTranslatedAutocorrelation,
    ccmFuAutocorrelationProfile_eq_zero_of_radius_le_abs hradius, mul_zero]

theorem ccmFuDeningerSupport_subset_timeDomain {δ t : ℝ}
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    (ccmFuDeningerSupport δ t : Set ℝ) ⊆ (deningerTimeDomain : Set ℝ) := by
  intro x hx
  change 0 < x
  change x ∈ Icc (t - δ * ccmFuAutocorrelationTest.radius)
    (t + δ * ccmFuAutocorrelationTest.radius) at hx
  linarith [hx.1]

def ccmFuDeningerTest (δ t : ℝ) (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) : DeningerTimeTestFunction :=
  TestFunction.ofSupportedIn (ccmFuDeningerSupport_subset_timeDomain ht)
    { toFun := ccmFuDeningerProfile δ t
      contDiff' := contDiff_ccmFuDeningerProfile δ t
      zero_on_compl' := ccmFuDeningerProfile_zero_on_compl hδ }

@[simp] theorem ccmFuDeningerTest_apply (δ t : ℝ) (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) (x : ℝ) :
    ccmFuDeningerTest δ t hδ ht x = ccmFuDeningerProfile δ t x := rfl

theorem deningerTimeTestLaplace_criticalLine_eq_fourier
    (φ : DeningerTimeTestFunction) (y : ℝ) :
    deningerTimeTestLaplace φ ((1 / 2 : ℂ) + (y : ℂ) * I) =
      𝓕 (fun x : ℝ => ((Real.exp (x / 2) * φ x : ℝ) : ℂ))
        (-y / (2 * Real.pi)) := by
  rw [deningerTimeTestLaplace, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  rw [smul_eq_mul]
  have hphase :
      Complex.exp
          ((↑(-2 * Real.pi * x * (-y / (2 * Real.pi))) : ℂ) * I) =
        Complex.exp (((x * y : ℝ) : ℂ) * I) := by
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hphase]
  have hexp :
      Complex.exp ((x : ℂ) * ((1 / 2 : ℂ) + (y : ℂ) * I)) =
        (Real.exp (x / 2) : ℂ) * Complex.exp (((x * y : ℝ) : ℂ) * I) := by
    calc
      Complex.exp ((x : ℂ) * ((1 / 2 : ℂ) + (y : ℂ) * I)) =
          Complex.exp (((x / 2 : ℝ) : ℂ) + ((x * y : ℝ) : ℂ) * I) := by
        congr 1
        push_cast
        ring
      _ = Complex.exp ((x / 2 : ℝ) : ℂ) *
          Complex.exp (((x * y : ℝ) : ℂ) * I) := Complex.exp_add _ _
      _ = _ := by rw [ofReal_exp]
  rw [hexp]
  push_cast
  ring

theorem fourier_ccmFuAutocorrelationProfile (ξ : ℝ) :
    𝓕 (fun x : ℝ => (ccmFuAutocorrelationProfile x : ℂ)) ξ =
      ((‖𝓕 (suzukiRestrictedWeilCoreSchwartz ccmFuBumpCore : ℝ → ℂ) ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [show (fun x : ℝ => (ccmFuAutocorrelationProfile x : ℂ)) =
      (ccmFuAutocorrelationTest : ℝ → ℂ) by
    funext x
    exact ccmFuAutocorrelationProfile_ofReal x]
  exact fourier_suzukiRestrictedWeilCoreAutocorrelationTest ccmFuBumpCore ξ

theorem deningerTimeTestLaplace_ccmFuDeningerTest_criticalLine
    {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) (y : ℝ) :
    deningerTimeTestLaplace (ccmFuDeningerTest δ t hδ ht)
        ((1 / 2 : ℂ) + (y : ℂ) * I) =
      Complex.exp (((t * y : ℝ) : ℂ) * I) *
        (δ : ℂ) *
          ((‖𝓕 (suzukiRestrictedWeilCoreSchwartz ccmFuBumpCore : ℝ → ℂ)
              (-δ * y / (2 * Real.pi))‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [deningerTimeTestLaplace_criticalLine_eq_fourier]
  have htilt : (fun x : ℝ =>
      ((Real.exp (x / 2) * ccmFuDeningerTest δ t hδ ht x : ℝ) : ℂ)) =
      fun x : ℝ => (ccmFuAutocorrelationProfile ((x - t) / δ) : ℂ) := by
    funext x
    rw [ccmFuDeningerTest_apply, ccmFuDeningerProfile,
      ccmFuTranslatedAutocorrelation]
    have hcancel : Real.exp (x / 2) * Real.exp (-x / 2) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp
    exact_mod_cast (show Real.exp (x / 2) *
        (Real.exp (-x / 2) * ccmFuAutocorrelationProfile ((x - t) / δ)) =
          ccmFuAutocorrelationProfile ((x - t) / δ) by
      rw [← mul_assoc, hcancel, one_mul])
  rw [htilt, fourierIntegral_comp_div_sub
    (fun x : ℝ => (ccmFuAutocorrelationProfile x : ℂ)) t δ hδ
      (-y / (2 * Real.pi)), fourier_ccmFuAutocorrelationProfile]
  simp only [smul_eq_mul, Complex.real_smul]
  have hphase :
      2 * Real.pi * -t * (-y / (2 * Real.pi)) = t * y := by
    field_simp [Real.pi_ne_zero]
  have hfreq : δ * (-y / (2 * Real.pi)) = -δ * y / (2 * Real.pi) := by ring
  rw [hphase, hfreq]
  push_cast
  ring

theorem deningerTimeTestLaplace_ccmFuDeningerTest_rawTheta
    (hRH : RiemannHypothesis) {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) (q : XiZeroCopy) :
    deningerTimeTestLaplace (ccmFuDeningerTest δ t hδ ht)
        (deningerRawThetaEigen q) =
      Complex.exp (((t * (q.1 : ℂ).im : ℝ) : ℂ) * I) *
        (δ : ℂ) *
          ((‖𝓕 (suzukiRestrictedWeilCoreSchwartz ccmFuBumpCore : ℝ → ℂ)
              (-δ * (q.1 : ℂ).im / (2 * Real.pi))‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  have hre : (q.1 : ℂ).re = 1 / 2 :=
    (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH) (q.1 : ℂ)
      (xi_eq_zero_of_mem_divisor_support q.1)
  have heigen : deningerRawThetaEigen q =
      (1 / 2 : ℂ) + (((q.1 : ℂ).im : ℂ) * I) := by
    apply Complex.ext
    · simpa [deningerRawThetaEigen] using hre
    · simp [deningerRawThetaEigen]
  rw [heigen]
  exact deningerTimeTestLaplace_ccmFuDeningerTest_criticalLine hδ ht _

def ccmFuDeningerWeight (δ : ℝ) (q : XiZeroCopy) : ℝ :=
  δ * ‖𝓕 (suzukiRestrictedWeilCoreSchwartz ccmFuBumpCore : ℝ → ℂ)
    (-δ * (q.1 : ℂ).im / (2 * Real.pi))‖ ^ (2 : ℕ)

def ccmFuBaseFourier (ξ : ℝ) : ℂ :=
  𝓕 (suzukiRestrictedWeilCoreSchwartz ccmFuBumpCore : ℝ → ℂ) ξ

theorem ccmFuBaseFourier_zero : ccmFuBaseFourier 0 = 1 := by
  rw [ccmFuBaseFourier, fourier_zero_eq_integral]
  change (∫ x : ℝ, (suzukiMollifier (1 / 8) x : ℂ)) = 1
  rw [integral_complex_ofReal, integral_suzukiMollifier (by norm_num)]
  rfl

theorem continuous_ccmFuBaseFourier : Continuous ccmFuBaseFourier := by
  exact GaloisForLFunctions.HTGeometry.continuous_fourier
    (suzukiRestrictedWeilCoreSchwartz ccmFuBumpCore).integrable

theorem exists_ccmFuBaseFourier_norm_sq_lower_near_zero :
    ∃ η : ℝ, 0 < η ∧ ∀ ξ : ℝ, |ξ| < η →
      (1 / 4 : ℝ) < ‖ccmFuBaseFourier ξ‖ ^ (2 : ℕ) := by
  have hcont : ContinuousAt ccmFuBaseFourier 0 :=
    continuous_ccmFuBaseFourier.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨η, hη, hclose⟩ := hcont (1 / 2 : ℝ) (by norm_num)
  refine ⟨η, hη, fun ξ hξ => ?_⟩
  have hdist : dist ξ 0 < η := by
    simpa [Real.dist_eq] using hξ
  have hF := hclose hdist
  rw [ccmFuBaseFourier_zero, dist_eq_norm] at hF
  have hreverse := norm_sub_norm_le (1 : ℂ) (ccmFuBaseFourier ξ)
  have hsmall : ‖(1 : ℂ) - ccmFuBaseFourier ξ‖ < 1 / 2 := by
    rw [norm_sub_rev]
    exact hF
  have hnorm : (1 / 2 : ℝ) < ‖ccmFuBaseFourier ξ‖ := by
    norm_num at hreverse
    linarith
  nlinarith [sq_nonneg (‖ccmFuBaseFourier ξ‖ - 1 / 2)]

def ccmFuDeningerDyadicScale (η T : ℝ) : ℝ :=
  Real.pi * η / (2 * T)

def ccmFuDeningerDyadicMass (η T : ℝ) : ℝ :=
  ∑ q ∈ xiCopiesBand T (2 * T),
    ccmFuDeningerWeight (ccmFuDeningerDyadicScale η T) q

theorem exists_eventually_ccmFuDeningerDyadicMass_log_lower :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ T : ℝ in atTop,
      (η / 32) * Real.log T ≤ ccmFuDeningerDyadicMass η T := by
  obtain ⟨η, hη, hFourier⟩ := exists_ccmFuBaseFourier_norm_sq_lower_near_zero
  refine ⟨η, hη, ?_⟩
  filter_upwards [eventually_card_xiCopiesBand_mul_two_lower,
    eventually_ge_atTop (4 : ℝ)] with T hcard hT4
  have hT0 : 0 < T := by linarith
  have hδ : 0 < ccmFuDeningerDyadicScale η T := by
    unfold ccmFuDeningerDyadicScale
    positivity
  have hterm : ∀ q ∈ xiCopiesBand T (2 * T),
      ccmFuDeningerDyadicScale η T / 4 ≤
        ccmFuDeningerWeight (ccmFuDeningerDyadicScale η T) q := by
    intro q hq
    have him := (mem_xiCopiesBand.mp hq).2
    have hfreq :
        |-ccmFuDeningerDyadicScale η T * (q.1 : ℂ).im /
            (2 * Real.pi)| < η := by
      have hpi : 0 < Real.pi := Real.pi_pos
      rw [abs_div, abs_mul, abs_neg, abs_of_pos (show 0 < 2 * Real.pi by positivity),
        abs_of_pos hδ]
      have hhalf :
          ccmFuDeningerDyadicScale η T * |(q.1 : ℂ).im| /
              (2 * Real.pi) ≤ η / 2 := by
        rw [ccmFuDeningerDyadicScale]
        apply (div_le_iff₀ (show 0 < 2 * Real.pi by positivity)).2
        field_simp [hT0.ne', Real.pi_ne_zero]
        nlinarith
      linarith
    have hnorm := le_of_lt (hFourier _ hfreq)
    rw [ccmFuDeningerWeight]
    change ccmFuDeningerDyadicScale η T / 4 ≤
      ccmFuDeningerDyadicScale η T *
        ‖ccmFuBaseFourier
          (-ccmFuDeningerDyadicScale η T * (q.1 : ℂ).im /
            (2 * Real.pi))‖ ^ (2 : ℕ)
    calc
      ccmFuDeningerDyadicScale η T / 4 =
          ccmFuDeningerDyadicScale η T * (1 / 4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hnorm hδ.le
  have hsum :
      ((xiCopiesBand T (2 * T)).card : ℝ) *
          (ccmFuDeningerDyadicScale η T / 4) ≤
        ccmFuDeningerDyadicMass η T := by
    rw [ccmFuDeningerDyadicMass]
    calc
      ((xiCopiesBand T (2 * T)).card : ℝ) *
          (ccmFuDeningerDyadicScale η T / 4) =
          ∑ q ∈ xiCopiesBand T (2 * T),
            ccmFuDeningerDyadicScale η T / 4 := by simp
      _ ≤ _ := Finset.sum_le_sum hterm
  calc
    (η / 32) * Real.log T =
        ((1 / (4 * Real.pi)) * (T * Real.log T)) *
          (ccmFuDeningerDyadicScale η T / 4) := by
      rw [ccmFuDeningerDyadicScale]
      field_simp [hT0.ne', Real.pi_ne_zero]
      ring
    _ ≤ ((xiCopiesBand T (2 * T)).card : ℝ) *
          (ccmFuDeningerDyadicScale η T / 4) := by
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ ccmFuDeningerDyadicMass η T := hsum

theorem ccmFuDeningerWeight_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (q : XiZeroCopy) :
    0 ≤ ccmFuDeningerWeight δ q := by
  exact mul_nonneg hδ (sq_nonneg _)

theorem deningerTimeTestLaplace_ccmFuDeningerTest_rawTheta_eq_phase_mul_weight
    (hRH : RiemannHypothesis) {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) (q : XiZeroCopy) :
    deningerTimeTestLaplace (ccmFuDeningerTest δ t hδ ht)
        (deningerRawThetaEigen q) =
      Complex.exp (((t * (q.1 : ℂ).im : ℝ) : ℂ) * I) *
        (ccmFuDeningerWeight δ q : ℂ) := by
  rw [deningerTimeTestLaplace_ccmFuDeningerTest_rawTheta hRH hδ ht]
  simp only [ccmFuDeningerWeight]
  push_cast
  ring

theorem summable_ccmFuDeningerWeight (hRH : RiemannHypothesis)
    {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    Summable (ccmFuDeningerWeight δ) := by
  have hs :=
    (deningerTimeTestLaplace_rawThetaEigen_summable
      (ccmFuDeningerTest δ t hδ ht)).norm
  refine hs.congr (fun q => ?_)
  rw [deningerTimeTestLaplace_ccmFuDeningerTest_rawTheta_eq_phase_mul_weight
    hRH hδ ht, norm_mul]
  have hphase :
      ‖Complex.exp (((t * (q.1 : ℂ).im : ℝ) : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hphase, one_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg
    (ccmFuDeningerWeight_nonneg hδ.le q)]

theorem summable_ccmFuDeningerWeight_of_pos (hRH : RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) : Summable (ccmFuDeningerWeight δ) := by
  let t : ℝ := δ * ccmFuAutocorrelationTest.radius + 1
  have ht : δ * ccmFuAutocorrelationTest.radius < t := by
    dsimp only [t]
    linarith
  exact summable_ccmFuDeningerWeight hRH hδ ht

def ccmFuDeningerMass (δ : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, ccmFuDeningerWeight δ q

def ccmFuDeningerRealPhase (δ t : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, ccmFuDeningerWeight δ q *
    (GaloisForLFunctions.bohrChar (-(q.1 : ℂ).im) t).re

theorem summable_ccmFuDeningerRealPhase_term (hRH : RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    Summable (fun q : XiZeroCopy => ccmFuDeningerWeight δ q *
      (GaloisForLFunctions.bohrChar (-(q.1 : ℂ).im) t).re) := by
  apply (summable_ccmFuDeningerWeight_of_pos hRH hδ).of_norm_bounded
  intro q
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (ccmFuDeningerWeight_nonneg hδ.le q)]
  calc
    ccmFuDeningerWeight δ q *
        |(GaloisForLFunctions.bohrChar (-(q.1 : ℂ).im) t).re| ≤
      ccmFuDeningerWeight δ q *
        ‖GaloisForLFunctions.bohrChar (-(q.1 : ℂ).im) t‖ := by
      exact mul_le_mul_of_nonneg_left
        (Complex.abs_re_le_norm
          (GaloisForLFunctions.bohrChar (-(q.1 : ℂ).im) t))
        (ccmFuDeningerWeight_nonneg hδ.le q)
    _ = ccmFuDeningerWeight δ q := by
      rw [GaloisForLFunctions.norm_bohrChar, mul_one]

theorem exists_ccmFuDeningerRealPhase_gt_half_mass
    (hRH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ)
    (hMass : 0 < ccmFuDeningerMass δ) (L : ℝ) :
    ∃ t : ℝ, L ≤ t ∧
      ccmFuDeningerMass δ / 2 < ccmFuDeningerRealPhase δ t := by
  let w : XiZeroCopy → ℝ := ccmFuDeningerWeight δ
  have hw0 : ∀ q, 0 ≤ w q := fun q => ccmFuDeningerWeight_nonneg hδ.le q
  have hwsum : Summable w := summable_ccmFuDeningerWeight_of_pos hRH hδ
  have hmassEq : ∑' q, w q = ccmFuDeningerMass δ := rfl
  obtain ⟨F, htail⟩ :=
    exists_finset_tsum_compl_lt hwsum.hasSum
      (show 0 < ccmFuDeningerMass δ / 8 by positivity)
  let omega : {q : XiZeroCopy // q ∈ F} → ℝ :=
    fun q => -(q.1.1 : ℂ).im
  obtain ⟨t, htL, hrec⟩ :=
    exists_simultaneous_phase_recurrence omega
      (ε := (1 / 4 : ℝ)) (by norm_num) L
  refine ⟨t, htL, ?_⟩
  let p : XiZeroCopy → ℝ := fun q =>
    w q * (GaloisForLFunctions.bohrChar (-(q.1 : ℂ).im) t).re
  have hpsum : Summable p := by
    simpa only [p, w] using
      summable_ccmFuDeningerRealPhase_term hRH hδ t
  have hhead :
      (3 / 4 : ℝ) * ∑ q ∈ F, w q ≤ ∑ q ∈ F, p q := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have habs := Complex.abs_re_le_norm
      (GaloisForLFunctions.bohrChar (-(q.1 : ℂ).im) t - 1)
    have hnorm := hrec ⟨q, hq⟩
    have hreal :
        (GaloisForLFunctions.bohrChar (-(q.1 : ℂ).im) t - 1).re =
          (GaloisForLFunctions.bohrChar (-(q.1 : ℂ).im) t).re - 1 := by simp
    rw [hreal] at habs
    have hre : (3 / 4 : ℝ) ≤
        (GaloisForLFunctions.bohrChar (-(q.1 : ℂ).im) t).re := by
      have := neg_le_of_abs_le (habs.trans hnorm)
      linarith
    dsimp only [p]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hre (hw0 q)
  let tailMass : ℝ := ∑' q : ↑((↑F : Set XiZeroCopy)ᶜ), w q
  let tailPhase : ℝ := ∑' q : ↑((↑F : Set XiZeroCopy)ᶜ), p q
  have htailPhase : -tailMass ≤ tailPhase := by
    dsimp only [tailMass, tailPhase]
    rw [← tsum_neg]
    apply Summable.tsum_le_tsum
    · intro q
      have hre : (-1 : ℝ) ≤
          (GaloisForLFunctions.bohrChar (-(q.1.1 : ℂ).im) t).re := by
        have habs := Complex.abs_re_le_norm
          (GaloisForLFunctions.bohrChar (-(q.1.1 : ℂ).im) t)
        rw [GaloisForLFunctions.norm_bohrChar] at habs
        exact neg_le_of_abs_le habs
      dsimp only [p]
      have := mul_le_mul_of_nonneg_left hre (hw0 q.1)
      linarith
    · exact (hwsum.subtype _).neg
    · exact hpsum.subtype _
  have hmassSplit :
      (∑ q ∈ F, w q) + tailMass = ccmFuDeningerMass δ := by
    have hsplit := hwsum.sum_add_tsum_compl (s := F)
    rw [hmassEq] at hsplit
    exact hsplit
  have hphaseSplit :
      (∑ q ∈ F, p q) + tailPhase = ccmFuDeningerRealPhase δ t := by
    have hsplit := hpsum.sum_add_tsum_compl (s := F)
    change (∑ q ∈ F, p q) + tailPhase = ∑' q, p q
    rw [hsplit]
  have htail' : tailMass < ccmFuDeningerMass δ / 8 := htail
  rw [← hphaseSplit]
  nlinarith

theorem exists_eventually_ccmFuDeningerMass_log_lower
    (hRH : RiemannHypothesis) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ T : ℝ in atTop,
      (η / 32) * Real.log T ≤
        ccmFuDeningerMass (ccmFuDeningerDyadicScale η T) := by
  obtain ⟨η, hη, hband⟩ :=
    exists_eventually_ccmFuDeningerDyadicMass_log_lower
  refine ⟨η, hη, ?_⟩
  filter_upwards [hband, eventually_ge_atTop (4 : ℝ)] with T hbandT hT4
  have hT0 : 0 < T := by linarith
  have hδ : 0 < ccmFuDeningerDyadicScale η T := by
    unfold ccmFuDeningerDyadicScale
    positivity
  have hsum := summable_ccmFuDeningerWeight_of_pos hRH hδ
  have hpartial : ccmFuDeningerDyadicMass η T ≤
      ccmFuDeningerMass (ccmFuDeningerDyadicScale η T) := by
    rw [ccmFuDeningerDyadicMass, ccmFuDeningerMass]
    exact hsum.sum_le_tsum _ (fun q _ =>
      ccmFuDeningerWeight_nonneg hδ.le q)
  exact hbandT.trans hpartial

def ccmFuDeningerPhase (δ t : ℝ) : ℂ :=
  ∑' q : XiZeroCopy,
    Complex.exp (((t * (q.1 : ℂ).im : ℝ) : ℂ) * I) *
      (ccmFuDeningerWeight δ q : ℂ)

theorem summable_ccmFuDeningerPhase_term (hRH : RiemannHypothesis)
    {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    Summable (fun q : XiZeroCopy =>
      Complex.exp (((t * (q.1 : ℂ).im : ℝ) : ℂ) * I) *
        (ccmFuDeningerWeight δ q : ℂ)) := by
  exact (deningerTimeTestLaplace_rawThetaEigen_summable
    (ccmFuDeningerTest δ t hδ ht)).congr (fun q =>
      deningerTimeTestLaplace_ccmFuDeningerTest_rawTheta_eq_phase_mul_weight
        hRH hδ ht q)

theorem deningerSpectralSum_ccmFuDeningerTest_eq_phase
    (hRH : RiemannHypothesis) {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    (∑' q : XiZeroCopy,
      deningerTimeTestLaplace (ccmFuDeningerTest δ t hδ ht)
        (deningerRawThetaEigen q)) = ccmFuDeningerPhase δ t := by
  unfold ccmFuDeningerPhase
  apply tsum_congr
  intro q
  exact deningerTimeTestLaplace_ccmFuDeningerTest_rawTheta_eq_phase_mul_weight
    hRH hδ ht q

theorem ccmFuDeningerPhase_re_eq_realPhase
    (hRH : RiemannHypothesis) {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    (ccmFuDeningerPhase δ t).re = ccmFuDeningerRealPhase δ t := by
  have hs := summable_ccmFuDeningerPhase_term hRH hδ ht
  rw [← Complex.reCLM_apply, ccmFuDeningerPhase,
    Complex.reCLM.map_tsum hs, ccmFuDeningerRealPhase]
  apply tsum_congr
  intro q
  rw [Complex.reCLM_apply]
  have hphase :
      Complex.exp (((t * (q.1 : ℂ).im : ℝ) : ℂ) * I) =
        GaloisForLFunctions.bohrChar (-(q.1 : ℂ).im) t := by
    rw [GaloisForLFunctions.bohrChar]
    congr 1
    push_cast
    ring
  rw [hphase]
  simp [mul_comm]

theorem deningerSpectralSum_ccmFuDeningerTest_re_eq_realPhase
    (hRH : RiemannHypothesis) {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    (∑' q : XiZeroCopy,
      deningerTimeTestLaplace (ccmFuDeningerTest δ t hδ ht)
        (deningerRawThetaEigen q)).re = ccmFuDeningerRealPhase δ t := by
  rw [deningerSpectralSum_ccmFuDeningerTest_eq_phase hRH hδ ht,
    ccmFuDeningerPhase_re_eq_realPhase hRH hδ ht]

theorem ccmFuDeningerRealPhase_cofinally_unbounded
    (hRH : RiemannHypothesis) :
    ∀ C L : ℝ, ∃ η T t : ℝ,
      0 < η ∧ 0 < T ∧
      0 < ccmFuDeningerDyadicScale η T ∧
      ccmFuDeningerDyadicScale η T *
          ccmFuAutocorrelationTest.radius < t ∧
      L ≤ t ∧ C < ccmFuDeningerRealPhase
        (ccmFuDeningerDyadicScale η T) t := by
  obtain ⟨η, hη, hmassEventually⟩ :=
    exists_eventually_ccmFuDeningerMass_log_lower hRH
  intro C L
  have hlog : ∀ᶠ T : ℝ in atTop,
      64 * |C| / η + 1 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually_ge_atTop (64 * |C| / η + 1)
  have hlarge : ∀ᶠ T : ℝ in atTop,
      0 < T ∧
      0 < ccmFuDeningerMass (ccmFuDeningerDyadicScale η T) ∧
      2 * C < ccmFuDeningerMass (ccmFuDeningerDyadicScale η T) := by
    filter_upwards [hmassEventually, hlog,
      eventually_ge_atTop (4 : ℝ)] with T hmass hlogT hT4
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
    exact ⟨hT, hmass0, hClower.trans_le hmass⟩
  obtain ⟨T, hT, hmass0, hmassC⟩ := hlarge.exists
  have hδ : 0 < ccmFuDeningerDyadicScale η T := by
    unfold ccmFuDeningerDyadicScale
    positivity
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
  refine ⟨η, T, t, hη, hT, hδ, htSupport, htL, ?_⟩
  linarith

theorem deningerSpectralSum_ccmFuDeningerTest_cofinally_unbounded
    (hRH : RiemannHypothesis) :
    ∀ C L : ℝ, ∃ η T t : ℝ,
      0 < η ∧ 0 < T ∧
      ∃ hδ : 0 < ccmFuDeningerDyadicScale η T,
      ∃ ht : ccmFuDeningerDyadicScale η T *
          ccmFuAutocorrelationTest.radius < t,
      L ≤ t ∧ C <
        (∑' q : XiZeroCopy,
          deningerTimeTestLaplace
            (ccmFuDeningerTest (ccmFuDeningerDyadicScale η T) t hδ ht)
            (deningerRawThetaEigen q)).re := by
  intro C L
  obtain ⟨η, T, t, hη, hT, hδ, ht, htL, hphase⟩ :=
    ccmFuDeningerRealPhase_cofinally_unbounded hRH C L
  refine ⟨η, T, t, hη, hT, hδ, ht, htL, ?_⟩
  rw [deningerSpectralSum_ccmFuDeningerTest_re_eq_realPhase hRH hδ ht]
  exact hphase

end

end RHTower
