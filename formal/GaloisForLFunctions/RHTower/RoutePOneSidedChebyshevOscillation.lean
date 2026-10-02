import GaloisForLFunctions.RHTower.RoutePOneSidedDampedResponse
import GaloisForLFunctions.RHTower.ChebyshevDeficitPrimitiveOneSidedRH

/-!
# Unconditional negative Chebyshev excursions for RP

The actual Chebyshev average plus the damped spectral response satisfies a homogeneous
one-sided damping law under RH. The archimedean density dominates the full polar forcing;
no counterterm is discarded. An eventual lower bound for the normalized Chebyshev error
would therefore bound the response from above, contradicting its positive escape.

The same contrary source bound implies RH through the corpus's one-sided deficit-primitive
Landau theorem. Thus the final negative-escape theorems are unconditional, including the
integer-head remainder statement. These excursions do not yet control RP's quadratic
mass compensation or prove its signed linear history floor.
-/

open Complex Filter MeasureTheory Set TopologicalSpace
open scoped FourierTransform Convolution
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower
open GaloisForLFunctions.RHTower
noncomputable section

theorem ccmFuNormalizedError_eq (x : ℝ) :
    criticalMellinNormalizedChebyshevError x =
      (Chebyshev.psi (Real.exp x) - Real.exp x) * Real.exp (-x / 2) := by
  rw [criticalMellinNormalizedChebyshevError, criticalMellinError,
    criticalCumulative_vonMangoldt_eq_psi, ← Real.exp_half,
    div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  ring

theorem locallyIntegrable_ccmFuNormalizedError :
    LocallyIntegrable criticalMellinNormalizedChebyshevError volume := by
  have he : LocallyIntegrable
      (fun x => Chebyshev.psi (Real.exp x) - Real.exp x) volume :=
    (Chebyshev.psi_mono.comp Real.exp_monotone).locallyIntegrable.sub
      Real.continuous_exp.locallyIntegrable
  rw [funext ccmFuNormalizedError_eq, locallyIntegrable_iff]
  intro K hK
  exact (he.integrableOn_isCompact hK).mul_continuousOn
    (by fun_prop : ContinuousOn (fun x : ℝ => Real.exp (-x / 2)) K) hK

def ccmFuReversedKernel (δ y : ℝ) : ℝ :=
  ccmFuTranslatedAutocorrelation δ 0 (-y)

def ccmFuChebyshevAverage (δ t : ℝ) : ℝ :=
  ∫ x : ℝ, criticalMellinNormalizedChebyshevError x *
    ccmFuTranslatedAutocorrelation δ t x

theorem hasCompactSupport_ccmFuReversedKernel {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (ccmFuReversedKernel δ) :=
  (hasCompactSupport_ccmFuTranslatedAutocorrelation (t := 0) hδ).comp_homeomorph
    (Homeomorph.neg ℝ)

theorem contDiff_ccmFuReversedKernel (δ : ℝ) : ContDiff ℝ 1 (ccmFuReversedKernel δ) := by
  unfold ccmFuReversedKernel ccmFuTranslatedAutocorrelation
  exact (contDiff_ccmFuAutocorrelationProfile.of_le (by simp)).comp (by fun_prop)

theorem hasDerivAt_ccmFuReversedKernel (δ y : ℝ) :
    HasDerivAt (ccmFuReversedKernel δ)
      (-ccmFuTranslatedAutocorrelationDeriv δ 0 (-y)) y := by
  have h := (hasDerivAt_ccmFuTranslatedAutocorrelation (δ := δ) (t := 0) (-y)).comp y
    ((hasDerivAt_id y).neg)
  convert! h using 1
  simp only [mul_neg, mul_one]

theorem ccmFuChebyshevAverage_eq_convolution (δ t : ℝ) :
    ccmFuChebyshevAverage δ t =
      convolution criticalMellinNormalizedChebyshevError (ccmFuReversedKernel δ)
        (ContinuousLinearMap.mul ℝ ℝ) volume t := by
  unfold ccmFuChebyshevAverage convolution ccmFuReversedKernel
  apply integral_congr_ae
  filter_upwards with x
  change _ * ccmFuAutocorrelationProfile ((x - t) / δ) =
    _ * ccmFuAutocorrelationProfile ((-(t - x) - 0) / δ)
  congr 2
  ring

theorem ccmFuChebyshevAverage_hasDerivAt {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (ccmFuChebyshevAverage δ)
      (-(∫ x : ℝ, criticalMellinNormalizedChebyshevError x *
        ccmFuTranslatedAutocorrelationDeriv δ t x)) t := by
  have hc := (hasCompactSupport_ccmFuReversedKernel hδ).hasDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) locallyIntegrable_ccmFuNormalizedError
    (contDiff_ccmFuReversedKernel δ) t
  rw [← funext (ccmFuChebyshevAverage_eq_convolution δ)] at hc
  apply hc.congr_deriv
  unfold convolution
  have hd : ∀ x : ℝ, deriv (ccmFuReversedKernel δ) (t - x) =
      -ccmFuTranslatedAutocorrelationDeriv δ t x := by
    intro x
    rw [(hasDerivAt_ccmFuReversedKernel δ (t - x)).deriv]
    unfold ccmFuTranslatedAutocorrelationDeriv
    congr 3
    ring
  simp_rw [hd]
  change (∫ x : ℝ, criticalMellinNormalizedChebyshevError x *
    -ccmFuTranslatedAutocorrelationDeriv δ t x) = _
  simp_rw [mul_neg]
  exact integral_neg _

def ccmFuArchimedeanRealProfile (δ t x : ℝ) : ℝ :=
  ccmFuDeningerProfile δ t x * (1 - Real.exp (-2 * x))⁻¹

theorem continuous_ccmFuArchimedeanRealProfile {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    Continuous (ccmFuArchimedeanRealProfile δ t) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : 0 < x
  · have hd : 1 - Real.exp (-2 * x) ≠ 0 := by
      have h := Real.exp_lt_one_iff.mpr (by linarith : -2 * x < 0)
      linarith
    exact ((contDiff_ccmFuDeningerProfile δ t).continuous.continuousAt).mul
      ((by fun_prop : ContinuousAt (fun y : ℝ => 1 - Real.exp (-2 * y)) x).inv₀ hd)
  · have hxlt : x < t - δ * ccmFuAutocorrelationTest.radius := by linarith
    have heq : ccmFuArchimedeanRealProfile δ t =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hxlt] with y hy
      simp only [ccmFuArchimedeanRealProfile, ccmFuDeningerProfile,
        ccmFuTranslatedAutocorrelation_eq_zero_of_lt_lower hδ hy, mul_zero, zero_mul]
    exact continuousAt_const.congr_of_eventuallyEq heq

theorem ccmFuArchimedeanRealProfile_ge {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) (x : ℝ) :
    ccmFuDeningerProfile δ t x ≤ ccmFuArchimedeanRealProfile δ t x := by
  by_cases hz : ccmFuDeningerProfile δ t x = 0
  · simp [ccmFuArchimedeanRealProfile, hz]
  have hxS : x ∈ (ccmFuDeningerSupport δ t : Set ℝ) := by
    by_contra hn
    exact hz (ccmFuDeningerProfile_zero_on_compl hδ hn)
  have hx : 0 < x := lt_of_lt_of_le (by linarith : 0 < t - δ * ccmFuAutocorrelationTest.radius)
    hxS.1
  have hd : 0 < 1 - Real.exp (-2 * x) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hinv : 1 ≤ (1 - Real.exp (-2 * x))⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hd]
    linarith [Real.exp_pos (-2 * x)]
  exact le_mul_of_one_le_right (ccmFuDeningerTest_nonneg hδ ht x) hinv

theorem ccmFuArchimedeanIntegral_dominates_polar {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    (∫ x : ℝ, ccmFuDeningerProfile δ t x) ≤
      (∫ x : ℝ, (ccmFuDeningerTest δ t hδ ht x : ℂ) *
        deningerArchimedeanLefschetzDensity x).re := by
  have hs : HasCompactSupport (ccmFuDeningerProfile δ t) :=
    (ccmFuDeningerTest δ t hδ ht).hasCompactSupport
  have hi : Integrable (ccmFuDeningerProfile δ t) :=
    (contDiff_ccmFuDeningerProfile δ t).continuous.integrable_of_hasCompactSupport hs
  have ha : Integrable (ccmFuArchimedeanRealProfile δ t) :=
    (continuous_ccmFuArchimedeanRealProfile hδ ht).integrable_of_hasCompactSupport hs.mul_right
  have heq : (fun x : ℝ => (ccmFuDeningerTest δ t hδ ht x : ℂ) *
      deningerArchimedeanLefschetzDensity x) = fun x => (ccmFuArchimedeanRealProfile δ t x : ℂ) := by
    funext x
    simp only [ccmFuDeningerTest_apply, deningerArchimedeanLefschetzDensity,
      ccmFuArchimedeanRealProfile, Complex.ofReal_mul]
  rw [heq, integral_complex_ofReal, Complex.ofReal_re]
  exact integral_mono hi ha (ccmFuArchimedeanRealProfile_ge hδ ht)

private theorem ccmFuWindowDeriv_zero_above {δ t x : ℝ} (hδ : 0 < δ)
    (hx : t + δ * ccmFuAutocorrelationTest.radius < x) :
    ccmFuTranslatedAutocorrelationDeriv δ t x = 0 := by
  rw [ccmFuTranslatedAutocorrelationDeriv_eq_deriv]
  have heq : ccmFuTranslatedAutocorrelation δ t =ᶠ[nhds x] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact ccmFuTranslatedAutocorrelation_eq_zero_of_upper_lt hδ hy
  rw [heq.deriv_eq]
  simp

theorem integral_ccmFuWindow_eq_full {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) (f : ℝ → ℝ) :
    (∫ x in (0 : ℝ)..2 * t, f x * ccmFuTranslatedAutocorrelation δ t x) =
      ∫ x : ℝ, f x * ccmFuTranslatedAutocorrelation δ t x := by
  apply IntervalIntegral.integral_eq_integral_of_support_subset_Icc
  intro x hx
  constructor
  · by_contra hn
    have hz := ccmFuTranslatedAutocorrelation_eq_zero_of_lt_lower hδ
      (by linarith : x < t - δ * ccmFuAutocorrelationTest.radius)
    exact hx (by simp [hz])
  · by_contra hn
    have hz := ccmFuTranslatedAutocorrelation_eq_zero_of_upper_lt hδ
      (by linarith : t + δ * ccmFuAutocorrelationTest.radius < x)
    exact hx (by simp [hz])

theorem integral_ccmFuWindowDeriv_eq_full {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) (f : ℝ → ℝ) :
    (∫ x in (0 : ℝ)..2 * t, f x * ccmFuTranslatedAutocorrelationDeriv δ t x) =
      ∫ x : ℝ, f x * ccmFuTranslatedAutocorrelationDeriv δ t x := by
  apply IntervalIntegral.integral_eq_integral_of_support_subset_Icc
  intro x hx
  constructor
  · by_contra hn
    have hz := ccmFuTranslatedAutocorrelationDeriv_eq_zero_of_lt_lower hδ
      (by linarith : x < t - δ * ccmFuAutocorrelationTest.radius)
    exact hx (by simp [hz])
  · by_contra hn
    have hz := ccmFuWindowDeriv_zero_above hδ
      (by linarith : t + δ * ccmFuAutocorrelationTest.radius < x)
    exact hx (by simp [hz])

theorem integral_ccmFuCutoffWindowDeriv_eq_full {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    (∫ x in (0 : ℝ)..2 * t, criticalMellinNormalizedErrorCutoff (2 * t) x *
      ccmFuTranslatedAutocorrelationDeriv δ t x) =
      ∫ x : ℝ, criticalMellinNormalizedChebyshevError x *
        ccmFuTranslatedAutocorrelationDeriv δ t x := by
  rw [← integral_ccmFuWindowDeriv_eq_full hδ ht]
  have ht0 : 0 ≤ 2 * t := by
    nlinarith [ccmFuAutocorrelationTest.one_lt_radius]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le ht0] at hx
  simp only [criticalMellinNormalizedErrorCutoff, if_pos hx]

theorem integral_ccmFuCutoffWindow_eq_average {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    (∫ x in (0 : ℝ)..2 * t, ccmFuTranslatedAutocorrelation δ t x *
      criticalMellinNormalizedErrorCutoff (2 * t) x) = ccmFuChebyshevAverage δ t := by
  rw [ccmFuChebyshevAverage, ← integral_ccmFuWindow_eq_full hδ ht]
  have ht0 : 0 ≤ 2 * t := by
    nlinarith [ccmFuAutocorrelationTest.one_lt_radius]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le ht0] at hx
  change ccmFuTranslatedAutocorrelation δ t x *
    (if x ∈ Icc 0 (2 * t) then criticalMellinNormalizedChebyshevError x else 0) = _
  rw [if_pos hx]
  exact mul_comm _ _

theorem ccmFuPolarForcing_eq_integral {δ t : ℝ} (hδ : 0 < δ)
    (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    -(∫ x in (0 : ℝ)..2 * t, (1 - 2 * Real.exp (-x / 2)) *
      ccmFuTranslatedAutocorrelationDeriv δ t x) =
      ∫ x : ℝ, ccmFuDeningerProfile δ t x := by
  let u : ℝ → ℝ := fun x => 1 - 2 * Real.exp (-x / 2)
  let u' : ℝ → ℝ := fun x => Real.exp (-x / 2)
  let φ := ccmFuTranslatedAutocorrelation δ t
  let φ' := ccmFuTranslatedAutocorrelationDeriv δ t
  have hu : Continuous u := by fun_prop
  have hu' : Continuous u' := by fun_prop
  have hφ := continuous_ccmFuTranslatedAutocorrelation δ t
  have hφ' := continuous_ccmFuTranslatedAutocorrelationDeriv δ t
  have hsφ := hasCompactSupport_ccmFuTranslatedAutocorrelation (t := t) hδ
  have hsφ' := hasCompactSupport_ccmFuTranslatedAutocorrelationDeriv (t := t) hδ
  have hi : Integrable (fun x => u x * φ x) :=
    (hu.mul hφ).integrable_of_hasCompactSupport hsφ.mul_left
  have hi' : Integrable (fun x => u x * φ' x) :=
    (hu.mul hφ').integrable_of_hasCompactSupport hsφ'.mul_left
  have hdi : Integrable (fun x => u' x * φ x) :=
    (hu'.mul hφ).integrable_of_hasCompactSupport hsφ.mul_left
  have hd : ∀ x, HasDerivAt u (u' x) x := by
    intro x
    have h := (((((hasDerivAt_id x).neg).div_const 2).exp).const_mul 2).const_sub 1
    convert! h using 1
    dsimp [u']
    ring
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hd x)
    (fun x _ => hasDerivAt_ccmFuTranslatedAutocorrelation x) hi' hdi hi
  rw [integral_ccmFuWindowDeriv_eq_full hδ ht]
  change -(∫ x : ℝ, u x * φ' x) = ∫ x : ℝ, u' x * φ x
  rw [hibp, neg_neg]

def ccmFuCombinedResponse (δ t : ℝ) : ℝ :=
  ccmFuChebyshevAverage δ t + ccmFuRealResponse δ t

theorem ccmFuCombinedResponse_hasDerivAt (hRH : RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (ccmFuCombinedResponse δ)
      (-(∫ x : ℝ, criticalMellinNormalizedChebyshevError x *
        ccmFuTranslatedAutocorrelationDeriv δ t x) +
        ccmFuDeningerRealPhase δ t - (1 / 2 : ℝ) * ccmFuRealResponse δ t) t := by
  convert! (ccmFuChebyshevAverage_hasDerivAt hδ t).add
    (ccmFuRealResponse_hasDerivAt hRH hδ t) using 1
  ring

theorem ccmFuCombinedResponse_damping_nonpos (hRH : RiemannHypothesis)
    {δ t : ℝ} (hδ : 0 < δ) (ht : δ * ccmFuAutocorrelationTest.radius < t) :
    deriv (ccmFuCombinedResponse δ) t + (1 / 2 : ℝ) * ccmFuCombinedResponse δ t ≤ 0 := by
  have hp := deningerSpectralSum_ccmFuDeningerTest_re_eq_realPhase hRH hδ ht
  rw [deningerSpectralSum_ccmFu_eq_criticalMellinPairing_sub_arch hδ ht,
    Complex.sub_re, criticalMellinStieltjesPairing_ccmFu_re_decomposition hδ ht,
    integral_ccmFuCutoffWindowDeriv_eq_full hδ ht,
    integral_ccmFuCutoffWindow_eq_average hδ ht,
    ccmFuPolarForcing_eq_integral hδ ht] at hp
  have ha := ccmFuArchimedeanIntegral_dominates_polar hδ ht
  rw [(ccmFuCombinedResponse_hasDerivAt hRH hδ t).deriv, ccmFuCombinedResponse]
  linarith

def ccmFuWeightedCombinedResponse (δ t : ℝ) : ℝ :=
  Real.exp (t / 2) * ccmFuCombinedResponse δ t

theorem ccmFuWeightedCombinedResponse_hasDerivAt (hRH : RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (ccmFuWeightedCombinedResponse δ)
      (Real.exp (t / 2) * (deriv (ccmFuCombinedResponse δ) t +
        (1 / 2 : ℝ) * ccmFuCombinedResponse δ t)) t := by
  have hY := ccmFuCombinedResponse_hasDerivAt hRH hδ t
  have he := (((hasDerivAt_id t).div_const 2).exp).mul hY
  simp only [id_eq] at he
  convert! he using 1
  rw [hY.deriv]
  ring

theorem ccmFuWeightedCombinedResponse_antitoneOn (hRH : RiemannHypothesis)
    {δ T : ℝ} (hδ : 0 < δ) (hT : δ * ccmFuAutocorrelationTest.radius < T) :
    AntitoneOn (ccmFuWeightedCombinedResponse δ) (Ici T) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici T)
    (f' := fun t => Real.exp (t / 2) * (deriv (ccmFuCombinedResponse δ) t +
      (1 / 2 : ℝ) * ccmFuCombinedResponse δ t))
  · exact (continuous_iff_continuousAt.mpr
      (fun t => (ccmFuWeightedCombinedResponse_hasDerivAt hRH hδ t).continuousAt)).continuousOn
  · intro t _
    exact (ccmFuWeightedCombinedResponse_hasDerivAt hRH hδ t).hasDerivWithinAt
  · intro t ht
    have hTt : T ≤ t := interior_subset ht
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (ccmFuCombinedResponse_damping_nonpos hRH hδ (hT.trans_le hTt))

theorem ccmFuCombinedResponse_eventual_upper (hRH : RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, ccmFuCombinedResponse δ t ≤ ε := by
  let T := δ * ccmFuAutocorrelationTest.radius + 1
  have hT : δ * ccmFuAutocorrelationTest.radius < T := by dsimp [T]; linarith
  have hm := ccmFuWeightedCombinedResponse_antitoneOn hRH hδ hT
  have hz : Tendsto (fun t : ℝ => ccmFuWeightedCombinedResponse δ T * Real.exp (-t / 2))
      atTop (nhds 0) := by
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    simpa only [Function.comp_def, neg_div, mul_zero, id_eq] using
      he.const_mul (ccmFuWeightedCombinedResponse δ T)
  filter_upwards [eventually_ge_atTop T, hz.eventually_le_const hε] with t ht hsmall
  have hmono := hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  have hscaled := mul_le_mul_of_nonneg_left hmono (Real.exp_pos (-t / 2)).le
  have hc : Real.exp (-t / 2) * ccmFuWeightedCombinedResponse δ t =
      ccmFuCombinedResponse δ t := by
    rw [ccmFuWeightedCombinedResponse, ← mul_assoc, ← Real.exp_add]
    simp only [show -t / 2 + t / 2 = 0 by ring, Real.exp_zero, one_mul]
  rw [hc] at hscaled
  exact hscaled.trans (by simpa only [mul_comm] using hsmall)

theorem ccmFuChebyshevAverage_lower_of_source_lower {C L δ t : ℝ} (hδ : 0 < δ)
    (hsource : ∀ x : ℝ, L ≤ x → -C ≤ criticalMellinNormalizedChebyshevError x)
    (ht : L + δ * ccmFuAutocorrelationTest.radius ≤ t) :
    -C * δ * (∫ x : ℝ, |ccmFuAutocorrelationProfile x|) ≤ ccmFuChebyshevAverage δ t := by
  let φ := ccmFuTranslatedAutocorrelation δ t
  have hφ : Integrable φ := integrable_ccmFuTranslatedAutocorrelation hδ
  have hi : Integrable (fun x : ℝ => criticalMellinNormalizedChebyshevError x * φ x) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_ccmFuNormalizedError.integrable_smul_right_of_hasCompactSupport
        (continuous_ccmFuTranslatedAutocorrelation δ t)
        (hasCompactSupport_ccmFuTranslatedAutocorrelation hδ)
  have hmass : (∫ x : ℝ, φ x) = δ * ∫ x : ℝ, |ccmFuAutocorrelationProfile x| := by
    have h := integral_abs_ccmFuTranslatedAutocorrelation (t := t) hδ
    have heq : (fun x : ℝ => |ccmFuTranslatedAutocorrelation δ t x|) = φ := by
      funext x
      exact abs_of_nonneg (ccmFuAutocorrelationProfile_nonneg _)
    rwa [heq] at h
  have hpoint : ∀ x : ℝ, -C * φ x ≤ criticalMellinNormalizedChebyshevError x * φ x := by
    intro x
    by_cases hz : φ x = 0
    · simp [hz]
    have hxS : x ∈ (ccmFuDeningerSupport δ t : Set ℝ) := by
      by_contra hn
      exact hz (ccmFuTranslatedAutocorrelation_zero_on_compl hδ hn)
    have hx : L ≤ x := by
      have h := hxS.1
      change t - δ * ccmFuAutocorrelationTest.radius ≤ x at h
      linarith
    exact mul_le_mul_of_nonneg_right (hsource x hx) (ccmFuAutocorrelationProfile_nonneg _)
  have hb := integral_mono (hφ.const_mul (-C)) hi hpoint
  rw [integral_const_mul, hmass] at hb
  simpa only [ccmFuChebyshevAverage, φ, mul_assoc] using hb

theorem not_ccmFuNormalizedError_eventually_lower_bounded_of_rh (hRH : RiemannHypothesis) :
    ¬ ∃ C L : ℝ, ∀ x : ℝ, L ≤ x → -C ≤ criticalMellinNormalizedChebyshevError x := by
  rintro ⟨C, L, hsource⟩
  let K := C * ∫ x : ℝ, |ccmFuAutocorrelationProfile x|
  obtain ⟨δ, t, hδ, _, hescape⟩ := ccmFuRealResponse_positive_escape hRH K 0
  have hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ u in atTop, ccmFuRealResponse δ u ≤ K * δ + ε := by
    intro ε hε
    filter_upwards [ccmFuCombinedResponse_eventual_upper hRH hδ hε,
      eventually_ge_atTop (L + δ * ccmFuAutocorrelationTest.radius)] with u hu hlu
    have hA := ccmFuChebyshevAverage_lower_of_source_lower hδ hsource hlu
    dsimp only [ccmFuCombinedResponse] at hu
    dsimp only [K]
    nlinarith
  exact not_lt_of_ge (ccmFuRealResponse_le_of_eventual_upper hRH hδ hu t) hescape

theorem ccmFuGlobalLower_of_eventual_lower {C L : ℝ}
    (hsource : ∀ x : ℝ, L ≤ x → -C ≤ criticalMellinNormalizedChebyshevError x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 0 ≤ x → -B ≤ criticalMellinNormalizedChebyshevError x := by
  let M := max L 0
  let A := criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp M) + Real.exp M
  have hA : 0 ≤ A := add_nonneg (criticalCumulative_vonMangoldt_nonneg _) (Real.exp_pos _).le
  refine ⟨|C| + A, add_nonneg (abs_nonneg _) hA, ?_⟩
  intro x hx
  by_cases hMx : M ≤ x
  · have h := hsource x ((le_max_left L 0).trans hMx)
    linarith [le_abs_self C]
  · have h := abs_criticalMellinNormalizedChebyshevError_le_endpoint
      (show x ∈ Icc 0 M from ⟨hx, (lt_of_not_ge hMx).le⟩)
    have hneg := (abs_le.mp h).1
    change -A ≤ criticalMellinNormalizedChebyshevError x at hneg
    linarith [abs_nonneg C]

theorem riemannHypothesis_of_ccmFuNormalizedError_eventual_lower {C L : ℝ}
    (hsource : ∀ x : ℝ, L ≤ x → -C ≤ criticalMellinNormalizedChebyshevError x) :
    RiemannHypothesis := by
  obtain ⟨B, hB, hb⟩ := ccmFuGlobalLower_of_eventual_lower hsource
  apply riemannHypothesis_of_logChebyshevDeficitPrimitive_le_mul (B := B)
  intro T hT
  have hpoint : ∀ x ∈ Icc (0 : ℝ) T,
      chebyshevLogDeficit x ≤ B * Real.exp (T / 2) := by
    intro x hx
    have h := mul_le_mul_of_nonneg_right (hb x hx.1) (Real.exp_pos (x / 2)).le
    have hcancel : criticalMellinNormalizedChebyshevError x * Real.exp (x / 2) =
        Chebyshev.psi (Real.exp x) - Real.exp x := by
      rw [ccmFuNormalizedError_eq, mul_assoc, ← Real.exp_add]
      simp only [show -x / 2 + x / 2 = 0 by ring, Real.exp_zero, mul_one]
    rw [hcancel] at h
    have hm : B * Real.exp (x / 2) ≤ B * Real.exp (T / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hx.2])) hB
    dsimp only [chebyshevLogDeficit]
    linarith
  have hint := intervalIntegral.integral_mono_on hT (intervalIntegrable_chebyshevLogDeficit 0 T)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B * Real.exp (T / 2)) volume 0 T)
    hpoint
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hint
  change ccmLogChebyshevDeficitPrimitive T ≤ T * (B * Real.exp (T / 2)) at hint
  have hexp := Real.exp_pos (T / 2)
  nlinarith

theorem not_ccmFuNormalizedError_eventually_lower_bounded :
    ¬ ∃ C L : ℝ, ∀ x : ℝ, L ≤ x → -C ≤ criticalMellinNormalizedChebyshevError x := by
  rintro ⟨C, L, hsource⟩
  exact not_ccmFuNormalizedError_eventually_lower_bounded_of_rh
    (riemannHypothesis_of_ccmFuNormalizedError_eventual_lower hsource) ⟨C, L, hsource⟩

theorem ccmFuNormalizedError_negative_escape (C L : ℝ) :
    ∃ x : ℝ, L ≤ x ∧ criticalMellinNormalizedChebyshevError x < -C := by
  by_contra! h
  exact not_ccmFuNormalizedError_eventually_lower_bounded ⟨C, L, h⟩

theorem ccmFuPsiRemainder_negative_escape (C : ℝ) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ 3 ≤ N ∧ psiRemainder N < -C * Real.sqrt (N : ℝ) := by
  obtain ⟨x, hx, hneg⟩ := ccmFuNormalizedError_negative_escape (|C| + 1)
    (Real.log ((M : ℝ) + 3))
  let N := ⌊Real.exp x⌋₊
  have hlarge : (M : ℝ) + 3 ≤ Real.exp x := by
    rw [← Real.exp_log (by positivity : 0 < (M : ℝ) + 3)]
    exact Real.exp_le_exp.mpr hx
  have hN : M + 3 ≤ N := by
    apply (Nat.le_floor_iff (Real.exp_pos x).le).mpr
    exact_mod_cast hlarge
  refine ⟨N, by omega, by omega, ?_⟩
  have hs : Real.sqrt (N : ℝ) ≤ Real.exp (x / 2) := by
    rw [Real.exp_half]
    exact Real.sqrt_le_sqrt (Nat.floor_le (Real.exp_pos x).le)
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := by
    apply Real.one_le_sqrt.mpr
    exact_mod_cast (show 1 ≤ N by omega)
  have hc : Real.exp (-x / 2) * Real.exp (x / 2) = 1 := by
    rw [← Real.exp_add]
    simp only [show -x / 2 + x / 2 = 0 by ring, Real.exp_zero]
  have heq : criticalMellinNormalizedChebyshevError x * Real.exp (x / 2) =
      psiRemainder N + ((N : ℝ) - Real.exp x) := by
    rw [criticalMellinNormalizedChebyshevError_eq_discrete_add_floor]
    change (Real.exp (-x / 2) * psiRemainder N +
      Real.exp (-x / 2) * ((N : ℝ) - Real.exp x)) * Real.exp (x / 2) = _
    calc
      _ = (Real.exp (-x / 2) * Real.exp (x / 2)) *
          (psiRemainder N + ((N : ℝ) - Real.exp x)) := by ring
      _ = _ := by rw [hc, one_mul]
  have hmul := mul_lt_mul_of_pos_right hneg (Real.exp_pos (x / 2))
  rw [heq] at hmul
  have hfloor := (abs_le.mp (abs_natFloor_exp_sub_le_one x)).1
  change -1 ≤ (N : ℝ) - Real.exp x at hfloor
  have hscale := mul_le_mul_of_nonneg_left hs (abs_nonneg C)
  have hC := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg (N : ℝ))
  nlinarith

end
end RHTower
