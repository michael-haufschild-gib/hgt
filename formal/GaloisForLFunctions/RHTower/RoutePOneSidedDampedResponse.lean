import GaloisForLFunctions.RHTower.CCM.CCMFULittlewoodNoGo
import GaloisForLFunctions.RHTower.WeilLagFunctionRecurrence
import GaloisForLFunctions.HTGeometry.BohrExponentialSeriesCoefficient

/-!
# One-sided escape of the literal compact-autocorrelation response

The damped response has coefficients `w_delta(q)/(1/2+i*gamma(q))`.
Reflection cancels its sine contribution; the remaining cosine series is controlled by the
summable lag weights. Bohr recurrence therefore converts an eventual one-sided upper bound
into a two-sided bound. A centered compact-test pairing cancels the resolvent by integration
by parts. Finite-head continuity at scale zero would then bound the Deninger mass, contradicting
its already-proved growth. Consequently the response divided by its scale escapes upward at
arbitrarily late times under RH.

This is the spectral component of the RP one-sided Chebyshev argument. RH is an explicit
hypothesis here. The arithmetic comparison that would derive it from a contrary one-sided
source bound, and the ratio-one terminal compensation barrier, remain separate obligations.
-/

open Complex Filter MeasureTheory Set TopologicalSpace
open scoped FourierTransform
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower
open GaloisForLFunctions.RHTower
noncomputable section

theorem ccmFuBaseFourier_norm_le_one (ξ : ℝ) : ‖ccmFuBaseFourier ξ‖ ≤ 1 := by
  have h := VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ) 
    (suzukiRestrictedWeilCoreSchwartz ccmFuBumpCore : ℝ → ℂ) ξ
  have hmass : (∫ x : ℝ,
      ‖(suzukiRestrictedWeilCoreSchwartz ccmFuBumpCore : ℝ → ℂ) x‖) = 1 := by
    change (∫ x : ℝ, ‖(suzukiMollifier (1 / 8) x : ℂ)‖) = 1
    simp_rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (suzukiMollifier_nonneg (by norm_num : (0 : ℝ) < 1 / 8) _)]
    exact integral_suzukiMollifier (by norm_num)
  exact h.trans_eq hmass

theorem ccmFuDeningerWeight_le_scale {δ : ℝ} (hδ : 0 ≤ δ) (q : XiZeroCopy) :
    ccmFuDeningerWeight δ q ≤ δ := by
  have h := ccmFuBaseFourier_norm_le_one (-δ * (q.1 : ℂ).im / (2 * Real.pi))
  have hsq : ‖ccmFuBaseFourier (-δ * (q.1 : ℂ).im / (2 * Real.pi))‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (ccmFuBaseFourier (-δ * (q.1 : ℂ).im / (2 * Real.pi)))]
  exact (mul_le_mul_of_nonneg_left hsq hδ).trans_eq (mul_one δ)

def ccmFuResponsePole (q : XiZeroCopy) : ℂ :=
  1 / 2 + (zeroOrdinate q : ℂ) * I

theorem ccmFuResponsePole_ne_zero (q : XiZeroCopy) : ccmFuResponsePole q ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num [ccmFuResponsePole] at hr

theorem ccmFuResponsePole_norm_lower (q : XiZeroCopy) :
    (1 / 2 : ℝ) ≤ ‖ccmFuResponsePole q‖ := by
  simpa [ccmFuResponsePole] using Complex.abs_re_le_norm (ccmFuResponsePole q)

def ccmFuResponseCoefficient (δ : ℝ) (q : XiZeroCopy) : ℂ :=
  (ccmFuDeningerWeight δ q : ℂ) / ccmFuResponsePole q

def ccmFuComplexResponse (δ : ℝ) : ℝ → ℂ :=
  expSeriesCarrier (ccmFuResponseCoefficient δ) zeroOrdinate

def ccmFuRealResponse (δ t : ℝ) : ℝ := (ccmFuComplexResponse δ t).re

theorem ccmFuResponseCoefficient_norm_le {δ : ℝ} (hδ : 0 ≤ δ) (q : XiZeroCopy) :
    ‖ccmFuResponseCoefficient δ q‖ ≤ 2 * ccmFuDeningerWeight δ q := by
  rw [ccmFuResponseCoefficient, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ccmFuDeningerWeight_nonneg hδ q)]
  apply (div_le_iff₀ (norm_pos_iff.mpr (ccmFuResponsePole_ne_zero q))).mpr
  have h := mul_le_mul_of_nonneg_left (ccmFuResponsePole_norm_lower q)
    (ccmFuDeningerWeight_nonneg hδ q)
  nlinarith

theorem summable_norm_ccmFuResponseCoefficient (hRH : RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) : Summable (fun q => ‖ccmFuResponseCoefficient δ q‖) := by
  apply ((summable_ccmFuDeningerWeight_of_pos hRH hδ).mul_left 2).of_norm_bounded
  intro q
  rw [norm_norm]
  exact ccmFuResponseCoefficient_norm_le hδ.le q

theorem isBohrAlmostPeriodic_ccmFuComplexResponse (hRH : RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) :
    _root_.HTGeometry.IsBohrAlmostPeriodic (ccmFuComplexResponse δ) :=
  isBohrAlmostPeriodic_expSeriesCarrier (summable_norm_ccmFuResponseCoefficient hRH hδ) _

theorem ccmFuResponseTerm_re (δ t : ℝ) (q : XiZeroCopy) :
    (ccmFuResponseCoefficient δ q * expChar (zeroOrdinate q) t).re =
      ccmFuDeningerWeight δ q *
        ((1 / 2 : ℝ) * Real.cos (zeroOrdinate q * t) +
          zeroOrdinate q * Real.sin (zeroOrdinate q * t)) /
        (1 / 4 + zeroOrdinate q ^ 2) := by
  have hp : expChar (zeroOrdinate q) t =
      (Real.cos (zeroOrdinate q * t) : ℂ) +
        (Real.sin (zeroOrdinate q * t) : ℂ) * I := by
    rw [expChar, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [ccmFuResponseCoefficient, div_mul_eq_mul_div, Complex.div_re, hp]
  norm_num only [ccmFuResponsePole, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im]
  ring

private theorem ccmFuResponseTerm_reflection (δ t : ℝ) (q : XiZeroCopy) :
    (ccmFuResponseCoefficient δ q * expChar (zeroOrdinate q) t).re +
      (ccmFuResponseCoefficient δ q * expChar (zeroOrdinate q) (-t)).re =
      ccmFuDeningerWeight δ q * cosWeight q * Real.cos (zeroOrdinate q * t) := by
  rw [ccmFuResponseTerm_re, ccmFuResponseTerm_re]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, cosWeight]
  ring

private theorem summable_ccmFuResponseTerm_re (hRH : RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    Summable (fun q => (ccmFuResponseCoefficient δ q * expChar (zeroOrdinate q) t).re) :=
  Complex.reCLM.summable
    (summable_expSeries (summable_norm_ccmFuResponseCoefficient hRH hδ) zeroOrdinate t)

private theorem ccmFuRealResponse_eq_tsum (hRH : RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : ccmFuRealResponse δ t =
    ∑' q, (ccmFuResponseCoefficient δ q * expChar (zeroOrdinate q) t).re :=
  Complex.re_tsum
    (summable_expSeries (summable_norm_ccmFuResponseCoefficient hRH hδ) zeroOrdinate t)

theorem ccmFuRealResponse_reflection (hRH : RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ccmFuRealResponse δ t + ccmFuRealResponse δ (-t) =
      ∑' q : XiZeroCopy, ccmFuDeningerWeight δ q * cosWeight q *
        Real.cos (zeroOrdinate q * t) := by
  rw [ccmFuRealResponse_eq_tsum hRH hδ t, ccmFuRealResponse_eq_tsum hRH hδ (-t),
    ← (summable_ccmFuResponseTerm_re hRH hδ t).tsum_add
      (summable_ccmFuResponseTerm_re hRH hδ (-t))]
  exact tsum_congr (ccmFuResponseTerm_reflection δ t)

theorem abs_ccmFuRealResponse_reflection_le (hRH : RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    |ccmFuRealResponse δ t + ccmFuRealResponse δ (-t)| ≤ δ * poleSharpConstant := by
  rw [ccmFuRealResponse_reflection hRH hδ]
  have hm := (summable_cosWeight hRH).mul_left δ
  have hb : ∀ q : XiZeroCopy,
      ‖ccmFuDeningerWeight δ q * cosWeight q * Real.cos (zeroOrdinate q * t)‖ ≤
        δ * cosWeight q := by
    intro q
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (ccmFuDeningerWeight_nonneg hδ.le q),
      abs_of_pos (cosWeight_pos q)]
    calc
      _ ≤ ccmFuDeningerWeight δ q * cosWeight q * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
          (mul_nonneg (ccmFuDeningerWeight_nonneg hδ.le q) (cosWeight_pos q).le)
      _ ≤ δ * cosWeight q := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right (ccmFuDeningerWeight_le_scale hδ.le q)
          (cosWeight_pos q).le
  have hs := hm.of_norm_bounded hb
  calc
    _ ≤ ∑' q, ‖ccmFuDeningerWeight δ q * cosWeight q * Real.cos (zeroOrdinate q * t)‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' q, δ * cosWeight q := hs.norm.tsum_le_tsum hb hm
    _ = δ * poleSharpConstant := by rw [tsum_mul_left, tsum_cosWeight hRH]

theorem ccmFuRealResponse_le_of_eventual_upper (hRH : RiemannHypothesis)
    {δ C : ℝ} (hδ : 0 < δ)
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ccmFuRealResponse δ t ≤ C + ε)
    (x : ℝ) : ccmFuRealResponse δ x ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨L, _, hrec⟩ := isBohrAlmostPeriodic_ccmFuComplexResponse hRH hδ
    (ε / 2) (by linarith)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hupper (ε / 2) (by linarith))
  obtain ⟨τ, hτ, hclose⟩ := hrec (T - x)
  have ht : T ≤ x + τ := by linarith [hτ.1]
  have hb := hT (x + τ) ht
  have hd := (Complex.abs_re_le_norm
    (ccmFuComplexResponse δ (x + τ) - ccmFuComplexResponse δ x)).trans (hclose x)
  change |ccmFuRealResponse δ (x + τ) - ccmFuRealResponse δ x| ≤ ε / 2 at hd
  linarith [(abs_le.mp hd).1]

theorem abs_ccmFuRealResponse_le_of_eventual_upper (hRH : RiemannHypothesis)
    {δ C : ℝ} (hδ : 0 < δ)
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ccmFuRealResponse δ t ≤ C + ε)
    (x : ℝ) : |ccmFuRealResponse δ x| ≤ C + δ * poleSharpConstant := by
  have hx := ccmFuRealResponse_le_of_eventual_upper hRH hδ hupper x
  have hn := ccmFuRealResponse_le_of_eventual_upper hRH hδ hupper (-x)
  have hr := abs_ccmFuRealResponse_reflection_le hRH hδ x
  have hp : 0 ≤ δ * poleSharpConstant := mul_nonneg hδ.le poleSharpConstant_pos.le
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hr).1], by linarith⟩

private theorem ccmFuResponseTerm_hasDerivAt (δ t : ℝ) (q : XiZeroCopy) :
    HasDerivAt (fun u => ccmFuResponseCoefficient δ q * expChar (zeroOrdinate q) u)
      (ccmFuResponseCoefficient δ q * expChar (zeroOrdinate q) t *
        ((zeroOrdinate q : ℂ) * I)) t := by
  have hd := ((((hasDerivAt_id t).const_mul (zeroOrdinate q)).ofReal_comp).mul_const I).cexp
  simpa only [expChar, mul_one, id_eq, mul_assoc] using
    hd.const_mul (ccmFuResponseCoefficient δ q)

private theorem ccmFuResponseTerm_deriv_norm_le {δ : ℝ} (hδ : 0 ≤ δ)
    (t : ℝ) (q : XiZeroCopy) :
    ‖ccmFuResponseCoefficient δ q * expChar (zeroOrdinate q) t *
      ((zeroOrdinate q : ℂ) * I)‖ ≤ ccmFuDeningerWeight δ q := by
  have hg : |zeroOrdinate q| ≤ ‖ccmFuResponsePole q‖ := by
    simpa [ccmFuResponsePole] using Complex.abs_im_le_norm (ccmFuResponsePole q)
  rw [ccmFuResponseCoefficient, norm_mul, norm_mul, norm_div, norm_expChar, mul_one,
    norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    Complex.norm_I, mul_one, abs_of_nonneg (ccmFuDeningerWeight_nonneg hδ q)]
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr (ccmFuResponsePole_ne_zero q))).mpr
    (mul_le_mul_of_nonneg_left hg (ccmFuDeningerWeight_nonneg hδ q))

theorem ccmFuComplexResponse_hasDerivAt (hRH : RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (ccmFuComplexResponse δ)
      (∑' q : XiZeroCopy,
        ccmFuResponseCoefficient δ q * expChar (zeroOrdinate q) t *
          ((zeroOrdinate q : ℂ) * I)) t := by
  change HasDerivAt (fun u => ∑' q, ccmFuResponseCoefficient δ q * expChar (zeroOrdinate q) u) _ t
  apply hasDerivAt_tsum_of_isPreconnected
    (g' := fun q u => ccmFuResponseCoefficient δ q * expChar (zeroOrdinate q) u *
      ((zeroOrdinate q : ℂ) * I)) (t := univ) (y₀ := t) (y := t)
    (summable_ccmFuDeningerWeight_of_pos hRH hδ) isOpen_univ isPreconnected_univ
  · intro q u _
    exact ccmFuResponseTerm_hasDerivAt δ u q
  · intro q u _
    exact ccmFuResponseTerm_deriv_norm_le hδ.le u q
  · exact mem_univ _
  · exact summable_expSeries (summable_norm_ccmFuResponseCoefficient hRH hδ) _ _
  · exact mem_univ _

theorem ccmFuRealResponse_hasDerivAt (hRH : RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (ccmFuRealResponse δ)
      (ccmFuDeningerRealPhase δ t - (1 / 2 : ℝ) * ccmFuRealResponse δ t) t := by
  have hc := ccmFuComplexResponse_hasDerivAt hRH hδ t
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hc
  have hs := summable_expSeries (summable_norm_ccmFuResponseCoefficient hRH hδ)
    zeroOrdinate t
  have hp : Summable (fun q : XiZeroCopy =>
      (ccmFuDeningerWeight δ q : ℂ) * expChar (zeroOrdinate q) t) := by
    apply (summable_ccmFuDeningerWeight_of_pos hRH hδ).of_norm_bounded
    intro q
    simp only [norm_mul, norm_expChar, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (ccmFuDeningerWeight_nonneg hδ.le q), le_refl]
  have heq : (∑' q : XiZeroCopy,
      ccmFuResponseCoefficient δ q * expChar (zeroOrdinate q) t *
        ((zeroOrdinate q : ℂ) * I)) =
      (∑' q : XiZeroCopy, (ccmFuDeningerWeight δ q : ℂ) * expChar (zeroOrdinate q) t) -
        (1 / 2 : ℂ) * ccmFuComplexResponse δ t := by
    have hterm : ∀ q : XiZeroCopy,
        ccmFuResponseCoefficient δ q * expChar (zeroOrdinate q) t *
          ((zeroOrdinate q : ℂ) * I) =
        (ccmFuDeningerWeight δ q : ℂ) * expChar (zeroOrdinate q) t -
          (1 / 2 : ℂ) * (ccmFuResponseCoefficient δ q * expChar (zeroOrdinate q) t) := by
      intro q
      rw [ccmFuResponseCoefficient]
      field_simp [ccmFuResponsePole_ne_zero q]
      simp only [ccmFuResponsePole]
      ring
    simp_rw [hterm]
    rw [hp.tsum_sub (hs.mul_left (1 / 2 : ℂ)), tsum_mul_left]
    rfl
  have hreal : (∑' q : XiZeroCopy,
      (ccmFuDeningerWeight δ q : ℂ) * expChar (zeroOrdinate q) t).re =
      ccmFuDeningerRealPhase δ t := by
    rw [Complex.re_tsum hp, ccmFuDeningerRealPhase]
    apply tsum_congr
    intro q
    simp [expChar, GaloisForLFunctions.bohrChar, zeroOrdinate]
  apply hr.congr_deriv
  change (∑' q : XiZeroCopy,
      ccmFuResponseCoefficient δ q * expChar (zeroOrdinate q) t *
        ((zeroOrdinate q : ℂ) * I)).re = _
  rw [heq, Complex.sub_re, hreal]
  simp [ccmFuRealResponse]

theorem integral_expChar_mul_ccmFuAutocorrelation {δ : ℝ} (hδ : 0 < δ)
    (q : XiZeroCopy) :
    (∫ x : ℝ, expChar (zeroOrdinate q) x *
      (ccmFuTranslatedAutocorrelation δ 0 x : ℂ)) = (ccmFuDeningerWeight δ q : ℂ) := by
  have hf : (∫ x : ℝ, expChar (zeroOrdinate q) x *
      (ccmFuTranslatedAutocorrelation δ 0 x : ℂ)) =
      𝓕 (fun x : ℝ => (ccmFuTranslatedAutocorrelation δ 0 x : ℂ))
        (-zeroOrdinate q / (2 * Real.pi)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with x
    rw [smul_eq_mul, expChar]
    congr 2
    field_simp [Real.pi_ne_zero]
  rw [hf]
  change 𝓕 (fun x : ℝ => (ccmFuAutocorrelationProfile ((x - 0) / δ) : ℂ)) _ = _
  rw [fourierIntegral_comp_div_sub (fun x : ℝ => (ccmFuAutocorrelationProfile x : ℂ)) 0 δ hδ,
    fourier_ccmFuAutocorrelationProfile]
  simp only [neg_zero, mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
    one_smul, Complex.real_smul, ccmFuDeningerWeight, zeroOrdinate]
  push_cast
  congr 2
  ring

private theorem ccmFuRealPhaseTerm_eq (δ t : ℝ) (q : XiZeroCopy) :
    ccmFuDeningerWeight δ q *
      (GaloisForLFunctions.bohrChar (-(q.1 : ℂ).im) t).re =
      ccmFuDeningerWeight δ q * (expChar (zeroOrdinate q) t).re := by
  simp [GaloisForLFunctions.bohrChar, expChar, zeroOrdinate]

theorem integral_ccmFuRealPhase_mul_autocorrelation (hRH : RiemannHypothesis)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    (∫ x : ℝ, ccmFuDeningerRealPhase ε x * ccmFuTranslatedAutocorrelation δ 0 x) =
      ∑' q : XiZeroCopy, ccmFuDeningerWeight ε q * ccmFuDeningerWeight δ q := by
  let φ := ccmFuTranslatedAutocorrelation δ 0
  let F : XiZeroCopy → ℝ → ℝ := fun q x =>
    ccmFuDeningerWeight ε q * (expChar (zeroOrdinate q) x).re * φ x
  have hφ := integrable_ccmFuTranslatedAutocorrelation (t := 0) hδ
  have hc : ∀ q, Continuous (F q) := by
    intro q
    exact (continuous_const.mul (Complex.continuous_re.comp (continuous_expChar _))).mul
      (continuous_ccmFuTranslatedAutocorrelation δ 0)
  have hFi : ∀ q, Integrable (F q) := by
    intro q
    exact (hc q).integrable_of_hasCompactSupport
      (hasCompactSupport_ccmFuTranslatedAutocorrelation hδ).mul_left
  have hb : ∀ q, (∫ x : ℝ, ‖F q x‖) ≤
      ccmFuDeningerWeight ε q * ∫ x : ℝ, |φ x| := by
    intro q
    rw [← integral_const_mul]
    apply integral_mono (hFi q).norm (hφ.norm.const_mul _)
    intro x
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (ccmFuDeningerWeight_nonneg hε.le q)]
    have hp : |(expChar (zeroOrdinate q) x).re| ≤ 1 :=
      (Complex.abs_re_le_norm _).trans_eq (norm_expChar _ _)
    change ccmFuDeningerWeight ε q * |(expChar (zeroOrdinate q) x).re| * |φ x| ≤
      ccmFuDeningerWeight ε q * |φ x|
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (ccmFuDeningerWeight_nonneg hε.le q) hp) (abs_nonneg _)
  have hsum : Summable (fun q => ∫ x : ℝ, ‖F q x‖) := by
    apply ((summable_ccmFuDeningerWeight_of_pos hRH hε).mul_right
      (∫ x : ℝ, |φ x|)).of_norm_bounded
    intro q
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
    exact hb q
  have hterm : ∀ q, (∫ x : ℝ, F q x) =
      ccmFuDeningerWeight ε q * ccmFuDeningerWeight δ q := by
    intro q
    have hci : Integrable (fun x : ℝ =>
        expChar (zeroOrdinate q) x * (φ x : ℂ)) := by
      apply ((continuous_expChar _).mul
        (Complex.continuous_ofReal.comp
          (continuous_ccmFuTranslatedAutocorrelation δ 0))).integrable_of_hasCompactSupport
      exact ((hasCompactSupport_ccmFuTranslatedAutocorrelation hδ).comp_left
        (g := fun r : ℝ => (r : ℂ)) rfl).mul_left
    have hi := congrArg Complex.re (integral_expChar_mul_ccmFuAutocorrelation hδ q)
    have hi' := (integral_re hci).trans hi
    simp only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] at hi'
    dsimp only [F]
    simp_rw [mul_assoc]
    rw [integral_const_mul, hi']
  rw [← tsum_congr hterm, integral_tsum_of_summable_integral_norm hFi hsum]
  apply integral_congr_ae
  filter_upwards with x
  rw [ccmFuDeningerRealPhase]
  simp_rw [ccmFuRealPhaseTerm_eq]
  exact (tsum_mul_right : (∑' q, ccmFuDeningerWeight ε q *
    (expChar (zeroOrdinate q) x).re * φ x) = _).symm

theorem continuous_ccmFuDeningerRealPhase (hRH : RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) : Continuous (ccmFuDeningerRealPhase δ) := by
  refine continuous_tsum (fun q => continuous_const.mul
    (Complex.continuous_re.comp (GaloisForLFunctions.continuous_bohrChar _)))
    (summable_ccmFuDeningerWeight_of_pos hRH hδ) ?_
  intro q t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ccmFuDeningerWeight_nonneg hδ.le q)]
  have hp := Complex.abs_re_le_norm (GaloisForLFunctions.bohrChar (-(q.1 : ℂ).im) t)
  rw [GaloisForLFunctions.norm_bohrChar] at hp
  exact mul_le_of_le_one_right (ccmFuDeningerWeight_nonneg hδ.le q) hp

theorem ccmFuMixedMass_eq_response_pairing (hRH : RiemannHypothesis)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    (∑' q : XiZeroCopy, ccmFuDeningerWeight ε q * ccmFuDeningerWeight δ q) =
      (1 / 2 : ℝ) * (∫ x : ℝ,
        ccmFuRealResponse ε x * ccmFuTranslatedAutocorrelation δ 0 x) -
      ∫ x : ℝ, ccmFuRealResponse ε x * ccmFuTranslatedAutocorrelationDeriv δ 0 x := by
  let Q := ccmFuRealResponse ε
  let P := ccmFuDeningerRealPhase ε
  let φ := ccmFuTranslatedAutocorrelation δ 0
  let φ' := ccmFuTranslatedAutocorrelationDeriv δ 0
  have hQ : Continuous Q := continuous_iff_continuousAt.mpr
    (fun x => (ccmFuRealResponse_hasDerivAt hRH hε x).continuousAt)
  have hP : Continuous P := continuous_ccmFuDeningerRealPhase hRH hε
  have hφ : Continuous φ := continuous_ccmFuTranslatedAutocorrelation δ 0
  have hφ' : Continuous φ' := continuous_ccmFuTranslatedAutocorrelationDeriv δ 0
  have hcφ : HasCompactSupport φ := hasCompactSupport_ccmFuTranslatedAutocorrelation hδ
  have hcφ' : HasCompactSupport φ' := hasCompactSupport_ccmFuTranslatedAutocorrelationDeriv hδ
  have hQφ : Integrable (fun x => Q x * φ x) :=
    (hQ.mul hφ).integrable_of_hasCompactSupport hcφ.mul_left
  have hQφ' : Integrable (fun x => Q x * φ' x) :=
    (hQ.mul hφ').integrable_of_hasCompactSupport hcφ'.mul_left
  have hPφ : Integrable (fun x => P x * φ x) :=
    (hP.mul hφ).integrable_of_hasCompactSupport hcφ.mul_left
  have hdφ : Integrable (fun x => (P x - (1 / 2 : ℝ) * Q x) * φ x) :=
    ((hP.sub (continuous_const.mul hQ)).mul hφ).integrable_of_hasCompactSupport hcφ.mul_left
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := Q) (v := φ) (u' := fun x => P x - (1 / 2 : ℝ) * Q x) (v' := φ')
    (fun x _ => ccmFuRealResponse_hasDerivAt hRH hε x)
    (fun x _ => hasDerivAt_ccmFuTranslatedAutocorrelation x) hQφ' hdφ hQφ
  have hdecomp : (∫ x : ℝ, (P x - (1 / 2 : ℝ) * Q x) * φ x) =
      (∫ x : ℝ, P x * φ x) - (1 / 2 : ℝ) * ∫ x : ℝ, Q x * φ x := by
    simp_rw [sub_mul, mul_assoc]
    rw [integral_sub hPφ (hQφ.const_mul _), integral_const_mul]
  rw [hdecomp] at hibp
  rw [← integral_ccmFuRealPhase_mul_autocorrelation hRH hε hδ]
  change (∫ x : ℝ, P x * φ x) = _
  linarith

theorem ccmFuMixedMass_le_of_response_bound (hRH : RiemannHypothesis)
    {ε δ B : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hB : ∀ x : ℝ, |ccmFuRealResponse ε x| ≤ B * ε) :
    (∑' q : XiZeroCopy, ccmFuDeningerWeight ε q * ccmFuDeningerWeight δ q) ≤
      B * ε * ((δ / 2) * (∫ x : ℝ, |ccmFuAutocorrelationProfile x|) +
        ∫ x : ℝ, |deriv ccmFuAutocorrelationProfile x|) := by
  have hQ : Continuous (ccmFuRealResponse ε) := continuous_iff_continuousAt.mpr
    (fun x => (ccmFuRealResponse_hasDerivAt hRH hε x).continuousAt)
  have hb : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      |∫ x : ℝ, ccmFuRealResponse ε x * f x| ≤ B * ε * ∫ x : ℝ, |f x| := by
    intro f hf hfc
    have hi : Integrable (fun x => ccmFuRealResponse ε x * f x) :=
      (hQ.mul hf).integrable_of_hasCompactSupport hfc.mul_left
    calc
      _ ≤ ∫ x : ℝ, |ccmFuRealResponse ε x * f x| := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun x : ℝ => ccmFuRealResponse ε x * f x)
      _ ≤ ∫ x : ℝ, (B * ε) * |f x| := by
        apply integral_mono hi.norm ((hf.integrable_of_hasCompactSupport hfc).norm.const_mul _)
        intro x
        simp only [Real.norm_eq_abs]
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
      _ = _ := integral_const_mul _ _
  have hφ := hb _ (continuous_ccmFuTranslatedAutocorrelation δ 0)
    (hasCompactSupport_ccmFuTranslatedAutocorrelation hδ)
  have hφ' := hb _ (continuous_ccmFuTranslatedAutocorrelationDeriv δ 0)
    (hasCompactSupport_ccmFuTranslatedAutocorrelationDeriv hδ)
  rw [integral_abs_ccmFuTranslatedAutocorrelation hδ] at hφ
  rw [integral_abs_ccmFuTranslatedAutocorrelationDeriv hδ] at hφ'
  rw [ccmFuMixedMass_eq_response_pairing hRH hε hδ]
  linarith [(abs_le.mp hφ).2, (abs_le.mp hφ').1]

theorem ccmFuDeningerMass_le_of_uniform_response_bound (hRH : RiemannHypothesis)
    {B : ℝ} (hB : ∀ ε : ℝ, 0 < ε → ∀ x : ℝ, |ccmFuRealResponse ε x| ≤ B * ε)
    {δ : ℝ} (hδ : 0 < δ) :
    ccmFuDeningerMass δ ≤
      B * ((δ / 2) * (∫ x : ℝ, |ccmFuAutocorrelationProfile x|) +
        ∫ x : ℝ, |deriv ccmFuAutocorrelationProfile x|) := by
  classical
  let K := (δ / 2) * (∫ x : ℝ, |ccmFuAutocorrelationProfile x|) +
    ∫ x : ℝ, |deriv ccmFuAutocorrelationProfile x|
  have hhead : ∀ F : Finset XiZeroCopy, ∑ q ∈ F, ccmFuDeningerWeight δ q ≤ B * K := by
    intro F
    let f : ℝ → ℝ := fun ε => ∑ q ∈ F, ccmFuDeningerWeight δ q *
      ‖ccmFuBaseFourier (-ε * (q.1 : ℂ).im / (2 * Real.pi))‖ ^ 2
    have hc : Continuous f := by
      apply continuous_finsetSum
      intro q _
      exact continuous_const.mul
        ((continuous_ccmFuBaseFourier.comp (by fun_prop)).norm.pow 2)
    have hzero : f 0 = ∑ q ∈ F, ccmFuDeningerWeight δ q := by
      simp [f, ccmFuBaseFourier_zero]
    have hl : Tendsto f (nhdsWithin 0 (Ioi 0)) (nhds (∑ q ∈ F, ccmFuDeningerWeight δ q)) := by
      rw [← hzero]
      exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto hl
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : 0 < ε := hε
    have hmix := ccmFuMixedMass_le_of_response_bound hRH hε0 hδ (hB ε hε0)
    have hs : Summable (fun q : XiZeroCopy =>
        ccmFuDeningerWeight ε q * ccmFuDeningerWeight δ q) := by
      apply ((summable_ccmFuDeningerWeight_of_pos hRH hε0).mul_right δ).of_norm_bounded
      intro q
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (ccmFuDeningerWeight_nonneg hε0.le q) (ccmFuDeningerWeight_nonneg hδ.le q))]
      exact mul_le_mul_of_nonneg_left (ccmFuDeningerWeight_le_scale hδ.le q)
        (ccmFuDeningerWeight_nonneg hε0.le q)
    have hpart := hs.sum_le_tsum F (fun q _ =>
      mul_nonneg (ccmFuDeningerWeight_nonneg hε0.le q) (ccmFuDeningerWeight_nonneg hδ.le q))
    have heq : ∑ q ∈ F, ccmFuDeningerWeight ε q * ccmFuDeningerWeight δ q = ε * f ε := by
      dsimp only [f]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      change ε * ‖ccmFuBaseFourier (-ε * (q.1 : ℂ).im / (2 * Real.pi))‖ ^ 2 *
        ccmFuDeningerWeight δ q = _
      ring
    rw [heq] at hpart
    apply (mul_le_mul_iff_right₀ hε0).mp
    calc
      ε * f ε ≤ ∑' q, ccmFuDeningerWeight ε q * ccmFuDeningerWeight δ q := hpart
      _ ≤ ε * (B * K) := by simpa only [K, mul_assoc, mul_comm, mul_left_comm] using hmix
  exact le_of_tendsto' (summable_ccmFuDeningerWeight_of_pos hRH hδ).hasSum hhead

theorem not_uniform_ccmFuResponse_scale_bound (hRH : RiemannHypothesis) :
    ¬ ∃ B : ℝ, 0 ≤ B ∧ ∀ δ : ℝ, 0 < δ → ∀ x : ℝ,
      |ccmFuRealResponse δ x| ≤ B * δ := by
  rintro ⟨B, hB0, hB⟩
  let I₀ := ∫ x : ℝ, |ccmFuAutocorrelationProfile x|
  let I₁ := ∫ x : ℝ, |deriv ccmFuAutocorrelationProfile x|
  obtain ⟨δ, t, hδ, ht, hδ1, _, hlarge⟩ :=
    deningerSpectralSum_ccmFu_cofinally_unbounded_smallScale hRH (B * (I₀ / 2 + I₁)) 0
  rw [deningerSpectralSum_ccmFuDeningerTest_re_eq_realPhase hRH hδ ht] at hlarge
  have hphase : ccmFuDeningerRealPhase δ t ≤ ccmFuDeningerMass δ := by
    apply (summable_ccmFuDeningerRealPhase_term hRH hδ t).tsum_le_tsum _
      (summable_ccmFuDeningerWeight_of_pos hRH hδ)
    intro q
    have hp := Complex.abs_re_le_norm (GaloisForLFunctions.bohrChar (-(q.1 : ℂ).im) t)
    rw [GaloisForLFunctions.norm_bohrChar] at hp
    exact mul_le_of_le_one_right (ccmFuDeningerWeight_nonneg hδ.le q)
      ((le_abs_self _).trans hp)
  have hm := ccmFuDeningerMass_le_of_uniform_response_bound hRH hB hδ
  have hI : 0 ≤ I₀ := integral_nonneg (fun x => abs_nonneg _)
  have hK : δ / 2 * I₀ + I₁ ≤ I₀ / 2 + I₁ := by nlinarith
  have hbound := mul_le_mul_of_nonneg_left hK hB0
  linarith

theorem ccmFuRealResponse_positive_escape (hRH : RiemannHypothesis) (C L : ℝ) :
    ∃ δ t : ℝ, 0 < δ ∧ L ≤ t ∧ C * δ < ccmFuRealResponse δ t := by
  by_contra! h
  apply not_uniform_ccmFuResponse_scale_bound hRH
  refine ⟨|C| + poleSharpConstant, add_nonneg (abs_nonneg _) poleSharpConstant_pos.le, ?_⟩
  intro δ hδ x
  have hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop,
      ccmFuRealResponse δ t ≤ C * δ + ε := by
    intro ε hε
    filter_upwards [eventually_ge_atTop L] with t ht
    exact (h δ t hδ ht).trans (by linarith)
  have hb := abs_ccmFuRealResponse_le_of_eventual_upper hRH hδ hu x
  have hc := mul_le_mul_of_nonneg_right (le_abs_self C) hδ.le
  nlinarith

end
end RHTower
