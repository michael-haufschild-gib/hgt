import GaloisForLFunctions.RHTower.SelbergThetaSourcePhase
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaCompactDivisorEigenmode
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCompletedDividedEnergy

/-!
# Exact positive variance of the actual theta source mode

At every actual Xi divisor, the ratio of the two-ended mode to the complete theta source is
bounded on the real line. This supplies integrability and vanishing endpoints for its weighted
energies and currents after every real tilt in `(-1,1)`.

The weighted logarithmic-source current equals twice the shifted transverse parameter times
an explicit strictly positive squared deviation. The same deviation gives the exact energy
above its source-mass term. At the required gauge tilt this yields the weighted source balance
with a finite, strictly positive energy. No native spectral occurrence is asserted.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate
namespace RHTower.SelbergThetaSourceVariance
noncomputable section
open SelbergThetaSourcePhase HedenmalmThetaSource HedenmalmQuantile HedenmalmPrimeTranslation

private theorem strip (q : XiZeroCopy) : |(xiSpectralPoint q).im| < 1 := by
  have h := xiSpectralPoint_im_mem_openHalf q
  rw [abs_lt]
  constructor <;> linarith

private theorem source_zero (q : XiZeroCopy) : xiC thetaSource (xiSpectralPoint q) = 0 := by
  rw [xiC_thetaSource (strip q)]
  exact XiC_xiSpectralPoint_eq_zero q

private theorem tail_mode_bound {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) {x : ℝ} (hx : 1 ≤ x) :
    ‖hedenmalmCausalVolterra z x‖ ≤
      (thetaEnvelopeUpper / thetaEnvelopeLower) * thetaCuspFullSource x := by
  have hu := norm_sourceModeU_le_thetaEnvelope_right hz hzero hx
  rw [sourceModeU_thetaSource_eq_hedenmalmCausalVolterra] at hu
  have hp := thetaCuspFullSource_ge_envelope (by linarith : 0 < x)
  calc
    ‖hedenmalmCausalVolterra z x‖ ≤ thetaEnvelopeUpper * thetaEnvelope x := hu
    _ = (thetaEnvelopeUpper / thetaEnvelopeLower) * (thetaEnvelopeLower * thetaEnvelope x) := by
      field_simp [thetaEnvelopeLower_pos.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (div_pos thetaEnvelopeUpper_pos thetaEnvelopeLower_pos).le

private theorem mode_bound_tail (q : XiZeroCopy) {x : ℝ} (hx : 1 ≤ |x|) :
    ‖mode q x‖ ≤ (thetaEnvelopeUpper / thetaEnvelopeLower) * thetaCuspFullSource x := by
  rcases le_or_gt 0 x with hp | hn
  · exact tail_mode_bound (strip q) (source_zero q) (by simpa [abs_of_nonneg hp] using hx)
  · have hs : |(-(xiSpectralPoint q)).im| < 1 := by simpa using strip q
    have hz : xiC thetaSource (-(xiSpectralPoint q)) = 0 := by
      rw [xiC_thetaSource hs, XiC_even, XiC_xiSpectralPoint_eq_zero]
    have hb := tail_mode_bound hs hz (x := -x) (by simpa [abs_of_neg hn] using hx)
    have he := sourceModeU_neg thetaSource thetaSource_even
      (hasShiftedTail_thetaSource (strip q)) (source_zero q) x
    simp_rw [sourceModeU_thetaSource_eq_hedenmalmCausalVolterra] at he
    rw [he, norm_neg, thetaCuspFullSource_neg] at hb
    exact hb

/-- Ratio of the literal actual zero mode to the strictly positive theta source. -/
def sourceRatio (q : XiZeroCopy) (x : ℝ) : ℂ := mode q x / (thetaCuspFullSource x : ℂ)

private theorem source_ne_zero (x : ℝ) : (thetaCuspFullSource x : ℂ) ≠ 0 := by
  exact_mod_cast (thetaCuspFullSource_pos_all x).ne'

/-- The actual source ratio is continuous throughout the real line. -/
theorem continuous_sourceRatio (q : XiZeroCopy) : Continuous (sourceRatio q) := by
  exact (continuous_iff_continuousAt.mpr fun x => (hasDerivAt_mode q x).continuousAt).div
    (Complex.continuous_ofReal.comp thetaCuspSchwartzReal.continuous) source_ne_zero

/-- The complete theta tail and compact core give a global bound on the actual source ratio. -/
theorem sourceRatio_bounded (q : XiZeroCopy) : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖sourceRatio q x‖ ≤ C := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) (continuous_sourceRatio q).continuousOn
  let K := thetaEnvelopeUpper / thetaEnvelopeLower
  refine ⟨max 1 (max K M), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x
  by_cases hx : 1 ≤ |x|
  · have h := mode_bound_tail q hx
    have hnorm : ‖sourceRatio q x‖ = ‖mode q x‖ / thetaCuspFullSource x := by
      rw [sourceRatio, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (thetaCuspFullSource_pos_all x)]
    rw [hnorm]
    exact (div_le_iff₀ (thetaCuspFullSource_pos_all x)).mpr h |>.trans
      ((le_max_left K M).trans (le_max_right 1 (max K M)))
  · have hm : x ∈ Icc (-1 : ℝ) 1 := by
      have ha := abs_lt.mp (lt_of_not_ge hx)
      exact ⟨ha.1.le, ha.2.le⟩
    exact (hM x hm).trans ((le_max_right K M).trans (le_max_right 1 (max K M)))

/-- Real exponential tilt of the complete theta source. -/
def tiltedSource (a x : ℝ) : ℝ := Real.exp (a*x) * thetaCuspFullSource x

/-- Literal mode energy in the reciprocal theta density, with a real exponential tilt. -/
def weightedEnergy (q : XiZeroCopy) (a x : ℝ) : ℝ :=
  tiltedSource a x * ‖sourceRatio q x‖ ^ (2 : ℕ)

/-- The actual two-ended mode with the same exponential tilt. -/
def weightedMode (q : XiZeroCopy) (a x : ℝ) : ℂ :=
  (Real.exp (a*x) : ℂ) * mode q x

/-- Exact source-ratio factorization of the tilted mode. -/
theorem weightedMode_eq (q : XiZeroCopy) (a x : ℝ) :
    weightedMode q a x = (tiltedSource a x : ℂ) * sourceRatio q x := by
  unfold weightedMode tiltedSource sourceRatio
  push_cast
  field_simp [source_ne_zero x]

private theorem tiltedSource_integrable {a : ℝ} (ha : |a| < 1) : Integrable (tiltedSource a) :=
  (thetaCuspTiltedSchwartzReal a ha).integrable

private theorem tiltedSource_continuous (a : ℝ) : Continuous (tiltedSource a) := by
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    thetaCuspSchwartzReal.continuous

private theorem tiltedSource_pos (a x : ℝ) : 0 < tiltedSource a x :=
  mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all x)

private theorem weightedMode_integrable (q : XiZeroCopy) {a : ℝ} (ha : |a| < 1) :
    Integrable (weightedMode q a) := by
  obtain ⟨C, _, hC⟩ := sourceRatio_bounded q
  have h := (tiltedSource_integrable ha).ofReal.mul_bdd
    (continuous_sourceRatio q).aestronglyMeasurable (Eventually.of_forall hC)
  exact h.congr (Eventually.of_forall fun x => (weightedMode_eq q a x).symm)

private theorem weightedEnergy_integrable (q : XiZeroCopy) {a : ℝ} (ha : |a| < 1) :
    Integrable (weightedEnergy q a) := by
  obtain ⟨C, hCp, hC⟩ := sourceRatio_bounded q
  apply (tiltedSource_integrable ha).mul_bdd
    ((continuous_sourceRatio q).norm.pow 2).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2

private theorem weightedMode_tendsto (q : XiZeroCopy) {a : ℝ} (ha : |a| < 1) :
    Tendsto (weightedMode q a) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C, hCp, hC⟩ := sourceRatio_bounded q
  apply squeeze_zero_norm (a := fun x => C * ‖tiltedSource a x‖)
  · intro x
    rw [weightedMode_eq, norm_mul, Complex.norm_real]
    nlinarith [hC x, norm_nonneg (tiltedSource a x)]
  · simpa [tiltedSource, thetaCuspTiltedSource] using (thetaCuspTiltedSchwartzReal a ha).tendsto_cocompact.norm.const_mul C

private theorem weightedEnergy_tendsto (q : XiZeroCopy) {a : ℝ} (ha : |a| < 1) :
    Tendsto (weightedEnergy q a) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C, hCp, hC⟩ := sourceRatio_bounded q
  apply squeeze_zero_norm (a := fun x => C^(2 : ℕ) * ‖tiltedSource a x‖)
  · intro x
    rw [weightedEnergy, norm_mul, Real.norm_eq_abs, abs_of_pos (tiltedSource_pos a x),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hp := pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
    nlinarith [tiltedSource_pos a x]
  · simpa [tiltedSource, thetaCuspTiltedSource] using (thetaCuspTiltedSchwartzReal a ha).tendsto_cocompact.norm.const_mul (C^(2 : ℕ))


private def Q (x : ℝ) : ℝ := deriv thetaCuspLogSource x

private theorem hasDerivAt_source (x : ℝ) :
    HasDerivAt thetaCuspFullSource (Q x * thetaCuspFullSource x) x := by
  have h : HasDerivAt thetaCuspFullSource (deriv thetaCuspFullSource x) x :=
    thetaCuspSchwartzReal.hasDerivAt x
  convert h using 1
  have hq := (hasDerivAt_thetaCuspLogSource x).deriv
  simp only [iteratedDeriv_one] at hq
  dsimp [Q]
  rw [hq]
  field_simp [(thetaCuspFullSource_pos_all x).ne']

private theorem hasDerivAt_ratio (q : XiZeroCopy) (x : ℝ) :
    HasDerivAt (sourceRatio q)
      ((-I*xiSpectralPoint q - (Q x : ℂ))*sourceRatio q x-I) x := by
  have h := (hasDerivAt_mode q x).div (hasDerivAt_source x).ofReal_comp (source_ne_zero x)
  refine h.congr_deriv ?_
  unfold sourceRatio
  push_cast
  field_simp [source_ne_zero x]
  ring

private theorem hasDerivAt_tiltedSource (a x : ℝ) :
    HasDerivAt (tiltedSource a) ((a+Q x)*tiltedSource a x) x := by
  have h := (((hasDerivAt_id x).const_mul a).exp).mul (hasDerivAt_source x)
  simpa [tiltedSource] using! h.congr_deriv (by simp only [id_eq]; ring)

private theorem hasDerivAt_ratio_norm (q : XiZeroCopy) (x : ℝ) :
    HasDerivAt (fun t => ‖sourceRatio q t‖^(2 : ℕ))
      (2*((xiSpectralPoint q).im-Q x)*‖sourceRatio q x‖^(2 : ℕ) - 2*(sourceRatio q x).im) x := by
  have h := (hasDerivAt_ratio q x).norm_sq
  refine h.congr_deriv ?_
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
  simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

private def sourceMomentDensity (q : XiZeroCopy) (a x : ℝ) : ℝ :=
  deriv (tiltedSource a) x * ‖sourceRatio q x‖^(2 : ℕ)

private theorem sourceMoment_integrable (q : XiZeroCopy) {a : ℝ} (ha : |a| < 1) :
    Integrable (sourceMomentDensity q a) := by
  obtain ⟨C, _, hC⟩ := sourceRatio_bounded q
  have hf : Integrable (deriv (tiltedSource a)) :=
    (SchwartzMap.derivCLM ℝ ℝ (thetaCuspTiltedSchwartzReal a ha)).integrable
  apply hf.mul_bdd ((continuous_sourceRatio q).norm.pow 2).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2

private theorem hasDerivAt_weightedEnergy (q : XiZeroCopy) (a x : ℝ) :
    HasDerivAt (weightedEnergy q a)
      (2*(a+(xiSpectralPoint q).im)*weightedEnergy q a x - sourceMomentDensity q a x
        -2*(weightedMode q a x).im) x := by
  have h := (hasDerivAt_tiltedSource a x).mul (hasDerivAt_ratio_norm q x)
  refine h.congr_deriv ?_
  rw [weightedMode_eq]
  unfold weightedEnergy sourceMomentDensity
  rw [(hasDerivAt_tiltedSource a x).deriv]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  ring

private def shift (q : XiZeroCopy) (a : ℝ) : ℂ := xiSpectralPoint q + I*(a:ℂ)

private theorem shift_ne_zero (q : XiZeroCopy) (a : ℝ) : shift q a ≠ 0 := by
  have hb : (xiSpectralPoint q).re ≠ 0 := by
    simpa [xiSpectralPoint, Complex.mul_re, Complex.mul_im] using xi_divisor_support_im_ne_zero q.1
  intro he
  apply hb
  have hr := congrArg Complex.re he
  simpa [shift, Complex.mul_re] using hr

private theorem hasDerivAt_weightedMode (q : XiZeroCopy) (a x : ℝ) :
    HasDerivAt (weightedMode q a)
      (-I*shift q a*weightedMode q a x - I*(tiltedSource a x:ℂ)) x := by
  have h := ((((hasDerivAt_id x).const_mul a).exp).ofReal_comp).mul (hasDerivAt_mode q x)
  refine h.congr_deriv ?_
  unfold weightedMode tiltedSource shift
  simp only [id_eq]
  push_cast
  ring_nf
  simp only [I_sq]
  ring

private theorem integral_weightedMode (q : XiZeroCopy) {a : ℝ} (ha : |a| < 1) :
    (∫ x, weightedMode q a x) = -(∫ x, tiltedSource a x : ℝ) / shift q a := by
  have hu := weightedMode_integrable q ha
  have hf := tiltedSource_integrable ha
  have hdRaw := MeasureTheory.integral_of_hasDerivAt_of_tendsto
    (hasDerivAt_weightedMode q a)
    ((hu.const_mul (-I*shift q a)).sub (hf.ofReal.const_mul I))
    ((weightedMode_tendsto q ha).mono_left atBot_le_cocompact)
    ((weightedMode_tendsto q ha).mono_left atTop_le_cocompact)
  have hd : (∫ x, -I*shift q a*weightedMode q a x-I*(tiltedSource a x:ℂ)) = 0 := by
    simpa using! hdRaw
  have heq : (∫ x, -I*shift q a*weightedMode q a x-I*(tiltedSource a x:ℂ)) =
      (-I*shift q a)*(∫ x, weightedMode q a x)-I*(∫ x, tiltedSource a x : ℝ) := by
    calc
      _ = (∫ x, -I*shift q a*weightedMode q a x) - (∫ x, I*(tiltedSource a x:ℂ)) := by
        simpa using! integral_sub (hu.const_mul (-I*shift q a)) (hf.ofReal.const_mul I)
      _ = _ := by rw [integral_const_mul, integral_const_mul, integral_complex_ofReal]
  rw [heq] at hd
  apply (eq_div_iff (shift_ne_zero q a)).2
  linear_combination (norm := ring_nf) I * hd
  simp only [I_sq]
  ring

private theorem integral_sourceMoment (q : XiZeroCopy) {a : ℝ} (ha : |a| < 1) :
    (∫ x, sourceMomentDensity q a x) =
      2*(a+(xiSpectralPoint q).im)*(∫ x, weightedEnergy q a x) -
        2*(∫ x, weightedMode q a x).im := by
  have hw := weightedEnergy_integrable q ha
  have hq := sourceMoment_integrable q ha
  have hu := weightedMode_integrable q ha
  have hdRaw := MeasureTheory.integral_of_hasDerivAt_of_tendsto
    (hasDerivAt_weightedEnergy q a)
    (((hw.const_mul _).sub hq).sub (hu.im.const_mul 2))
    ((weightedEnergy_tendsto q ha).mono_left atBot_le_cocompact)
    ((weightedEnergy_tendsto q ha).mono_left atTop_le_cocompact)
  have hd : (∫ x, 2*(a+(xiSpectralPoint q).im)*weightedEnergy q a x -
      sourceMomentDensity q a x-2*(weightedMode q a x).im) = 0 := by
    simpa using! hdRaw
  have heq : (∫ x, 2*(a+(xiSpectralPoint q).im)*weightedEnergy q a x -
      sourceMomentDensity q a x-2*(weightedMode q a x).im) =
      2*(a+(xiSpectralPoint q).im)*(∫ x, weightedEnergy q a x) -
        (∫ x, sourceMomentDensity q a x) - 2*(∫ x, (weightedMode q a x).im) := by
    calc
      _ = (∫ x, 2*(a+(xiSpectralPoint q).im)*weightedEnergy q a x - sourceMomentDensity q a x) -
          (∫ x, 2*(weightedMode q a x).im) := by
        simpa using! integral_sub ((hw.const_mul (2*(a+(xiSpectralPoint q).im))).sub hq) (hu.im.const_mul 2)
      _ = _ := by
        have hs : (∫ x, 2*(a+(xiSpectralPoint q).im)*weightedEnergy q a x - sourceMomentDensity q a x) =
            (∫ x, 2*(a+(xiSpectralPoint q).im)*weightedEnergy q a x) - (∫ x, sourceMomentDensity q a x) := by
          simpa using! integral_sub (hw.const_mul (2*(a+(xiSpectralPoint q).im))) hq
        rw [hs, integral_const_mul, integral_const_mul]
  rw [heq] at hd
  have hi := integral_im (𝕜 := ℂ) hu
  change (∫ x, (weightedMode q a x).im) = (∫ x, weightedMode q a x).im at hi
  rw [hi] at hd
  linarith


private def varianceDensity (q : XiZeroCopy) (a x : ℝ) : ℝ :=
  tiltedSource a x * ‖sourceRatio q x + (shift q a)⁻¹‖^(2 : ℕ)

private theorem variance_integrable (q : XiZeroCopy) {a : ℝ} (ha : |a| < 1) :
    Integrable (varianceDensity q a) := by
  obtain ⟨C, hCp, hC⟩ := sourceRatio_bounded q
  have hbound : ∀ x : ℝ, ‖‖sourceRatio q x + (shift q a)⁻¹‖^(2 : ℕ)‖ ≤
      (C+‖(shift q a)⁻¹‖)^(2 : ℕ) := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hs : ‖sourceRatio q x+(shift q a)⁻¹‖ ≤ C+‖(shift q a)⁻¹‖ :=
      (norm_add_le (sourceRatio q x) ((shift q a)⁻¹)).trans (by linarith [hC x])
    exact pow_le_pow_left₀ (norm_nonneg _) hs 2
  exact (tiltedSource_integrable ha).mul_bdd
    (((continuous_sourceRatio q).add continuous_const).norm.pow 2).aestronglyMeasurable
    (Eventually.of_forall hbound)

private theorem variance_expand (q : XiZeroCopy) (a x : ℝ) :
    varianceDensity q a x = weightedEnergy q a x +
      2*(weightedMode q a x * conj ((shift q a)⁻¹)).re +
        tiltedSource a x*Complex.normSq ((shift q a)⁻¹) := by
  rw [varianceDensity, ← Complex.normSq_eq_norm_sq, Complex.normSq_add, weightedMode_eq]
  unfold weightedEnergy
  rw [Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  ring

private theorem integral_variance (q : XiZeroCopy) {a : ℝ} (ha : |a| < 1) :
    (∫ x, varianceDensity q a x) = (∫ x, weightedEnergy q a x) -
      (∫ x, tiltedSource a x)*Complex.normSq ((shift q a)⁻¹) := by
  have hu := weightedMode_integrable q ha
  have hw := weightedEnergy_integrable q ha
  have hf := tiltedSource_integrable ha
  have hr := (hu.mul_const (conj ((shift q a)⁻¹))).re
  simp_rw [variance_expand]
  have hs1 : (∫ x, weightedEnergy q a x + 2*(weightedMode q a x * conj ((shift q a)⁻¹)).re +
      tiltedSource a x*Complex.normSq ((shift q a)⁻¹)) =
      (∫ x, weightedEnergy q a x + 2*(weightedMode q a x * conj ((shift q a)⁻¹)).re) +
        (∫ x, tiltedSource a x*Complex.normSq ((shift q a)⁻¹)) := by
    simpa using! integral_add (hw.add (hr.const_mul 2)) (hf.mul_const (Complex.normSq ((shift q a)⁻¹)))
  have hs2 : (∫ x, weightedEnergy q a x + 2*(weightedMode q a x * conj ((shift q a)⁻¹)).re) =
      (∫ x, weightedEnergy q a x) + (∫ x, 2*(weightedMode q a x * conj ((shift q a)⁻¹)).re) := by
    simpa using! integral_add hw (hr.const_mul 2)
  rw [hs1, hs2, integral_const_mul, integral_mul_const]
  have hi := integral_re (𝕜 := ℂ) (hu.mul_const (conj ((shift q a)⁻¹)))
  change (∫ x, (weightedMode q a x*conj ((shift q a)⁻¹)).re) =
    (∫ x, weightedMode q a x*conj ((shift q a)⁻¹)).re at hi
  rw [hi, integral_mul_const, integral_weightedMode q ha, div_eq_mul_inv]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
    neg_zero, zero_mul, sub_zero]
  ring

private theorem source_variance_identity (q : XiZeroCopy) {a : ℝ} (ha : |a| < 1) :
    (∫ x, sourceMomentDensity q a x) =
      2*(a+(xiSpectralPoint q).im)*(∫ x, varianceDensity q a x) := by
  rw [integral_sourceMoment q ha, integral_variance q ha, integral_weightedMode q ha]
  have hi : ((shift q a)⁻¹).im = -(a+(xiSpectralPoint q).im)*Complex.normSq ((shift q a)⁻¹) := by
    rw [Complex.inv_im, Complex.normSq_inv, div_eq_mul_inv]
    simp only [shift, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
    ring
  rw [div_eq_mul_inv]
  simp only [Complex.mul_im, Complex.neg_im, Complex.ofReal_im, Complex.neg_re,
    Complex.ofReal_re]
  rw [hi]
  ring

private theorem ratio_deviation_exists (q : XiZeroCopy) (a : ℝ) :
    ∃ x : ℝ, sourceRatio q x+(shift q a)⁻¹ ≠ 0 := by
  by_contra h
  push Not at h
  have he : sourceRatio q = fun _ => -(shift q a)⁻¹ := by
    funext x
    exact eq_neg_of_add_eq_zero_left (h x)
  have hd (x : ℝ) := hasDerivAt_ratio q x
  simp only [he] at hd
  have h0 := (hd 0).unique (hasDerivAt_const 0 (-(shift q a)⁻¹))
  have h1 := (hd 1).unique (hasDerivAt_const 1 (-(shift q a)⁻¹))
  have hQ0 : Q 0 = 0 := by
    have hz := iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) (by exact ⟨0, rfl⟩)
    simpa [Q, iteratedDeriv_one] using hz
  have hQ1 : Q 1 < 0 := by
    have hn := neg_iteratedDeriv_one_thetaCuspLogSource_pos (x := 1) zero_lt_one
    simpa only [Q, iteratedDeriv_one, neg_pos] using hn
  have hm : (Q 1 : ℂ)*(shift q a)⁻¹=0 := by
    rw [hQ0, Complex.ofReal_zero] at h0
    linear_combination h1-h0
  have hQne : (Q 1 : ℂ) ≠ 0 := by exact_mod_cast hQ1.ne
  exact (mul_ne_zero hQne (inv_ne_zero (shift_ne_zero q a))) hm

private theorem variance_pos (q : XiZeroCopy) {a : ℝ} (ha : |a| < 1) :
    0 < ∫ x, varianceDensity q a x := by
  have hc : Continuous (varianceDensity q a) :=
    (tiltedSource_continuous a).mul (((continuous_sourceRatio q).add continuous_const).norm.pow 2)
  have hn : 0 ≤ varianceDensity q a := fun x => mul_nonneg (tiltedSource_pos a x).le (sq_nonneg _)
  rw [integral_pos_iff_support_of_nonneg hn (variance_integrable q ha)]
  apply IsOpen.measure_pos volume hc.isOpen_support
  obtain ⟨x,hx⟩ := ratio_deviation_exists q a
  refine ⟨x, ?_⟩
  exact (mul_pos (tiltedSource_pos a x) (sq_pos_of_pos (norm_pos_iff.mpr hx))).ne'


/-- Integrated squared deviation from the exact tilted source mean. -/
def sourceVariance (q : XiZeroCopy) (a : ℝ) : ℝ := ∫ x, varianceDensity q a x

private theorem tilt_mem {a : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1) : |a| < 1 := abs_lt.mpr ha

private theorem sourceMomentDensity_eq (q : XiZeroCopy) (a x : ℝ) :
    sourceMomentDensity q a x = (a+deriv thetaCuspLogSource x)*weightedEnergy q a x := by
  unfold sourceMomentDensity weightedEnergy
  rw [(hasDerivAt_tiltedSource a x).deriv]
  dsimp [Q]
  ring

/-- The ratio definition retains the original mode and reciprocal source weight. -/
theorem weightedEnergy_eq (q : XiZeroCopy) (a x : ℝ) :
    weightedEnergy q a x = Real.exp (a*x)*‖mode q x‖^(2 : ℕ)/thetaCuspFullSource x := by
  unfold weightedEnergy tiltedSource sourceRatio
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (thetaCuspFullSource_pos_all x)]
  field_simp [(thetaCuspFullSource_pos_all x).ne']


/-- Exact tilted first-order source equation, retaining the complex spectral parameter. -/
theorem weightedMode_hasDerivAt (q : XiZeroCopy) (a x : ℝ) :
    HasDerivAt (weightedMode q a)
      (-I*(xiSpectralPoint q+I*(a:ℂ))*weightedMode q a x-I*(tiltedSource a x:ℂ)) x :=
  hasDerivAt_weightedMode q a x

/-- Exact derivative of the weighted energy density. -/
theorem weightedEnergy_hasDerivAt (q : XiZeroCopy) (a x : ℝ) :
    HasDerivAt (weightedEnergy q a)
      ((a+2*(xiSpectralPoint q).im-deriv thetaCuspLogSource x)*weightedEnergy q a x -
        2*(weightedMode q a x).im) x := by
  have h := hasDerivAt_weightedEnergy q a x
  rw [sourceMomentDensity_eq] at h
  exact h.congr_deriv (by ring)

/-- The actual tilted weighted energy is integrable throughout the admitted tilt interval. -/
theorem tilted_energy_integrable (q : XiZeroCopy) (a : Ioo (-1 : ℝ) 1) :
    Integrable (weightedEnergy q a.val) := weightedEnergy_integrable q (tilt_mem a.property)

/-- The full tilted logarithmic-source current is integrable. -/
theorem tilted_current_integrable (q : XiZeroCopy) (a : Ioo (-1 : ℝ) 1) :
    Integrable (fun x => (a.val+deriv thetaCuspLogSource x)*weightedEnergy q a.val x) := by
  exact (sourceMoment_integrable q (tilt_mem a.property)).congr
    (Eventually.of_forall fun x => sourceMomentDensity_eq q a.val x)

/-- The actual squared deviation is strictly positive at every admitted tilt. -/
theorem tilted_variance_pos (q : XiZeroCopy) (a : Ioo (-1 : ℝ) 1) :
    0 < sourceVariance q a.val := variance_pos q (tilt_mem a.property)

/-- Exact positive-variance factorization of the full tilted source current. -/
theorem tilted_source_current_eq_variance (q : XiZeroCopy) (a : Ioo (-1 : ℝ) 1) :
    (∫ x, (a.val+deriv thetaCuspLogSource x)*weightedEnergy q a.val x) =
      2*(a.val+(xiSpectralPoint q).im)*sourceVariance q a.val := by
  simpa only [sourceMomentDensity_eq, sourceVariance] using! source_variance_identity q (tilt_mem a.property)


/-- Actual energy splits into the explicit source-mass term and its positive variance. -/
theorem tilted_energy_decomposition (q : XiZeroCopy) (a : Ioo (-1 : ℝ) 1) :
    (∫ x, weightedEnergy q a.val x) = sourceVariance q a.val +
      (∫ x, tiltedSource a.val x)/‖xiSpectralPoint q+I*(a.val:ℂ)‖^(2 : ℕ) := by
  have h := integral_variance q (tilt_mem a.property)
  rw [Complex.normSq_inv, Complex.normSq_eq_norm_sq] at h
  change sourceVariance q a.val = (∫ x, weightedEnergy q a.val x) -
    (∫ x, tiltedSource a.val x)*(‖xiSpectralPoint q+I*(a.val:ℂ)‖^(2 : ℕ))⁻¹ at h
  rw [div_eq_mul_inv]
  linarith

/-- The positive variance gives a strict source-mass lower bound on the actual energy. -/
theorem tilted_energy_strict_floor (q : XiZeroCopy) (a : Ioo (-1 : ℝ) 1) :
    (∫ x, tiltedSource a.val x)/‖xiSpectralPoint q+I*(a.val:ℂ)‖^(2 : ℕ) <
      ∫ x, weightedEnergy q a.val x := by
  rw [tilted_energy_decomposition]
  linarith [tilted_variance_pos q a]

/-- At the original weight, the source current is transverse parameter times positive variance. -/
theorem source_current_eq_variance (q : XiZeroCopy) :
    (∫ x, deriv thetaCuspLogSource x*weightedEnergy q 0 x) =
      2*(xiSpectralPoint q).im*sourceVariance q 0 := by
  simpa using tilted_source_current_eq_variance q ⟨0, by constructor <;> norm_num⟩

/-- The original-weight actual mode has strictly positive source variance. -/
theorem source_variance_pos (q : XiZeroCopy) : 0 < sourceVariance q 0 :=
  tilted_variance_pos q ⟨0, by constructor <;> norm_num⟩

private def gaugeTilt (q : XiZeroCopy) : Ioo (-1 : ℝ) 1 :=
  ⟨-(xiSpectralPoint q).im, by
    have h := abs_lt.mp (strip q)
    constructor <;> linarith⟩

/-- The exact gauge needed for the transformed differential equation has finite energy. -/
theorem gauge_energy_integrable (q : XiZeroCopy) :
    Integrable (weightedEnergy q (-(xiSpectralPoint q).im)) :=
  tilted_energy_integrable q (gaugeTilt q)

private theorem gauge_current_split (q : XiZeroCopy) (x : ℝ) :
    deriv thetaCuspLogSource x*weightedEnergy q (-(xiSpectralPoint q).im) x =
      (-(xiSpectralPoint q).im+deriv thetaCuspLogSource x)*weightedEnergy q (-(xiSpectralPoint q).im) x +
        (xiSpectralPoint q).im*weightedEnergy q (-(xiSpectralPoint q).im) x := by ring

/-- The odd-source term in the exact gauge is absolutely integrable. -/
theorem gauge_current_integrable (q : XiZeroCopy) :
    Integrable (fun x => deriv thetaCuspLogSource x*weightedEnergy q (-(xiSpectralPoint q).im) x) := by
  simp_rw [gauge_current_split]
  exact (tilted_current_integrable q (gaugeTilt q)).add
    ((gauge_energy_integrable q).const_mul (xiSpectralPoint q).im)

/-- The weighted source balance follows with its endpoint terms and integrability discharged. -/
theorem gauge_source_balance (q : XiZeroCopy) :
    (∫ x, deriv thetaCuspLogSource x*weightedEnergy q (-(xiSpectralPoint q).im) x) =
      (xiSpectralPoint q).im*(∫ x, weightedEnergy q (-(xiSpectralPoint q).im) x) := by
  have hz := tilted_source_current_eq_variance q (gaugeTilt q)
  change (∫ x, (-(xiSpectralPoint q).im+deriv thetaCuspLogSource x)*weightedEnergy q (-(xiSpectralPoint q).im) x) =
    2*(-(xiSpectralPoint q).im+(xiSpectralPoint q).im)*sourceVariance q (-(xiSpectralPoint q).im) at hz
  simp only [neg_add_cancel, mul_zero, zero_mul] at hz
  simp_rw [gauge_current_split]
  have hi := integral_add (tilted_current_integrable q (gaugeTilt q))
    ((gauge_energy_integrable q).const_mul (xiSpectralPoint q).im)
  have heq : (∫ x, (-(xiSpectralPoint q).im+deriv thetaCuspLogSource x)*weightedEnergy q (-(xiSpectralPoint q).im) x +
      (xiSpectralPoint q).im*weightedEnergy q (-(xiSpectralPoint q).im) x) =
    (∫ x, (-(xiSpectralPoint q).im+deriv thetaCuspLogSource x)*weightedEnergy q (-(xiSpectralPoint q).im) x) +
      (∫ x, (xiSpectralPoint q).im*weightedEnergy q (-(xiSpectralPoint q).im) x) := by
    simpa only [gaugeTilt] using! hi
  rw [heq, hz, zero_add, integral_const_mul]

/-- The exact gauge energy is strictly positive. -/
theorem gauge_energy_pos (q : XiZeroCopy) :
    0 < ∫ x, weightedEnergy q (-(xiSpectralPoint q).im) x := by
  have hp (x : ℝ) : 0 < weightedEnergy q (-(xiSpectralPoint q).im) x := by
    unfold weightedEnergy
    apply mul_pos (tiltedSource_pos _ _)
    apply sq_pos_of_pos
    exact norm_pos_iff.mpr (div_ne_zero (mode_ne_zero q x) (source_ne_zero x))
  rw [integral_pos_iff_support_of_nonneg (fun x => (hp x).le) (gauge_energy_integrable q)]
  have hc : Continuous (weightedEnergy q (-(xiSpectralPoint q).im)) :=
    (tiltedSource_continuous _).mul ((continuous_sourceRatio q).norm.pow 2)
  exact IsOpen.measure_pos volume hc.isOpen_support ⟨0, (hp 0).ne'⟩

end
end RHTower.SelbergThetaSourceVariance
