import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheReciprocalLogarithmicFactorHasItsCutDensity
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneCauchyFormula

/-!
# The positive measure of the reciprocal logarithmic factor

The reciprocal factor is exactly the Stieltjes transform of its positive pole
residue and explicit cut density. Shifted Cauchy formulas and dominated boundary
limits give a subtracted identity. Positive real differences, Fatou's lemma and
monotone convergence prove integrability and remove the subtraction constant.
-/

open MeasureTheory Set Filter Topology Complex Metric
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

/-- A divided difference makes the regular reciprocal decay fast enough for Cauchy inversion. -/
def logarithmicReciprocalCauchyKernel : ℂ → ℂ :=
  dslope regularLogReferenceReciprocal (-Complex.I)

theorem analyticOnNhd_logarithmicReciprocalCauchyKernel :
    AnalyticOnNhd ℂ logarithmicReciprocalCauchyKernel logarithmicFactorContinuationDomain := by
  have hp : -Complex.I ∈ logarithmicFactorContinuationDomain := Or.inr (by norm_num)
  have hd := (Complex.differentiableOn_dslope
    (isOpen_logarithmicFactorContinuationDomain.mem_nhds hp)).mpr
      analyticOnNhd_regularLogReferenceReciprocal.differentiableOn
  intro z hz
  exact hd.analyticAt (isOpen_logarithmicFactorContinuationDomain.mem_nhds hz)

theorem logarithmicReciprocalCauchyKernel_eq {z : ℂ} (hz : z ≠ -Complex.I) :
    logarithmicReciprocalCauchyKernel z =
      (regularLogReferenceReciprocal z - regularLogReferenceReciprocal (-Complex.I)) /
        (z + Complex.I) := by
  rw [logarithmicReciprocalCauchyKernel, dslope_of_ne _ hz, slope_def_field, sub_neg_eq_add]

private theorem norm_logarithmicReciprocalCauchyKernel_le
    {C : ℝ} (hC : 0 < C)
    (hb : ∀ z : ℂ, z.im ≠ 0 → ‖regularLogReferenceReciprocal z‖ ≤ C)
    {z : ℂ} (hi : z.im ≠ 0) (hz : 2 ≤ ‖z‖) :
    ‖logarithmicReciprocalCauchyKernel z‖ ≤ 4 * C / ‖z‖ := by
  have hne : z ≠ -Complex.I := by
    intro he
    norm_num [he] at hz
  rw [logarithmicReciprocalCauchyKernel_eq hne, norm_div]
  have hnum : ‖regularLogReferenceReciprocal z - regularLogReferenceReciprocal (-Complex.I)‖ ≤ 2 * C := by
    have h := norm_sub_le (regularLogReferenceReciprocal z) (regularLogReferenceReciprocal (-Complex.I))
    linarith only [h, hb z hi, hb (-Complex.I) (by norm_num)]
  have hden : ‖z‖ / 2 ≤ ‖z + Complex.I‖ := by
    have h := norm_sub_le (z + Complex.I) Complex.I
    rw [add_sub_cancel_right, Complex.norm_I] at h
    linarith only [h, hz]
  have hpos : 0 < ‖z‖ / 2 := by linarith only [hz]
  calc
    _ ≤ (2 * C) / (‖z‖ / 2) := div_le_div₀ (by positivity) hnum hpos hden
    _ = _ := by ring

private theorem norm_le_norm_add_positive_imaginary {z : ℂ} {e : ℝ}
    (hz : 0 ≤ z.im) (he : 0 ≤ e) : ‖z‖ ≤ ‖z + (e : ℂ) * Complex.I‖ := by
  have hs : ‖z‖ ^ 2 ≤ ‖z + (e : ℂ) * Complex.I‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      mul_one]
    nlinarith only [mul_nonneg hz he, sq_nonneg e]
  nlinarith only [hs, norm_nonneg z, norm_nonneg (z + (e : ℂ) * Complex.I)]

/-- Cauchy's formula applies on every horizontal line above the cut. -/
theorem integral_logarithmicReciprocalCauchyKernel_upper_shift
    {e : ℝ} (he : 0 < e) {w : ℂ} (hw : 0 < w.im) :
    (∫ x : ℝ, logarithmicReciprocalCauchyKernel ((x : ℂ) + (e : ℂ) * Complex.I) /
      ((x : ℂ) - w)) =
      2 * (Real.pi : ℂ) * Complex.I * logarithmicReciprocalCauchyKernel (w + (e : ℂ) * Complex.I) := by
  obtain ⟨C, hC, _, hbound⟩ := exists_bound_regularLogReferenceReciprocal
  have him : ∀ z : ℂ, 0 ≤ z.im → 0 < (z + (e : ℂ) * Complex.I).im := by
    intro z hz
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    exact add_pos_of_nonneg_of_pos hz he
  have hdiff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ
      (fun v : ℂ => logarithmicReciprocalCauchyKernel (v + (e : ℂ) * Complex.I)) z := by
    intro z hz
    have hd := (analyticOnNhd_logarithmicReciprocalCauchyKernel _ (Or.inr (him z hz).ne')).differentiableAt
    simpa only [Function.comp_def] using!
      hd.comp z (differentiableAt_id.add_const ((e : ℂ) * Complex.I))
  apply HTGeometry.integral_div_sub_eq_of_upperHalfPlane_farDecay hdiff (R := 2) (M := 4 * C)
    (by norm_num) _ hw
  intro z hz hr
  have hshift := norm_le_norm_add_positive_imaginary hz he.le
  calc
    _ ≤ 4 * C / ‖z + (e : ℂ) * Complex.I‖ :=
      norm_logarithmicReciprocalCauchyKernel_le hC hbound (him z hz).ne' (hr.trans hshift)
    _ ≤ 4 * C / ‖z‖ := div_le_div₀ (by positivity) le_rfl (by linarith only [hr]) hshift

private theorem integral_logarithmicReciprocalCauchyKernel_lower_reflected
    {e : ℝ} (he : 0 < e) {w : ℂ} (hw : 0 < w.im) :
    (∫ x : ℝ, logarithmicReciprocalCauchyKernel (-(x : ℂ) - (e : ℂ) * Complex.I) /
      (-(x : ℂ) - w)) = 0 := by
  obtain ⟨C, hC, _, hbound⟩ := exists_bound_regularLogReferenceReciprocal
  have him : ∀ z : ℂ, 0 ≤ z.im → (-z - (e : ℂ) * Complex.I).im < 0 := by
    intro z hz
    simp only [Complex.sub_im, Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    linarith only [hz, he]
  have hden : ∀ z : ℂ, 0 ≤ z.im → -z - w ≠ 0 := by
    intro z hz heq
    have hi := congrArg Complex.im heq
    simp only [Complex.sub_im, Complex.neg_im, Complex.zero_im] at hi
    linarith only [hi, hz, hw]
  have hdiff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ
      (fun v : ℂ => logarithmicReciprocalCauchyKernel (-v - (e : ℂ) * Complex.I) / (-v - w)) z := by
    intro z hz
    have hd := (analyticOnNhd_logarithmicReciprocalCauchyKernel _ (Or.inr (him z hz).ne)).differentiableAt
    have hlin : DifferentiableAt ℂ (fun v : ℂ => -v - (e : ℂ) * Complex.I) z := by fun_prop
    have hn : DifferentiableAt ℂ
        (fun v : ℂ => logarithmicReciprocalCauchyKernel (-v - (e : ℂ) * Complex.I)) z := by
      simpa only [Function.comp_def] using! hd.comp z hlin
    exact hn.div (by fun_prop) (hden z hz)
  apply HTGeometry.integral_eq_zero_of_upperHalfPlane_farDecay hdiff
    (R := 2 + 2 * ‖w‖) (M := 8 * C) (by positivity)
  intro z hz hr
  have hnz : 2 ≤ ‖z‖ := by linarith only [hr, norm_nonneg w]
  have hpos : 0 < ‖z‖ := by linarith only [hnz]
  have hshift : ‖z‖ ≤ ‖-z - (e : ℂ) * Complex.I‖ := by
    have heq : -z - (e : ℂ) * Complex.I = -(z + (e : ℂ) * Complex.I) := by ring
    rw [heq, norm_neg]
    exact norm_le_norm_add_positive_imaginary hz he.le
  have hg : ‖logarithmicReciprocalCauchyKernel (-z - (e : ℂ) * Complex.I)‖ ≤ 4 * C / ‖z‖ :=
    (norm_logarithmicReciprocalCauchyKernel_le hC hbound (him z hz).ne (hnz.trans hshift)).trans
      (div_le_div₀ (by positivity) le_rfl hpos hshift)
  have hd : ‖z‖ / 2 ≤ ‖-z - w‖ := by
    have h := norm_sub_le (z + w) w
    rw [add_sub_cancel_right] at h
    have heq : -z - w = -(z + w) := by ring
    rw [heq, norm_neg]
    linarith only [h, hr]
  rw [norm_div]
  calc
    _ ≤ (4 * C / ‖z‖) / (‖z‖ / 2) := div_le_div₀ (by positivity) hg (by positivity) hd
    _ = 8 * C / ‖z‖ ^ 2 := by ring

/-- The lower horizontal line contributes zero to the upper Cauchy formula. -/
theorem integral_logarithmicReciprocalCauchyKernel_lower_shift
    {e : ℝ} (he : 0 < e) {w : ℂ} (hw : 0 < w.im) :
    (∫ x : ℝ, logarithmicReciprocalCauchyKernel ((x : ℂ) - (e : ℂ) * Complex.I) /
      ((x : ℂ) - w)) = 0 := by
  let f : ℝ → ℂ := fun x => logarithmicReciprocalCauchyKernel
    ((x : ℂ) - (e : ℂ) * Complex.I) / ((x : ℂ) - w)
  have hneg : (∫ x : ℝ, f x) = ∫ x : ℝ, f (-x) := by
    conv_lhs => rw [← Measure.map_neg_eq_self (volume : Measure ℝ),
      measurableEmbedding_neg.integral_map]
  change (∫ x : ℝ, f x) = 0
  rw [hneg]
  simpa only [f, Complex.ofReal_neg] using
    integral_logarithmicReciprocalCauchyKernel_lower_reflected he hw

private theorem norm_shifted_logarithmic_cauchy_integrand_le
    {C : ℝ} (hC : 0 < C)
    (hb : ∀ z : ℂ, z.im ≠ 0 → ‖regularLogReferenceReciprocal z‖ ≤ C)
    {w : ℂ} (hw : 0 < w.im) {d : ℝ} (hd : d ≠ 0) (hdsmall : |d| ≤ 1 / 2)
    (x : ℝ) :
    ‖logarithmicReciprocalCauchyKernel ((x : ℂ) + (d : ℂ) * Complex.I) / ((x : ℂ) - w)‖ ≤
      ((4 * C / w.im) * (1 + (2 * ‖w‖ + 2) ^ 2) + 8 * C) / (1 + x ^ 2) := by
  let q : ℂ := (x : ℂ) + (d : ℂ) * Complex.I
  have hqi : q.im = d := by simp only [q, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hqr : q.re = x := by simp only [q, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, add_zero]
  have hdlo : -(1 / 2 : ℝ) ≤ d := (abs_le.mp hdsmall).1
  have hne : q ≠ -Complex.I := by
    intro he
    have hi := congrArg Complex.im he
    rw [hqi, Complex.neg_im, Complex.I_im] at hi
    linarith only [hi, hdlo]
  have hnum : ‖regularLogReferenceReciprocal q - regularLogReferenceReciprocal (-Complex.I)‖ ≤ 2 * C := by
    have h := norm_sub_le (regularLogReferenceReciprocal q) (regularLogReferenceReciprocal (-Complex.I))
    have hq := hb q (by rwa [hqi])
    have hp := hb (-Complex.I) (by norm_num)
    linarith only [h, hq, hp]
  have hA : 1 / 2 ≤ ‖q + Complex.I‖ := by
    have h := Complex.im_le_norm (q + Complex.I)
    rw [Complex.add_im, hqi, Complex.I_im] at h
    linarith only [h, hdlo]
  have hAx : |x| ≤ ‖q + Complex.I‖ := by
    simpa only [Complex.add_re, hqr, Complex.I_re, add_zero] using
      Complex.abs_re_le_norm (q + Complex.I)
  have hB : w.im ≤ ‖(x : ℂ) - w‖ := by
    simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_pos hw] using
      Complex.abs_im_le_norm ((x : ℂ) - w)
  have hBx : |x| - ‖w‖ ≤ ‖(x : ℂ) - w‖ := by
    have h := norm_add_le ((x : ℂ) - w) w
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at h
    linarith only [h]
  change ‖logarithmicReciprocalCauchyKernel q / ((x : ℂ) - w)‖ ≤ _
  rw [logarithmicReciprocalCauchyKernel_eq hne, norm_div, norm_div, div_div]
  by_cases hx : |x| ≤ 2 * ‖w‖ + 2
  · have hprod : (1 / 2) * w.im ≤ ‖q + Complex.I‖ * ‖(x : ℂ) - w‖ :=
      mul_le_mul hA hB hw.le (norm_nonneg _)
    have hfirst : ‖regularLogReferenceReciprocal q - regularLogReferenceReciprocal (-Complex.I)‖ /
        (‖q + Complex.I‖ * ‖(x : ℂ) - w‖) ≤ 4 * C / w.im := by
      calc
        _ ≤ (2 * C) / ((1 / 2) * w.im) := div_le_div₀ (by positivity) hnum (by positivity) hprod
        _ = _ := by ring
    refine hfirst.trans ((le_div_iff₀ (by positivity : 0 < 1 + x ^ 2)).mpr ?_)
    have hs : x ^ 2 ≤ (2 * ‖w‖ + 2) ^ 2 := by
      nlinarith only [hx, sq_abs x, abs_nonneg x, norm_nonneg w]
    have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * C / w.im by positivity)
    linarith only [hmul, hC]
  · have hxgt : 2 * ‖w‖ + 2 < |x| := lt_of_not_ge hx
    have hxpos : 0 < |x| := by linarith only [hxgt, norm_nonneg w]
    have hBl : |x| / 2 ≤ ‖(x : ℂ) - w‖ := by linarith only [hBx, hxgt]
    have hprod : |x| * (|x| / 2) ≤ ‖q + Complex.I‖ * ‖(x : ℂ) - w‖ :=
      mul_le_mul hAx hBl (by positivity) (norm_nonneg _)
    have hspos : 0 < x ^ 2 := by nlinarith only [hxpos, sq_abs x]
    have hsone : 1 ≤ x ^ 2 := by nlinarith only [hxgt, norm_nonneg w, sq_abs x]
    calc
      _ ≤ (2 * C) / (|x| * (|x| / 2)) := div_le_div₀ (by positivity) hnum (by positivity) hprod
      _ = 4 * C / x ^ 2 := by rw [show |x| * (|x| / 2) = x ^ 2 / 2 by nlinarith only [sq_abs x]]; ring
      _ ≤ (8 * C) / (1 + x ^ 2) := by
        apply (div_le_div_iff₀ hspos (by positivity)).mpr
        nlinarith only [mul_nonneg hC.le (sub_nonneg.mpr hsone)]
      _ ≤ _ := div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity)

private theorem tendsto_upper_regular_reciprocal (x : ℝ) :
    Tendsto (fun e : ℝ => regularLogReferenceReciprocal ((x : ℂ) + (e : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (nhds (upperRegularLogReferenceReciprocal (x : ℂ))) := by
  have hp : Tendsto (fun e : ℝ => (x : ℂ) + (e : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (𝓝[{z : ℂ | 0 ≤ z.im}] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun e : ℝ => (x : ℂ) + (e : ℂ) * Complex.I) 0 := by fun_prop
      simpa only [Complex.ofReal_zero, zero_mul, add_zero] using!
        hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with e he
      simpa only [mem_setOf_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using he.le
  have h := (continuousOn_upperRegularLogReferenceReciprocal (x : ℂ)
    (by simp only [mem_setOf_eq, Complex.ofReal_im, le_refl])).tendsto.comp hp
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  have hne : (x : ℂ) + (e : ℂ) * Complex.I ≠ -1 := by
    intro heq
    have hi := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
      Complex.neg_im, Complex.one_im, neg_zero] at hi
    exact he.ne' hi
  exact upperRegularLogReferenceReciprocal_eq hne

private theorem tendsto_lower_regular_reciprocal (x : ℝ) :
    Tendsto (fun e : ℝ => regularLogReferenceReciprocal ((x : ℂ) - (e : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (nhds (starRingEnd ℂ (upperRegularLogReferenceReciprocal (x : ℂ)))) := by
  have hstar : Continuous (fun z : ℂ => starRingEnd ℂ z) := by fun_prop
  have h := (hstar.tendsto _).comp (tendsto_upper_regular_reciprocal x)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  have hi : ((x : ℂ) + (e : ℂ) * Complex.I).im ≠ 0 := by
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using he.ne'
  have hc := regularLogReferenceReciprocal_conj hi
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
    ← sub_eq_add_neg] at hc
  exact hc.symm

private theorem tendsto_logarithmic_cauchy_kernel_of_boundary
    {f : ℝ → ℂ} {x : ℝ} {v : ℂ}
    (hf : Tendsto f (𝓝[>] (0 : ℝ)) (nhds (x : ℂ)))
    (hH : Tendsto (fun e => regularLogReferenceReciprocal (f e)) (𝓝[>] (0 : ℝ)) (nhds v)) :
    Tendsto (fun e => logarithmicReciprocalCauchyKernel (f e)) (𝓝[>] (0 : ℝ))
      (nhds ((v - regularLogReferenceReciprocal (-Complex.I)) / ((x : ℂ) + Complex.I))) := by
  have hne : (x : ℂ) ≠ -Complex.I := by
    intro he
    have hi := congrArg Complex.im he
    norm_num at hi
  have hden : (x : ℂ) + Complex.I ≠ 0 := by
    simpa only [sub_neg_eq_add] using sub_ne_zero.mpr hne
  have h := (hH.sub (tendsto_const_nhds (x := regularLogReferenceReciprocal (-Complex.I)))).div
    (hf.add tendsto_const_nhds) hden
  apply h.congr'
  filter_upwards [hf.eventually (isOpen_ne.eventually_mem hne)] with e he
  exact (logarithmicReciprocalCauchyKernel_eq he).symm

private theorem tendsto_upper_logarithmic_cauchy_kernel (x : ℝ) :
    Tendsto (fun e : ℝ => logarithmicReciprocalCauchyKernel ((x : ℂ) + (e : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (nhds ((upperRegularLogReferenceReciprocal (x : ℂ) -
        regularLogReferenceReciprocal (-Complex.I)) / ((x : ℂ) + Complex.I))) := by
  apply tendsto_logarithmic_cauchy_kernel_of_boundary _ (tendsto_upper_regular_reciprocal x)
  have hc : ContinuousAt (fun e : ℝ => (x : ℂ) + (e : ℂ) * Complex.I) 0 := by fun_prop
  simpa only [Complex.ofReal_zero, zero_mul, add_zero] using!
    hc.tendsto.mono_left nhdsWithin_le_nhds

private theorem tendsto_lower_logarithmic_cauchy_kernel (x : ℝ) :
    Tendsto (fun e : ℝ => logarithmicReciprocalCauchyKernel ((x : ℂ) - (e : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (nhds ((starRingEnd ℂ (upperRegularLogReferenceReciprocal (x : ℂ)) -
        regularLogReferenceReciprocal (-Complex.I)) / ((x : ℂ) + Complex.I))) := by
  apply tendsto_logarithmic_cauchy_kernel_of_boundary _ (tendsto_lower_regular_reciprocal x)
  have hc : ContinuousAt (fun e : ℝ => (x : ℂ) - (e : ℂ) * Complex.I) 0 := by fun_prop
  simpa only [Complex.ofReal_zero, zero_mul, sub_zero] using!
    hc.tendsto.mono_left nhdsWithin_le_nhds

private theorem continuous_shifted_logarithmic_cauchy_integrand
    {d : ℝ} (hd : d ≠ 0) {w : ℂ} (hw : 0 < w.im) :
    Continuous (fun x : ℝ => logarithmicReciprocalCauchyKernel
      ((x : ℂ) + (d : ℂ) * Complex.I) / ((x : ℂ) - w)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hi : ((x : ℂ) + (d : ℂ) * Complex.I).im ≠ 0 := by
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using hd
  have hG := (analyticOnNhd_logarithmicReciprocalCauchyKernel _ (Or.inr hi)).continuousAt
  have hlin : ContinuousAt (fun t : ℝ => (t : ℂ) + (d : ℂ) * Complex.I) x := by fun_prop
  have hden : (x : ℂ) - w ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at hi
    exact hw.ne' (neg_eq_zero.mp hi)
  have hn : ContinuousAt (fun t : ℝ => logarithmicReciprocalCauchyKernel
      ((t : ℂ) + (d : ℂ) * Complex.I)) x := by
    simpa only [Function.comp_def] using! hG.comp (f := fun t : ℝ => (t : ℂ) + (d : ℂ) * Complex.I)
      (x := x) hlin
  exact hn.div (by fun_prop) hden

/-- Upper boundary value of the regularized Cauchy integrand. -/
def upperLogarithmicCauchyBoundary (w : ℂ) (x : ℝ) : ℂ :=
  (upperRegularLogReferenceReciprocal (x : ℂ) - regularLogReferenceReciprocal (-Complex.I)) /
    ((x : ℂ) + Complex.I) / ((x : ℂ) - w)

/-- Lower boundary value of the regularized Cauchy integrand. -/
def lowerLogarithmicCauchyBoundary (w : ℂ) (x : ℝ) : ℂ :=
  (starRingEnd ℂ (upperRegularLogReferenceReciprocal (x : ℂ)) -
    regularLogReferenceReciprocal (-Complex.I)) / ((x : ℂ) + Complex.I) / ((x : ℂ) - w)

private theorem tendsto_integral_upper_logarithmic_cauchy {w : ℂ} (hw : 0 < w.im) :
    Tendsto (fun e : ℝ => ∫ x : ℝ,
      logarithmicReciprocalCauchyKernel ((x : ℂ) + (e : ℂ) * Complex.I) / ((x : ℂ) - w))
      (𝓝[>] (0 : ℝ)) (nhds (∫ x : ℝ, upperLogarithmicCauchyBoundary w x)) := by
  obtain ⟨C, hC, _, hb⟩ := exists_bound_regularLogReferenceReciprocal
  let M : ℝ := (4 * C / w.im) * (1 + (2 * ‖w‖ + 2) ^ 2) + 8 * C
  apply tendsto_integral_filter_of_dominated_convergence (fun x : ℝ => M / (1 + x ^ 2))
  · filter_upwards [self_mem_nhdsWithin] with e he
    exact (continuous_shifted_logarithmic_cauchy_integrand he.ne' hw).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds]
      with e he hes
    filter_upwards with x
    exact norm_shifted_logarithmic_cauchy_integrand_le hC hb hw he.ne'
      (by rw [abs_of_pos he]; exact hes.le) x
  · simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul M
  · filter_upwards with x
    have hden : (x : ℂ) - w ≠ 0 := by
      intro he
      have hi := congrArg Complex.im he
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at hi
      exact hw.ne' (neg_eq_zero.mp hi)
    exact (tendsto_upper_logarithmic_cauchy_kernel x).div tendsto_const_nhds hden

private theorem tendsto_integral_lower_logarithmic_cauchy {w : ℂ} (hw : 0 < w.im) :
    Tendsto (fun e : ℝ => ∫ x : ℝ,
      logarithmicReciprocalCauchyKernel ((x : ℂ) - (e : ℂ) * Complex.I) / ((x : ℂ) - w))
      (𝓝[>] (0 : ℝ)) (nhds (∫ x : ℝ, lowerLogarithmicCauchyBoundary w x)) := by
  obtain ⟨C, hC, _, hb⟩ := exists_bound_regularLogReferenceReciprocal
  let M : ℝ := (4 * C / w.im) * (1 + (2 * ‖w‖ + 2) ^ 2) + 8 * C
  apply tendsto_integral_filter_of_dominated_convergence (fun x : ℝ => M / (1 + x ^ 2))
  · filter_upwards [self_mem_nhdsWithin] with e he
    simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using
      (continuous_shifted_logarithmic_cauchy_integrand (neg_ne_zero.mpr he.ne') hw).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds]
      with e he hes
    filter_upwards with x
    have hsmall : |-e| ≤ 1 / 2 := by rw [abs_neg, abs_of_pos he]; exact hes.le
    simpa only [Pi.div_apply, M, Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using!
      norm_shifted_logarithmic_cauchy_integrand_le hC hb hw (neg_ne_zero.mpr he.ne') hsmall x
  · simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul M
  · filter_upwards with x
    have hden : (x : ℂ) - w ≠ 0 := by
      intro he
      have hi := congrArg Complex.im he
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at hi
      exact hw.ne' (neg_eq_zero.mp hi)
    exact (tendsto_lower_logarithmic_cauchy_kernel x).div tendsto_const_nhds hden

/-- The upper boundary reproduces the divided difference. -/
theorem integral_upperLogarithmicCauchyBoundary {w : ℂ} (hw : 0 < w.im) :
    (∫ x : ℝ, upperLogarithmicCauchyBoundary w x) =
      2 * (Real.pi : ℂ) * Complex.I * logarithmicReciprocalCauchyKernel w := by
  have hpath : Tendsto (fun e : ℝ => w + (e : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (nhds w) := by
    have hc : ContinuousAt (fun e : ℝ => w + (e : ℂ) * Complex.I) 0 := by fun_prop
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using!
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have hG := (analyticOnNhd_logarithmicReciprocalCauchyKernel w (Or.inr hw.ne')).continuousAt.tendsto.comp hpath
  have hr : Tendsto (fun e : ℝ => 2 * (Real.pi : ℂ) * Complex.I *
      logarithmicReciprocalCauchyKernel (w + (e : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (nhds (2 * (Real.pi : ℂ) * Complex.I * logarithmicReciprocalCauchyKernel w)) :=
    tendsto_const_nhds.mul hG
  have hri := hr.congr' (show (fun e : ℝ => 2 * (Real.pi : ℂ) * Complex.I *
      logarithmicReciprocalCauchyKernel (w + (e : ℂ) * Complex.I)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun e : ℝ => ∫ x : ℝ, logarithmicReciprocalCauchyKernel
        ((x : ℂ) + (e : ℂ) * Complex.I) / ((x : ℂ) - w)) from by
    filter_upwards [self_mem_nhdsWithin] with e he
    exact (integral_logarithmicReciprocalCauchyKernel_upper_shift he hw).symm)
  exact tendsto_nhds_unique (tendsto_integral_upper_logarithmic_cauchy hw) hri

/-- The lower boundary contributes no upper-half-plane residue. -/
theorem integral_lowerLogarithmicCauchyBoundary {w : ℂ} (hw : 0 < w.im) :
    (∫ x : ℝ, lowerLogarithmicCauchyBoundary w x) = 0 := by
  have hzero : Tendsto (fun e : ℝ => ∫ x : ℝ, logarithmicReciprocalCauchyKernel
      ((x : ℂ) - (e : ℂ) * Complex.I) / ((x : ℂ) - w)) (𝓝[>] (0 : ℝ)) (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with e he
    exact (integral_logarithmicReciprocalCauchyKernel_lower_shift he hw).symm
  exact tendsto_nhds_unique (tendsto_integral_lower_logarithmic_cauchy hw) hzero

private theorem integrable_logarithmic_cauchy_boundaries {w : ℂ} (hw : 0 < w.im) :
    Integrable (upperLogarithmicCauchyBoundary w) ∧ Integrable (lowerLogarithmicCauchyBoundary w) := by
  obtain ⟨C, hC, _, hb⟩ := exists_bound_regularLogReferenceReciprocal
  let M : ℝ := (4 * C / w.im) * (1 + (2 * ‖w‖ + 2) ^ 2) + 8 * C
  have hM : Integrable (fun x : ℝ => M / (1 + x ^ 2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul M
  have hcont : Continuous (fun x : ℝ => upperRegularLogReferenceReciprocal (x : ℂ)) :=
    continuousOn_upperRegularLogReferenceReciprocal.comp_continuous Complex.continuous_ofReal
      (fun x => by simp only [mem_setOf_eq, Complex.ofReal_im, le_refl])
  have hplus : ∀ x : ℝ, (x : ℂ) + Complex.I ≠ 0 := by
    intro x he
    have hi := congrArg Complex.im he
    norm_num at hi
  have hminus : ∀ x : ℝ, (x : ℂ) - w ≠ 0 := by
    intro x he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at hi
    exact hw.ne' (neg_eq_zero.mp hi)
  have hupper : Continuous (upperLogarithmicCauchyBoundary w) :=
    ((hcont.sub continuous_const).div (Complex.continuous_ofReal.add continuous_const) hplus).div
      (Complex.continuous_ofReal.sub continuous_const) hminus
  have hstar : Continuous (fun z : ℂ => starRingEnd ℂ z) := by fun_prop
  have hlower : Continuous (lowerLogarithmicCauchyBoundary w) :=
    (((hstar.comp hcont).sub continuous_const).div
      (Complex.continuous_ofReal.add continuous_const) hplus).div
      (Complex.continuous_ofReal.sub continuous_const) hminus
  constructor
  · apply hM.mono' hupper.aestronglyMeasurable
    filter_upwards with x
    have hl := ((tendsto_upper_logarithmic_cauchy_kernel x).div tendsto_const_nhds (hminus x)).norm
    apply le_of_tendsto_of_tendsto hl tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds]
      with e he hes
    exact norm_shifted_logarithmic_cauchy_integrand_le hC hb hw he.ne'
      (by rw [abs_of_pos he]; exact hes.le) x
  · apply hM.mono' hlower.aestronglyMeasurable
    filter_upwards with x
    have hl := ((tendsto_lower_logarithmic_cauchy_kernel x).div tendsto_const_nhds (hminus x)).norm
    apply le_of_tendsto_of_tendsto hl tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds]
      with e he hes
    have hsmall : |-e| ≤ 1 / 2 := by rw [abs_neg, abs_of_pos he]; exact hes.le
    simpa only [Pi.div_apply, M, Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using!
      norm_shifted_logarithmic_cauchy_integrand_le hC hb hw (neg_ne_zero.mpr he.ne') hsmall x

/-- The two contour sides leave exactly the boundary jump. -/
theorem integral_logarithmic_reciprocal_jump {w : ℂ} (hw : 0 < w.im) :
    (∫ x : ℝ, (upperRegularLogReferenceReciprocal (x : ℂ) -
      starRingEnd ℂ (upperRegularLogReferenceReciprocal (x : ℂ))) /
        (((x : ℂ) + Complex.I) * ((x : ℂ) - w))) =
      2 * (Real.pi : ℂ) * Complex.I * logarithmicReciprocalCauchyKernel w := by
  obtain ⟨hu, hl⟩ := integrable_logarithmic_cauchy_boundaries hw
  calc
    _ = ∫ x : ℝ, upperLogarithmicCauchyBoundary w x - lowerLogarithmicCauchyBoundary w x := by
      apply integral_congr_ae
      filter_upwards with x
      unfold upperLogarithmicCauchyBoundary lowerLogarithmicCauchyBoundary
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = (∫ x : ℝ, upperLogarithmicCauchyBoundary w x) -
        ∫ x : ℝ, lowerLogarithmicCauchyBoundary w x := integral_sub hu hl
    _ = _ := by rw [integral_upperLogarithmicCauchyBoundary hw,
      integral_lowerLogarithmicCauchyBoundary hw, sub_zero]

/-- The subtracted Cauchy formula is valid for the actual regular reciprocal. -/
theorem regularLogReferenceReciprocal_subtracted_cauchy {w : ℂ} (hw : 0 < w.im) :
    regularLogReferenceReciprocal w - regularLogReferenceReciprocal (-Complex.I) =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∫ x : ℝ,
        (upperRegularLogReferenceReciprocal (x : ℂ) -
          starRingEnd ℂ (upperRegularLogReferenceReciprocal (x : ℂ))) *
            (1 / ((x : ℂ) - w) - 1 / ((x : ℂ) + Complex.I)) := by
  have hden : ∀ x : ℝ, (x : ℂ) - w ≠ 0 := by
    intro x he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at hi
    exact hw.ne' (neg_eq_zero.mp hi)
  have hplus : ∀ x : ℝ, (x : ℂ) + Complex.I ≠ 0 := by
    intro x he
    have hi := congrArg Complex.im he
    norm_num at hi
  have heq (x : ℝ) :
      (upperRegularLogReferenceReciprocal (x : ℂ) -
        starRingEnd ℂ (upperRegularLogReferenceReciprocal (x : ℂ))) *
          (1 / ((x : ℂ) - w) - 1 / ((x : ℂ) + Complex.I)) =
        (w + Complex.I) * ((upperRegularLogReferenceReciprocal (x : ℂ) -
          starRingEnd ℂ (upperRegularLogReferenceReciprocal (x : ℂ))) /
            (((x : ℂ) + Complex.I) * ((x : ℂ) - w))) := by
    field_simp [hden x, hplus x]
    ring
  simp_rw [heq]
  rw [integral_const_mul, integral_logarithmic_reciprocal_jump hw]
  have hne : w ≠ -Complex.I := by
    intro he
    simp only [he, Complex.neg_im, Complex.I_im] at hw
    norm_num at hw
  have hwi : w + Complex.I ≠ 0 := by simpa only [sub_neg_eq_add] using sub_ne_zero.mpr hne
  have hc : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  rw [logarithmicReciprocalCauchyKernel_eq hne]
  field_simp [hwi, hc]

/-- Inserting the exact cut jump gives the subtracted Stieltjes identity. -/
theorem regularLogReferenceReciprocal_subtracted_stieltjes {w : ℂ} (hw : 0 < w.im) :
    regularLogReferenceReciprocal w - regularLogReferenceReciprocal (-Complex.I) =
      ∫ t in Ioi (1 : ℝ), (logarithmicFactorCutDensity t : ℂ) *
        (1 / ((t : ℂ) + w) - 1 / ((t : ℂ) - Complex.I)) := by
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  let F : ℝ → ℂ := fun x => -c * (logarithmicFactorCutDensity (-x) : ℂ) *
    (1 / ((x : ℂ) - w) - 1 / ((x : ℂ) + Complex.I))
  have hc : c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hcut : (∫ x : ℝ, (upperRegularLogReferenceReciprocal (x : ℂ) -
      starRingEnd ℂ (upperRegularLogReferenceReciprocal (x : ℂ))) *
        (1 / ((x : ℂ) - w) - 1 / ((x : ℂ) + Complex.I))) = ∫ x in Iio (-1 : ℝ), F x := by
    calc
      _ = ∫ x : ℝ, (Iio (-1 : ℝ)).indicator F x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [upperRegularLogReferenceReciprocal_jump]
        by_cases hx : x < -1
        · rw [if_pos hx, indicator_of_mem (s := Iio (-1 : ℝ)) hx]
        · rw [if_neg hx, zero_mul, indicator_of_notMem (s := Iio (-1 : ℝ)) hx]
      _ = _ := integral_indicator measurableSet_Iio
  have hreflect : (∫ x in Iio (-1 : ℝ), F x) = ∫ t in Ioi (1 : ℝ), F (-t) := by
    calc
      _ = ∫ x in Iic (-1 : ℝ), F x := setIntegral_congr_set Iio_ae_eq_Iic
      _ = _ := (integral_comp_neg_Ioi (1 : ℝ) F).symm
  have he (t : ℝ) : F (-t) = c * ((logarithmicFactorCutDensity t : ℂ) *
      (1 / ((t : ℂ) + w) - 1 / ((t : ℂ) - Complex.I))) := by
    dsimp only [F]
    simp only [neg_neg, Complex.ofReal_neg]
    rw [show -(t : ℂ) - w = -((t : ℂ) + w) by ring,
      show -(t : ℂ) + Complex.I = -((t : ℂ) - Complex.I) by ring]
    simp only [one_div, inv_neg]
    ring
  rw [regularLogReferenceReciprocal_subtracted_cauchy hw, hcut, hreflect]
  simp_rw [he]
  rw [integral_const_mul]
  change c⁻¹ * (c * _) = _
  exact inv_mul_cancel_left₀ hc _

/-- The density is the negative imaginary part of the upper reciprocal boundary. -/
theorem logarithmicFactorCutDensity_eq_boundary_im {t : ℝ} (ht : 1 < t) :
    logarithmicFactorCutDensity t = -(upperRegularLogReferenceReciprocal (-(t : ℂ))).im / Real.pi := by
  have hne : -(t : ℂ) ≠ -1 := by
    intro he
    have ht1 : t = 1 := by exact_mod_cast neg_injective he
    linarith only [ht, ht1]
  rw [upperRegularLogReferenceReciprocal_eq hne]
  have h := congrArg Complex.im (regularLogReferenceReciprocal_cut_jump ht)
  simp only [Complex.sub_im, Complex.conj_im, sub_neg_eq_add, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, zero_add, mul_one] at h
  norm_num at h
  apply (eq_div_iff Real.pi_ne_zero).mpr
  linarith only [h]

/-- The positive cut density is continuous along the interior of the cut. -/
theorem continuousOn_logarithmicFactorCutDensity :
    ContinuousOn logarithmicFactorCutDensity (Ioi (1 : ℝ)) := by
  have hc : Continuous (fun t : ℝ => upperRegularLogReferenceReciprocal (-(t : ℂ))) :=
    continuousOn_upperRegularLogReferenceReciprocal.comp_continuous Complex.continuous_ofReal.neg
      (fun t => by simp only [mem_setOf_eq, Complex.neg_im, Complex.ofReal_im, neg_zero, le_refl])
  have him : Continuous (fun t : ℝ => -(upperRegularLogReferenceReciprocal (-(t : ℂ))).im / Real.pi) :=
    (Complex.continuous_im.comp hc).neg.div_const Real.pi
  exact him.continuousOn.congr fun t ht => logarithmicFactorCutDensity_eq_boundary_im ht

private theorem norm_logarithmic_stieltjes_integrand_le {C : ℝ} (hC : 0 < C)
    (hbound : ∀ t : ℝ, 1 < t → logarithmicFactorCutDensity t ≤ C)
    {w : ℂ} (hw : 0 ≤ w.re) {t : ℝ} (ht : 1 < t) :
    ‖(logarithmicFactorCutDensity t : ℂ) *
      (1 / ((t : ℂ) + w) - 1 / ((t : ℂ) - Complex.I))‖ ≤
        2 * C * ‖w + Complex.I‖ / (1 + t ^ 2) := by
  have htpos : 0 < t := zero_lt_one.trans ht
  have hA : t ≤ ‖(t : ℂ) + w‖ := by
    have h := Complex.re_le_norm ((t : ℂ) + w)
    simp only [Complex.add_re, Complex.ofReal_re] at h
    linarith only [h, hw]
  have hB : t ≤ ‖(t : ℂ) - Complex.I‖ := by
    simpa only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero] using
      Complex.re_le_norm ((t : ℂ) - Complex.I)
  have hAne : (t : ℂ) + w ≠ 0 := norm_pos_iff.mp (htpos.trans_le hA)
  have hBne : (t : ℂ) - Complex.I ≠ 0 := norm_pos_iff.mp (htpos.trans_le hB)
  have he : 1 / ((t : ℂ) + w) - 1 / ((t : ℂ) - Complex.I) =
      -(w + Complex.I) / (((t : ℂ) + w) * ((t : ℂ) - Complex.I)) := by
    field_simp [hAne, hBne]
    ring
  rw [he, norm_mul, norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (logarithmicFactorCutDensity_pos t), ← mul_div_assoc]
  have hprod : t ^ 2 ≤ ‖(t : ℂ) + w‖ * ‖(t : ℂ) - Complex.I‖ := by
    simpa only [pow_two] using mul_le_mul hA hB htpos.le (norm_nonneg _)
  calc
    _ ≤ (C * ‖w + Complex.I‖) / t ^ 2 :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _))
        (sq_pos_of_pos htpos) hprod
    _ ≤ _ := by
      apply (div_le_div_iff₀ (sq_pos_of_pos htpos) (by positivity)).mpr
      have hs : 1 ≤ t ^ 2 := by nlinarith only [ht]
      have hm := mul_nonneg (show 0 ≤ C * ‖w + Complex.I‖ by positivity) (sub_nonneg.mpr hs)
      nlinarith only [hm]

private theorem continuousOn_logarithmic_stieltjes_integrand {w : ℂ} (hw : 0 ≤ w.re) :
    ContinuousOn (fun t : ℝ => (logarithmicFactorCutDensity t : ℂ) *
      (1 / ((t : ℂ) + w) - 1 / ((t : ℂ) - Complex.I))) (Ioi (1 : ℝ)) := by
  have hA : ∀ t ∈ Ioi (1 : ℝ), (t : ℂ) + w ≠ 0 := by
    intro t ht he
    change (1 : ℝ) < t at ht
    have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hr
    linarith only [ht, hw, hr]
  have hB : ∀ t ∈ Ioi (1 : ℝ), (t : ℂ) - Complex.I ≠ 0 := by
    intro t _ he
    have hi := congrArg Complex.im he
    norm_num at hi
  exact (Complex.continuous_ofReal.comp_continuousOn continuousOn_logarithmicFactorCutDensity).mul
    ((continuousOn_const.div (Complex.continuous_ofReal.add continuous_const).continuousOn hA).sub
      (continuousOn_const.div (Complex.continuous_ofReal.sub continuous_const).continuousOn hB))

theorem integrableOn_logarithmic_stieltjes_integrand {w : ℂ} (hw : 0 ≤ w.re) :
    IntegrableOn (fun t : ℝ => (logarithmicFactorCutDensity t : ℂ) *
      (1 / ((t : ℂ) + w) - 1 / ((t : ℂ) - Complex.I))) (Ioi (1 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := logarithmicFactorCutDensity_bounded
  have hM : IntegrableOn (fun t : ℝ => (2 * C * ‖w + Complex.I‖) / (1 + t ^ 2)) (Ioi (1 : ℝ)) := by
    simpa only [div_eq_mul_inv] using
      (integrable_inv_one_add_sq.const_mul (2 * C * ‖w + Complex.I‖)).integrableOn
  apply hM.mono' ((continuousOn_logarithmic_stieltjes_integrand hw).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_logarithmic_stieltjes_integrand_le hC hb hw ht

private theorem tendsto_integral_logarithmic_stieltjes_positive {s : ℝ} (hs : 0 < s) :
    Tendsto (fun e : ℝ => ∫ t in Ioi (1 : ℝ), (logarithmicFactorCutDensity t : ℂ) *
      (1 / ((t : ℂ) + ((s : ℂ) + (e : ℂ) * Complex.I)) - 1 / ((t : ℂ) - Complex.I)))
      (𝓝[>] (0 : ℝ)) (nhds (∫ t in Ioi (1 : ℝ), (logarithmicFactorCutDensity t : ℂ) *
        (1 / ((t : ℂ) + (s : ℂ)) - 1 / ((t : ℂ) - Complex.I)))) := by
  obtain ⟨C, hC, hb⟩ := logarithmicFactorCutDensity_bounded
  have hre (e : ℝ) : 0 ≤ ((s : ℂ) + (e : ℂ) * Complex.I).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, add_zero] using hs.le
  apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => (2 * C * (s + 2)) / (1 + t ^ 2))
  · exact Eventually.of_forall fun e =>
      (continuousOn_logarithmic_stieltjes_integrand (hre e)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with e he hes
    change (0 : ℝ) < e at he
    have hn : ‖((s : ℂ) + (e : ℂ) * Complex.I) + Complex.I‖ ≤ s + 2 := by
      calc
        _ ≤ ‖(s : ℂ) + (e : ℂ) * Complex.I‖ + ‖Complex.I‖ := norm_add_le _ _
        _ ≤ ‖(s : ℂ)‖ + ‖(e : ℂ) * Complex.I‖ + ‖Complex.I‖ :=
          by linarith only [norm_add_le (s : ℂ) ((e : ℂ) * Complex.I)]
        _ = s + e + 1 := by simp only [norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, abs_of_pos he]
        _ ≤ s + 2 := by linarith only [hes]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (norm_logarithmic_stieltjes_integrand_le hC hb (hre e) ht).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by positivity)) (by positivity))
  · simpa only [div_eq_mul_inv] using!
      (integrable_inv_one_add_sq.const_mul (2 * C * (s + 2))).integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change (1 : ℝ) < t at ht
    have hden : (t : ℂ) + ((s : ℂ) + (0 : ℂ) * Complex.I) ≠ 0 := by
      simp only [zero_mul, add_zero]
      have hp : 0 < t + s := by linarith only [ht, hs]
      exact_mod_cast hp.ne'
    have hdc : ContinuousAt (fun e : ℝ => (t : ℂ) + ((s : ℂ) + (e : ℂ) * Complex.I)) 0 := by fun_prop
    have hquot : ContinuousAt (fun e : ℝ => 1 / ((t : ℂ) + ((s : ℂ) + (e : ℂ) * Complex.I))) 0 :=
      continuousAt_const.div hdc hden
    have hc : ContinuousAt (fun e : ℝ => (logarithmicFactorCutDensity t : ℂ) *
        (1 / ((t : ℂ) + ((s : ℂ) + (e : ℂ) * Complex.I)) -
          1 / ((t : ℂ) - Complex.I))) 0 :=
      continuousAt_const.mul (hquot.sub continuousAt_const)
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using!
      hc.tendsto.mono_left nhdsWithin_le_nhds

/-- The subtracted Stieltjes identity extends to every positive real parameter. -/
theorem regularLogReferenceReciprocal_subtracted_stieltjes_ofReal {s : ℝ} (hs : 0 < s) :
    regularLogReferenceReciprocal (s : ℂ) - regularLogReferenceReciprocal (-Complex.I) =
      ∫ t in Ioi (1 : ℝ), (logarithmicFactorCutDensity t : ℂ) *
        (1 / ((t : ℂ) + (s : ℂ)) - 1 / ((t : ℂ) - Complex.I)) := by
  have hp : Tendsto (fun e : ℝ => (s : ℂ) + (e : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (nhds (s : ℂ)) := by
    have hc : ContinuousAt (fun e : ℝ => (s : ℂ) + (e : ℂ) * Complex.I) 0 := by fun_prop
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using!
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have hD : (s : ℂ) ∈ logarithmicFactorContinuationDomain := Or.inl (by
    simpa only [Complex.ofReal_re] using (show (-1 : ℝ) < s by linarith only [hs]))
  have hH := ((analyticOnNhd_regularLogReferenceReciprocal _ hD).continuousAt.tendsto.comp hp).sub
    (tendsto_const_nhds (x := regularLogReferenceReciprocal (-Complex.I)))
  have heq : (fun e : ℝ => regularLogReferenceReciprocal ((s : ℂ) + (e : ℂ) * Complex.I) -
      regularLogReferenceReciprocal (-Complex.I)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun e : ℝ => ∫ t in Ioi (1 : ℝ), (logarithmicFactorCutDensity t : ℂ) *
        (1 / ((t : ℂ) + ((s : ℂ) + (e : ℂ) * Complex.I)) - 1 / ((t : ℂ) - Complex.I))) := by
    filter_upwards [self_mem_nhdsWithin] with e he
    change (0 : ℝ) < e at he
    apply regularLogReferenceReciprocal_subtracted_stieltjes
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using he
  exact tendsto_nhds_unique (hH.congr' heq) (tendsto_integral_logarithmic_stieltjes_positive hs)

/-- Positive real parameters turn the subtracted formula into a difference of real Stieltjes kernels. -/
theorem logarithmic_stieltjes_difference {s S : ℝ} (hs : 0 < s) (hS : 0 < S) :
    IntegrableOn (fun t : ℝ => logarithmicFactorCutDensity t * (1 / (t + s) - 1 / (t + S)))
      (Ioi (1 : ℝ)) ∧
    (regularLogReferenceReciprocal (s : ℂ)).re - (regularLogReferenceReciprocal (S : ℂ)).re =
      ∫ t in Ioi (1 : ℝ), logarithmicFactorCutDensity t * (1 / (t + s) - 1 / (t + S)) := by
  let f : ℝ → ℝ → ℂ := fun a t => (logarithmicFactorCutDensity t : ℂ) *
    (1 / ((t : ℂ) + (a : ℂ)) - 1 / ((t : ℂ) - Complex.I))
  have hfs : IntegrableOn (f s) (Ioi (1 : ℝ)) := integrableOn_logarithmic_stieltjes_integrand hs.le
  have hfS : IntegrableOn (f S) (Ioi (1 : ℝ)) := integrableOn_logarithmic_stieltjes_integrand hS.le
  have he (t : ℝ) : f s t - f S t =
      ((logarithmicFactorCutDensity t * (1 / (t + s) - 1 / (t + S)) : ℝ) : ℂ) := by
    dsimp only [f]
    push_cast
    ring
  have hcint : IntegrableOn (fun t : ℝ =>
      ((logarithmicFactorCutDensity t * (1 / (t + s) - 1 / (t + S)) : ℝ) : ℂ)) (Ioi (1 : ℝ)) :=
    (hfs.sub hfS).congr (Eventually.of_forall he)
  have hrint : IntegrableOn (fun t : ℝ => logarithmicFactorCutDensity t *
      (1 / (t + s) - 1 / (t + S))) (Ioi (1 : ℝ)) := by
    simpa only [Complex.ofReal_re] using! hcint.re
  refine ⟨hrint, ?_⟩
  have hcomplex : regularLogReferenceReciprocal (s : ℂ) - regularLogReferenceReciprocal (S : ℂ) =
      ∫ t in Ioi (1 : ℝ), ((logarithmicFactorCutDensity t *
        (1 / (t + s) - 1 / (t + S)) : ℝ) : ℂ) := by
    calc
      _ = (regularLogReferenceReciprocal (s : ℂ) - regularLogReferenceReciprocal (-Complex.I)) -
          (regularLogReferenceReciprocal (S : ℂ) - regularLogReferenceReciprocal (-Complex.I)) := by ring
      _ = (∫ t in Ioi (1 : ℝ), f s t) - ∫ t in Ioi (1 : ℝ), f S t := by
        rw [regularLogReferenceReciprocal_subtracted_stieltjes_ofReal hs,
          regularLogReferenceReciprocal_subtracted_stieltjes_ofReal hS]
      _ = ∫ t in Ioi (1 : ℝ), f s t - f S t := (integral_sub hfs hfS).symm
      _ = _ := integral_congr_ae (Eventually.of_forall he)
  have h := congrArg Complex.re hcomplex
  simp only [Complex.sub_re] at h
  calc
    _ = _ := h
    _ = _ := by simpa only [Complex.ofReal_re] using! (integral_re hcint).symm

/-- The regular reciprocal vanishes along the positive real axis. -/
theorem tendsto_regularLogReferenceReciprocal_ofReal_atTop :
    Tendsto (fun s : ℝ => regularLogReferenceReciprocal (s : ℂ)) atTop (nhds 0) := by
  have hn : Tendsto (fun s : ℝ => ‖(s : ℂ)‖) atTop atTop := by
    apply tendsto_id.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    simp only [id_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  have hc : Tendsto (fun s : ℝ => (s : ℂ)) atTop (cocompact ℂ) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_norm_atTop_iff_cobounded.mp hn
  have hp : Tendsto (fun s : ℝ => (s : ℂ)) atTop
      (cocompact ℂ ⊓ 𝓟 {z : ℂ | 0 < z.re}) := by
    apply tendsto_inf.mpr ⟨hc, ?_⟩
    apply tendsto_principal.mpr
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact hs
  have hK := tendsto_inv_complexLogReferenceFactor_right.comp hp
  have hadd : Tendsto (fun s : ℝ => s + logarithmicFactorZeroRadius) atTop atTop :=
    tendsto_atTop_add_const_right atTop logarithmicFactorZeroRadius tendsto_id
  have hRreal : Tendsto (fun s : ℝ => logarithmicFactorReciprocalResidue /
      (s + logarithmicFactorZeroRadius)) atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero, div_eq_mul_inv] using!
      (tendsto_inv_atTop_zero.comp hadd).const_mul logarithmicFactorReciprocalResidue
  have hR : Tendsto (fun s : ℝ => (logarithmicFactorReciprocalResidue : ℂ) /
      ((s : ℂ) + (logarithmicFactorZeroRadius : ℂ))) atTop (nhds 0) := by
    simpa only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_zero] using!
      (Complex.continuous_ofReal.tendsto 0).comp hRreal
  have h := hK.sub hR
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  have hne : (s : ℂ) ≠ -(logarithmicFactorZeroRadius : ℂ) := by
    intro he
    have he' : s = -logarithmicFactorZeroRadius := by exact_mod_cast he
    linarith only [hs, he', logarithmicFactorZeroRadius_pos]
  rw [regularLogReferenceReciprocal_eq hne, continuedLogReferenceFactor_eq (Or.inl hs)]
  rfl

/-- Monotone positive differences recover the full finite Stieltjes integral. -/
theorem logarithmic_stieltjes_integral {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => logarithmicFactorCutDensity t / (t + s)) (Ioi (1 : ℝ)) ∧
    (regularLogReferenceReciprocal (s : ℂ)).re =
      ∫ t in Ioi (1 : ℝ), logarithmicFactorCutDensity t / (t + s) := by
  let μ : Measure ℝ := volume.restrict (Ioi (1 : ℝ))
  let S : ℕ → ℝ := fun n => s + (n : ℝ) + 1
  let f : ℕ → ℝ → ℝ := fun n t => logarithmicFactorCutDensity t *
    (1 / (t + s) - 1 / (t + S n))
  have hSpos (n : ℕ) : 0 < S n := by dsimp only [S]; positivity
  have hSint : ∀ n, Integrable (f n) μ := fun n => (logarithmic_stieltjes_difference hs (hSpos n)).1
  have hSgrow : Tendsto S atTop atTop := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    refine tendsto_atTop.mpr fun B => ?_
    filter_upwards [hnat.eventually_ge_atTop (B - s - 1)] with n hn
    dsimp only [S]
    linarith only [hn]
  have hnonneg : ∀ n, ∀ᵐ t ∂μ, 0 ≤ f n t := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change (1 : ℝ) < t at ht
    apply mul_nonneg (logarithmicFactorCutDensity_pos t).le
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by linarith only [ht, hs])
    dsimp only [S]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith only [hn]
  have hmono : ∀ᵐ t ∂μ, Monotone (fun n => f n t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change (1 : ℝ) < t at ht
    intro n m hnm
    apply mul_le_mul_of_nonneg_left _ (logarithmicFactorCutDensity_pos t).le
    apply sub_le_sub_left
    apply one_div_le_one_div_of_le (by linarith only [ht, hSpos n])
    have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    dsimp only [S]
    linarith only [hnm']
  have hpoint : ∀ᵐ t ∂μ, Tendsto (fun n => f n t) atTop
      (nhds (logarithmicFactorCutDensity t / (t + s))) := by
    filter_upwards with t
    have ht : Tendsto (fun n => t + S n) atTop atTop := by
      simpa only [add_comm] using tendsto_atTop_add_const_right atTop t hSgrow
    have hi := tendsto_inv_atTop_zero.comp ht
    simpa only [f, one_div, sub_zero, div_eq_mul_inv, Function.comp_def, one_mul] using!
      (tendsto_const_nhds (x := (t + s)⁻¹) |>.sub hi).const_mul (logarithmicFactorCutDensity t)
  have hH : Tendsto (fun n => (regularLogReferenceReciprocal (S n : ℂ)).re) atTop (nhds 0) := by
    simpa only [Function.comp_def, Complex.zero_re] using!
      (Complex.continuous_re.tendsto 0).comp
        (tendsto_regularLogReferenceReciprocal_ofReal_atTop.comp hSgrow)
  have hint : Tendsto (fun n => ∫ t, f n t ∂μ) atTop
      (nhds (regularLogReferenceReciprocal (s : ℂ)).re) := by
    have h := (tendsto_const_nhds (x := (regularLogReferenceReciprocal (s : ℂ)).re)).sub hH
    rw [sub_zero] at h
    apply h.congr'
    exact Eventually.of_forall fun n => (logarithmic_stieltjes_difference hs (hSpos n)).2
  have hnormeq (n : ℕ) : (∫⁻ t, ‖f n t‖ₑ ∂μ) = ENNReal.ofReal (∫ t, f n t ∂μ) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hSint n)]
    congr 1
    apply integral_congr_ae
    filter_upwards [hnonneg n] with t ht
    exact Real.norm_of_nonneg ht
  have hlin : Tendsto (fun n => ∫⁻ t, ‖f n t‖ₑ ∂μ) atTop
      (nhds (ENNReal.ofReal (regularLogReferenceReciprocal (s : ℂ)).re)) := by
    simp_rw [hnormeq]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hint
  have hfinite : liminf (fun n => ∫⁻ t, ‖f n t‖ₑ ∂μ) atTop ≠ ⊤ := by
    rw [hlin.liminf_eq]
    exact ENNReal.ofReal_ne_top
  have hF : Integrable (fun t : ℝ => logarithmicFactorCutDensity t / (t + s)) μ :=
    integrable_of_tendsto hpoint (fun n => (hSint n).aestronglyMeasurable) hfinite
  refine ⟨hF, ?_⟩
  exact tendsto_nhds_unique hint
    (integral_tendsto_of_tendsto_of_monotone hSint hF hmono hpoint)

/-- The reciprocal Poisson factor is exactly the Stieltjes transform of its positive atom and cut density. -/
theorem logReferenceFactor_reciprocal_stieltjes {s : ℝ} (hs : 0 < s) :
    (logReferenceFactor s)⁻¹ = logarithmicFactorReciprocalResidue /
      (s + logarithmicFactorZeroRadius) +
        ∫ t in Ioi (1 : ℝ), logarithmicFactorCutDensity t / (s + t) := by
  have h := (logarithmic_stieltjes_integral hs).2
  rw [regularLogReferenceReciprocal_ofReal hs, Complex.ofReal_re] at h
  simp only [add_comm s] at h ⊢
  linarith only [h]

#print axioms logarithmic_stieltjes_integral
#print axioms logReferenceFactor_reciprocal_stieltjes



#print axioms regularLogReferenceReciprocal_subtracted_cauchy


end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
