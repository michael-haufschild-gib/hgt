import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCanonicalDisorder
import GaloisForLFunctions.HTGeometry.GammaVerticalSharpBound

/-!
# Quantitative regularization of the full canonical phase

The phase on an explicit moving interior line approximates the full boundary
phase in dyadic L1. The bound retains all mass and uses its finite Cauchy moment.
It supplies boundary passage, not phase concentration.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace RHTower.WeilWorkSettledPhase

open WeilSpectral

private def windowError (η y r : ℝ) : ℝ :=
  |intervalPhaseKernel η (-y) y r - (Ioc (-y) y).indicator (fun _ => Real.pi) r|

private theorem measurable_windowError (η : ℝ) :
    Measurable (Function.uncurry (windowError η)) := by
  have hs : MeasurableSet {p : ℝ × ℝ | -p.1 < p.2 ∧ p.2 ≤ p.1} := by
    exact (isOpen_lt (continuous_fst.neg) continuous_snd).measurableSet.inter
      (isClosed_le continuous_snd continuous_fst).measurableSet
  have hi : Measurable (fun p : ℝ × ℝ =>
      (Ioc (-p.1) p.1).indicator (fun _ => Real.pi) p.2) := by
    convert (measurable_const (a := Real.pi)).indicator hs using 1
    ext p
    rfl
  exact ((by unfold intervalPhaseKernel; fun_prop :
    Measurable (fun p : ℝ × ℝ => intervalPhaseKernel η (-p.1) p.1 p.2)).sub hi).abs

private theorem windowError_le_pi {η y : ℝ} (hη : 0 < η) (hy : 0 ≤ y) (r : ℝ) :
    windowError η y r ≤ Real.pi := by
  have h0 := intervalPhaseKernel_nonneg hη (show -y ≤ y by linarith) r
  have h1 := intervalPhaseKernel_le_pi η (-y) y r
  unfold windowError
  by_cases hr : r ∈ Ioc (-y) y
  · rw [indicator_of_mem hr]
    exact abs_le.mpr ⟨by linarith, by linarith [Real.pi_pos]⟩
  · rw [indicator_of_notMem hr, sub_zero, abs_of_nonneg h0]
    exact h1

private theorem arctan_distance_lower {η h x : ℝ} (hη : 0 < η) (hh : 0 < h)
    (hx : h ≤ x) : Real.pi / 2 - η / h ≤ Real.arctan (x / η) := by
  have h := GaloisForLFunctions.HTGeometry.pi_div_two_sub_inv_le_arctan
    (div_pos hh hη)
  rw [one_div_div] at h
  exact h.trans (Real.arctan_strictMono.monotone (div_le_div_of_nonneg_right hx hη.le))

private theorem windowError_le_endpoint {η h y r : ℝ} (hη : 0 < η) (hh : 0 < h)
    (hy : 0 ≤ y) (hr : h ≤ |y + r|) (hyr : h ≤ |y - r|) :
    windowError η y r ≤ 2 * η / h := by
  rw [show 2 * η / h = 2 * (η / h) by ring]
  have hK0 := intervalPhaseKernel_nonneg hη (show -y ≤ y by linarith) r
  have hK1 := intervalPhaseKernel_le_pi η (-y) y r
  by_cases hin : r ∈ Ioc (-y) y
  · have ha : 0 ≤ y + r := by linarith [hin.1]
    have hb : 0 ≤ y - r := by linarith [hin.2]
    rw [abs_of_nonneg ha] at hr
    rw [abs_of_nonneg hb] at hyr
    have h1 := arctan_distance_lower hη hh hr
    have h2 := arctan_distance_lower hη hh hyr
    rw [windowError, indicator_of_mem hin, abs_of_nonpos (sub_nonpos.mpr hK1)]
    unfold intervalPhaseKernel
    rw [show -y - r = -(y + r) by ring, neg_div, Real.arctan_neg]
    linarith
  · rw [windowError, indicator_of_notMem hin, sub_zero, abs_of_nonneg hK0]
    by_cases hra : r ≤ -y
    · rw [abs_of_nonpos (by linarith : y + r ≤ 0)] at hr
      have h1 := arctan_distance_lower hη hh hr
      rw [neg_div, Real.arctan_neg] at h1
      unfold intervalPhaseKernel
      rw [show -y - r = -(y + r) by ring, neg_div, Real.arctan_neg]
      linarith [Real.arctan_lt_pi_div_two ((y - r) / η), div_pos hη hh]
    · have hrb : y < r := by
        by_contra h
        exact hin ⟨lt_of_not_ge hra, le_of_not_gt h⟩
      rw [abs_of_neg (sub_neg.mpr hrb)] at hyr
      have h1 := arctan_distance_lower hη hh hyr
      rw [neg_div, Real.arctan_neg] at h1
      unfold intervalPhaseKernel
      linarith [Real.neg_pi_div_two_lt_arctan ((-y - r) / η), div_pos hη hh]

private theorem windowError_le_far {η Y y r : ℝ} (hη : 0 < η) (hY : 1 ≤ Y)
    (hy : y ∈ Ioc Y (2 * Y)) (hr : 4 * Y < |r|) :
    windowError η y r ≤ 32 * η * Y * (1 + r ^ 2)⁻¹ := by
  have hy0 : 0 ≤ y := by linarith [hy.1]
  have hout : r ∉ Ioc (-y) y := by
    intro hin
    have : |r| ≤ y := abs_le.mpr ⟨hin.1.le, hin.2⟩
    linarith [hy.2]
  rw [windowError, indicator_of_notMem hout, sub_zero,
    abs_of_nonneg (intervalPhaseKernel_nonneg hη (by linarith) r)]
  have hden : 0 < 1 + r ^ 2 := by positivity
  have hr1 : 1 ≤ r ^ 2 := by
    have : 1 ≤ |r| := by linarith
    nlinarith [sq_abs r]
  have hbound : ∀ t ∈ Icc (-y) y,
      η / (η ^ 2 + (r - t) ^ 2) ≤ 8 * η / (1 + r ^ 2) := by
    intro t ht
    have htY : |t| ≤ 2 * Y := (abs_le.mpr ht).trans hy.2
    have hrt : |r| ≤ |r - t| + |t| := by simpa using abs_add_le (r - t) t
    have hhalf : |r| ≤ 2 * |r - t| := by linarith
    have hsq : r ^ 2 ≤ 4 * (r - t) ^ 2 := by
      have := (sq_le_sq₀ (abs_nonneg r) (by positivity : 0 ≤ 2 * |r - t|)).mpr hhalf
      norm_num [mul_pow, sq_abs] at this ⊢
      exact this
    have hd : 1 + r ^ 2 ≤ 8 * (η ^ 2 + (r - t) ^ 2) := by nlinarith [sq_nonneg η]
    rw [div_le_div_iff₀ (by positivity : 0 < η ^ 2 + (r - t) ^ 2) hden]
    nlinarith [mul_le_mul_of_nonneg_left hd hη.le]
  have hint : IntervalIntegrable (fun t : ℝ => η / (η ^ 2 + (r - t) ^ 2)) volume (-y) y :=
    (continuous_const.div (by fun_prop) (fun t => by positivity) :
      Continuous fun t : ℝ => η / (η ^ 2 + (r - t) ^ 2)).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on (show -y ≤ y by linarith)
    hint intervalIntegrable_const hbound
  rw [integral_poisson_interval hη, intervalIntegral.integral_const] at h
  simp only [smul_eq_mul] at h
  refine h.trans ?_
  rw [div_eq_mul_inv]
  nlinarith [mul_le_mul_of_nonneg_right hy.2
    (show 0 ≤ 16 * η * (1 + r ^ 2)⁻¹ by positivity)]

private theorem integrableOn_windowError {η Y : ℝ} (hη : 0 < η) (hY : 1 ≤ Y)
    (r : ℝ) : IntegrableOn (fun y => windowError η y r) (Ioc Y (2 * Y)) := by
  refine (integrableOn_const (measure_Ioc_lt_top.ne) :
    IntegrableOn (fun _ : ℝ => Real.pi) (Ioc Y (2 * Y))).mono'
    ((measurable_windowError η).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  change ‖windowError η y r‖ ≤ Real.pi
  rw [Real.norm_of_nonneg (show 0 ≤ windowError η y r from abs_nonneg _)]
  exact windowError_le_pi hη (by linarith [hy.1]) r

private theorem integral_windowError_le_near {η h Y : ℝ} (hη : 0 < η) (hh : 0 < h)
    (hY : 1 ≤ Y) (r : ℝ) :
    ∫ y in Ioc Y (2 * Y), windowError η y r ≤ 4 * Real.pi * h + 2 * η * Y / h := by
  let f : ℝ → ℝ := (Icc (r - h) (r + h)).indicator (fun _ => Real.pi)
  let g : ℝ → ℝ := (Icc (-r - h) (-r + h)).indicator (fun _ => Real.pi)
  have hfi : Integrable f := (integrableOn_const (measure_Icc_lt_top.ne)).integrable_indicator
    measurableSet_Icc
  have hgi : Integrable g := (integrableOn_const (measure_Icc_lt_top.ne)).integrable_indicator
    measurableSet_Icc
  have hf0 : ∀ y, 0 ≤ f y := indicator_nonneg (fun _ _ => Real.pi_pos.le)
  have hg0 : ∀ y, 0 ≤ g y := indicator_nonneg (fun _ _ => Real.pi_pos.le)
  have hf : (∫ y in Ioc Y (2 * Y), f y) ≤ 2 * h * Real.pi := by
    have hb := integral_mono_measure (Measure.restrict_le_self (s := Ioc Y (2 * Y)))
      (Eventually.of_forall hf0) hfi
    have he : (r + h) - (r - h) = 2 * h := by ring
    simpa [f, integral_indicator_const, Real.volume_real_Icc_of_le (by linarith : r - h ≤ r + h),
      smul_eq_mul, he] using hb
  have hg : (∫ y in Ioc Y (2 * Y), g y) ≤ 2 * h * Real.pi := by
    have h' := integral_mono_measure (Measure.restrict_le_self (s := Ioc Y (2 * Y)))
      (Eventually.of_forall hg0) hgi
    have he : (-r + h) - (-r - h) = 2 * h := by ring
    simpa [g, integral_indicator_const,
      Real.volume_real_Icc_of_le (by linarith : -r - h ≤ -r + h), smul_eq_mul, he] using h'
  have hbound : ∀ y ∈ Ioc Y (2 * Y), windowError η y r ≤ f y + g y + 2 * η / h := by
    intro y hy
    have hy0 : 0 ≤ y := by linarith [hy.1]
    by_cases hp : y ∈ Icc (r - h) (r + h)
    · have : f y = Real.pi := indicator_of_mem hp _
      linarith [windowError_le_pi hη hy0 r, hg0 y,
        show 0 ≤ 2 * η / h by positivity]
    by_cases hn : y ∈ Icc (-r - h) (-r + h)
    · have : g y = Real.pi := indicator_of_mem hn _
      linarith [windowError_le_pi hη hy0 r, hf0 y,
        show 0 ≤ 2 * η / h by positivity]
    have hp' : h ≤ |y - r| := by
      by_contra ha
      have ha := abs_lt.mp (lt_of_not_ge ha)
      exact hp ⟨by linarith [ha.1], by linarith [ha.2]⟩
    have hn' : h ≤ |y + r| := by
      by_contra ha
      have ha := abs_lt.mp (lt_of_not_ge ha)
      exact hn ⟨by linarith [ha.1], by linarith [ha.2]⟩
    linarith [windowError_le_endpoint hη hh hy0 hn' hp', hf0 y, hg0 y]
  have hi : IntegrableOn (fun _ : ℝ => 2 * η / h) (Ioc Y (2 * Y)) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hb := setIntegral_mono_on (integrableOn_windowError hη hY r)
    ((hfi.integrableOn.add hgi.integrableOn).add hi) measurableSet_Ioc hbound
  simp only [Pi.add_apply] at hb
  have hfg : IntegrableOn (fun y => f y + g y) (Ioc Y (2 * Y)) :=
    hfi.integrableOn.add hgi.integrableOn
  rw [integral_add hfg hi,
    integral_add hfi.integrableOn hgi.integrableOn, setIntegral_const,
    Real.volume_real_Ioc, smul_eq_mul, show 2 * Y - Y = Y by ring] at hb
  have hY0 : 0 ≤ Y := by linarith
  rw [max_eq_left hY0] at hb
  rw [show Y * (2 * η / h) = 2 * η * Y / h by ring] at hb
  nlinarith

private theorem integral_windowError_le_weight {η h Y : ℝ} (hη : 0 < η) (hh : 0 < h)
    (hY : 1 ≤ Y) (r : ℝ) :
    ∫ y in Ioc Y (2 * Y), windowError η y r ≤
      ((4 * Real.pi * h + 2 * η * Y / h) * (1 + 16 * Y ^ 2) + 32 * η * Y ^ 2) *
        (1 + r ^ 2)⁻¹ := by
  have hw : 0 < 1 + r ^ 2 := by positivity
  have hA : 0 ≤ 4 * Real.pi * h + 2 * η * Y / h := by positivity
  by_cases hr : |r| ≤ 4 * Y
  · have hs : 1 + r ^ 2 ≤ 1 + 16 * Y ^ 2 := by
      have := (sq_le_sq₀ (abs_nonneg r) (by positivity : 0 ≤ 4 * Y)).mpr hr
      norm_num [sq_abs, mul_pow] at this
      linarith
    refine (integral_windowError_le_near hη hh hY r).trans ?_
    rw [← div_eq_mul_inv, le_div_iff₀ hw]
    nlinarith [mul_le_mul_of_nonneg_left hs hA]
  · have hr' : 4 * Y < |r| := lt_of_not_ge hr
    have hc : IntegrableOn (fun _ : ℝ => 32 * η * Y * (1 + r ^ 2)⁻¹)
        (Ioc Y (2 * Y)) := integrableOn_const measure_Ioc_lt_top.ne
    have hb := setIntegral_mono_on (integrableOn_windowError hη hY r) hc measurableSet_Ioc
      (fun y hy => windowError_le_far hη hY hy hr')
    rw [setIntegral_const, Real.volume_real_Ioc, smul_eq_mul,
      show 2 * Y - Y = Y by ring, max_eq_left (by linarith : 0 ≤ Y)] at hb
    refine hb.trans ?_
    have hx : 0 ≤ (4 * Real.pi * h + 2 * η * Y / h) * (1 + 16 * Y ^ 2) *
        (1 + r ^ 2)⁻¹ := by positivity
    nlinarith

private theorem integrable_windowError_prod {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {η h Y : ℝ} (hη : 0 < η) (hh : 0 < h) (hY : 1 ≤ Y) :
    Integrable (fun p : ℝ × ℝ => windowError η p.2 p.1)
      ((boundaryMeasure hW).prod (volume.restrict (Ioc Y (2 * Y)))) := by
  haveI := sFinite_boundaryMeasure hW
  have hm := (measurable_windowError η).comp measurable_swap
  refine (integrable_prod_iff hm.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · exact Eventually.of_forall (integrableOn_windowError hη hY)
  · let B := (4 * Real.pi * h + 2 * η * Y / h) * (1 + 16 * Y ^ 2) + 32 * η * Y ^ 2
    refine ((integrable_inv_one_add_sq hW).const_mul B).mono'
      hm.norm.aestronglyMeasurable.integral_prod_right' ?_
    exact Eventually.of_forall fun r => by
      change ‖∫ y in Ioc Y (2 * Y), ‖windowError η y r‖‖ ≤ B * (1 + r ^ 2)⁻¹
      have hn : (fun y => ‖windowError η y r‖) = (fun y => windowError η y r) := by
        funext y
        exact Real.norm_of_nonneg (abs_nonneg _)
      have hnonneg : 0 ≤ ∫ y in Ioc Y (2 * Y), windowError η y r :=
        integral_nonneg fun _ => abs_nonneg _
      rw [hn, Real.norm_of_nonneg hnonneg]
      exact integral_windowError_le_weight hη hh hY r

private theorem integral_integral_windowError_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {η h Y : ℝ} (hη : 0 < η) (hh : 0 < h) (hY : 1 ≤ Y) :
    ∫ y in Ioc Y (2 * Y), ∫ r, windowError η y r ∂boundaryMeasure hW ≤
      ((4 * Real.pi * h + 2 * η * Y / h) * (1 + 16 * Y ^ 2) + 32 * η * Y ^ 2) *
        ∫ r, (1 + r ^ 2)⁻¹ ∂boundaryMeasure hW := by
  haveI := sFinite_boundaryMeasure hW
  have hi := integrable_windowError_prod hW hη hh hY
  rw [← integral_integral_swap hi]
  have hb := integral_mono hi.integral_prod_left
    ((integrable_inv_one_add_sq hW).const_mul
      ((4 * Real.pi * h + 2 * η * Y / h) * (1 + 16 * Y ^ 2) + 32 * η * Y ^ 2))
    (integral_windowError_le_weight hη hh hY)
  simpa only [integral_const_mul] using hb

private theorem norm_exp_real_sub_le (a b : ℝ) :
    ‖cexp ((a : ℂ) * I) - cexp ((b : ℂ) * I)‖ ≤ |a - b| := by
  have hid : cexp ((a : ℂ) * I) - cexp ((b : ℂ) * I) =
      (cexp (I * ((a - b : ℝ) : ℂ)) - 1) * cexp ((b : ℂ) * I) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hid, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |Real.sin ((a - b) / 2)| ≤ 2 * |(a - b) / 2| :=
      mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = |a - b| := by rw [abs_div]; norm_num; ring

/-- The actual normalized reflection phase at positive distance from the critical line. -/
def regularizedPhase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (η y : ℝ) : ℂ :=
  cexp (((2 * (sourcePrimitive hW (tracePoint η y)).im : ℝ) : ℂ) * I)

private theorem continuous_regularizedPhase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {η : ℝ} (hη : 0 < η) : Continuous (regularizedPhase hW η) := by
  have hc : Continuous (fun y => sourcePrimitive hW (tracePoint η y)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (hasDerivAt_sourcePrimitive hW (s := tracePoint η y)
      (by simp [tracePoint]; linarith)).continuousAt.comp (by unfold tracePoint; fun_prop)
  unfold regularizedPhase
  fun_prop

private theorem norm_regularizedPhase_sub_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {η y : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hy : 0 ≤ y) :
    ‖regularizedPhase hW η y - canonicalPhase hW y‖ ≤
      ∫ r, windowError η y r ∂boundaryMeasure hW := by
  have hfin : boundaryMeasure hW (Ioc (-y) y) ≠ ∞ :=
    ne_top_of_le_ne_top (boundaryMeasure_Ioo_ne_top hW (-y - 1) (y + 1))
      (measure_mono fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩)
  have hind : Integrable ((Ioc (-y) y).indicator (fun _ => Real.pi)) (boundaryMeasure hW) :=
    (integrableOn_const hfin).integrable_indicator measurableSet_Ioc
  have hker : Integrable (intervalPhaseKernel η (-y) y) (boundaryMeasure hW) := by
    refine ((integrable_inv_one_add_sq hW).const_mul
      (Real.pi * (1 + 4 * (|-y| + |y| + 1) ^ 2) + 8 * (y - -y))).mono'
      (continuous_intervalPhaseKernel η (-y) y).aestronglyMeasurable ?_
    exact Eventually.of_forall fun r => by
      rw [Real.norm_of_nonneg (intervalPhaseKernel_nonneg hη (by linarith) r)]
      exact intervalPhaseKernel_le_weight hη hη1 (by linarith) r
  refine (norm_exp_real_sub_le _ _).trans ?_
  rw [two_mul_im_sourcePrimitive hW hη hy]
  simp only [tracePoint]
  rw [setIntegral_re_weilContinuation_interval hW hη (by linarith)]
  have hsharp : Real.pi * (boundaryMeasure hW).real (Ioc (-y) y) =
      ∫ r, (Ioc (-y) y).indicator (fun _ => Real.pi) r ∂boundaryMeasure hW := by
    rw [integral_indicator_const _ measurableSet_Ioc, smul_eq_mul, mul_comm]
  rw [hsharp, ← integral_sub hker hind]
  simpa only [Real.norm_eq_abs, windowError] using norm_integral_le_integral_norm
    (fun r => intervalPhaseKernel η (-y) y r - (Ioc (-y) y).indicator (fun _ => Real.pi) r)

/-- Full-source dyadic phase regularization; neither atomicity nor edge continuity is assumed. -/
theorem integral_regularizedPhase_sub_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {η h Y : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hh : 0 < h) (hY : 1 ≤ Y) :
    ∫ y in Ioc Y (2 * Y), ‖regularizedPhase hW η y - canonicalPhase hW y‖ ≤
      ((4 * Real.pi * h + 2 * η * Y / h) * (1 + 16 * Y ^ 2) + 32 * η * Y ^ 2) *
        ∫ r, (1 + r ^ 2)⁻¹ ∂boundaryMeasure hW := by
  haveI := sFinite_boundaryMeasure hW
  have hi : IntegrableOn (fun y => ∫ r, windowError η y r ∂boundaryMeasure hW)
      (Ioc Y (2 * Y)) :=
    (integrable_windowError_prod hW hη hh hY).swap.integral_prod_left
  have hm : Measurable (fun y => ‖regularizedPhase hW η y - canonicalPhase hW y‖) :=
    ((continuous_regularizedPhase hW hη).measurable.sub (measurable_canonicalPhase hW)).norm
  have hbound : ∀ᵐ y ∂volume.restrict (Ioc Y (2 * Y)),
      ‖regularizedPhase hW η y - canonicalPhase hW y‖ ≤
        ∫ r, windowError η y r ∂boundaryMeasure hW := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact norm_regularizedPhase_sub_le hW hη hη1 (by linarith [hy.1])
  have hf : IntegrableOn (fun y => ‖regularizedPhase hW η y - canonicalPhase hW y‖)
      (Ioc Y (2 * Y)) := by
    apply hi.mono' hm.aestronglyMeasurable
    simpa only [norm_norm] using hbound
  exact (integral_mono_ae hf hi hbound).trans (integral_integral_windowError_le hW hη hh hY)

/-- At the explicit width `Y⁻⁸`, full canonical phase has a source-only `O(Y⁻¹)`
dyadic regularization error. This does not assert that either phase is constant. -/
theorem exists_integral_regularizedPhase_sub_le_inv {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 1 ≤ Y →
      ∫ y in Ioc Y (2 * Y),
        ‖regularizedPhase hW (Y ^ 8)⁻¹ y - canonicalPhase hW y‖ ≤ C / Y := by
  let W : ℝ := ∫ r, (1 + r ^ 2)⁻¹ ∂boundaryMeasure hW
  have hW0 : 0 ≤ W := integral_nonneg fun _ => by positivity
  refine ⟨(68 * Real.pi + 66) * W, by positivity, fun Y hY => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hη : 0 < (Y ^ 8)⁻¹ := by positivity
  have hη1 : (Y ^ 8)⁻¹ ≤ 1 := (inv_le_one₀ (pow_pos hY0 8)).2 (one_le_pow₀ hY)
  have hh : 0 < (Y ^ 3)⁻¹ := by positivity
  have hinv (n : ℕ) (hn : 1 ≤ n) : (Y ^ n)⁻¹ ≤ Y⁻¹ := by
    have hp : Y ≤ Y ^ n := by simpa using pow_le_pow_right₀ hY hn
    simpa only [one_div] using one_div_le_one_div_of_le hY0 hp
  have hid :
      (4 * Real.pi * (Y ^ 3)⁻¹ + 2 * (Y ^ 8)⁻¹ * Y / (Y ^ 3)⁻¹) *
          (1 + 16 * Y ^ 2) + 32 * (Y ^ 8)⁻¹ * Y ^ 2 =
        4 * Real.pi * (Y ^ 3)⁻¹ + 64 * Real.pi * Y⁻¹ +
          2 * (Y ^ 4)⁻¹ + 32 * (Y ^ 2)⁻¹ + 32 * (Y ^ 6)⁻¹ := by
    field_simp
    ring
  have hb :
      (4 * Real.pi * (Y ^ 3)⁻¹ + 2 * (Y ^ 8)⁻¹ * Y / (Y ^ 3)⁻¹) *
          (1 + 16 * Y ^ 2) + 32 * (Y ^ 8)⁻¹ * Y ^ 2 ≤
        (68 * Real.pi + 66) * Y⁻¹ := by
    rw [hid]
    have h3 := mul_le_mul_of_nonneg_left (hinv 3 (by norm_num))
      (show 0 ≤ 4 * Real.pi by positivity)
    linarith [hinv 2 (by norm_num), hinv 4 (by norm_num), hinv 6 (by norm_num)]
  have hi := integral_regularizedPhase_sub_le hW hη hη1 hh hY
  calc
    _ ≤ ((4 * Real.pi * (Y ^ 3)⁻¹ + 2 * (Y ^ 8)⁻¹ * Y / (Y ^ 3)⁻¹) *
          (1 + 16 * Y ^ 2) + 32 * (Y ^ 8)⁻¹ * Y ^ 2) * W := hi
    _ ≤ ((68 * Real.pi + 66) * Y⁻¹) * W := mul_le_mul_of_nonneg_right hb hW0
    _ = ((68 * Real.pi + 66) * W) / Y := by ring

end RHTower.WeilWorkSettledPhase
