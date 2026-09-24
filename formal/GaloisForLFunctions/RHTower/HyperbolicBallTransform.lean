import GaloisForLFunctions.RHTower.HyperbolicBallMeanValue
import GaloisForLFunctions.RHTower.SelbergMaassCurvatureTransport

open MeasureTheory UpperHalfPlane Metric Set

/-!
# Size of the Selberg transform of the ball kernel

The box `|x| ≤ Y/4`, `Y/2 ≤ y ≤ Y`, `Y = cosh R`, lies in the hyperbolic ball `B_R(i)` for `R ≥ 2` and has
hyperbolic area at least `1/4`; on it `y^s ≥ (Y/2)^s`. Hence `∫_{B_R(i)} y^s dμ ≥ (cosh R)^s/16` for
`0 ≤ s ≤ 2` (`ballTransform_lower`): the transform grows like `e^{sR}`.
-/

namespace GaloisForLFunctions.RHTower.HyperbolicBallTransform

/-- The box `|x| ≤ Y/4`, `Y/2 ≤ y ≤ Y` in the plane. -/
def boxC (Y : ℝ) : Set ℂ := {z | |z.re| ≤ Y / 4 ∧ Y / 2 ≤ z.im ∧ z.im ≤ Y}

/-- The same box in the upper half-plane. -/
def box (Y : ℝ) : Set ℍ := {w | |w.re| ≤ Y / 4 ∧ Y / 2 ≤ w.im ∧ w.im ≤ Y}

theorem boxC_eq (Y : ℝ) :
    boxC Y = Complex.measurableEquivRealProd ⁻¹' (Icc (-(Y / 4)) (Y / 4) ×ˢ Icc (Y / 2) Y) := by
  ext z
  simp only [boxC, abs_le, mem_setOf_eq, mem_preimage, Complex.measurableEquivRealProd_apply,
    mem_prod, mem_Icc]

theorem boxC_measurable (Y : ℝ) : MeasurableSet (boxC Y) := by
  rw [boxC_eq]
  exact (measurableSet_Icc.prod measurableSet_Icc).preimage Complex.measurableEquivRealProd.measurable

theorem box_measurable (Y : ℝ) : MeasurableSet (box Y) := by
  have : box Y = UpperHalfPlane.coe ⁻¹' boxC Y := by ext w; rfl
  rw [this]
  exact (boxC_measurable Y).preimage measurable_coe

theorem volume_boxC {Y : ℝ} (hY : 0 ≤ Y) : (volume (boxC Y)).toReal = Y ^ 2 / 4 := by
  rw [boxC_eq, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Icc, Real.volume_Icc, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  ring

theorem exp_div_two_le_cosh (R : ℝ) : Real.exp R / 2 ≤ Real.cosh R := by
  rw [Real.cosh_eq]; have := Real.exp_pos (-R); linarith

theorem two_le_cosh {R : ℝ} (hR : 2 ≤ R) : 2 ≤ Real.cosh R := by
  have h1 := exp_div_two_le_cosh R
  have h2 := Real.quadratic_le_exp_of_nonneg (show 0 ≤ R by linarith)
  nlinarith

theorem box_subset_closedBall {R : ℝ} (hR : 2 ≤ R) : box (Real.cosh R) ⊆ closedBall I R := by
  set Y := Real.cosh R
  have hY : 2 ≤ Y := two_le_cosh hR
  intro w ⟨hx, hy1, hy2⟩
  rw [mem_closedBall]
  have hdist : 0 ≤ dist w I := dist_nonneg
  have hRnn : 0 ≤ R := by linarith
  have hcosh : Real.cosh (dist w I) ≤ Y := by
    rw [cosh_dist]
    have hwi : 0 < w.im := w.im_pos
    simp only [UpperHalfPlane.I_im, mul_one]
    rw [← le_sub_iff_add_le', div_le_iff₀ (by positivity)]
    have hd : dist (w : ℂ) (I : ℂ) ^ 2 = w.re ^ 2 + (w.im - 1) ^ 2 := by
      rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
      simp; ring
    rw [hd]
    have hx2 : w.re ^ 2 ≤ Y ^ 2 / 16 := by
      have := abs_le.mp hx
      nlinarith
    nlinarith
  have := Real.cosh_le_cosh.mp hcosh
  rwa [abs_of_nonneg hdist, abs_of_nonneg hRnn] at this

open SelbergMaassCurvatureTransport in
/-- The box has hyperbolic area at least `1/4`. -/
theorem measureReal_box {Y : ℝ} (hY : 0 < Y) : 1 / 4 ≤ (volume : Measure ℍ).real (box Y) := by
  set F : ℂ → ℝ := (boxC Y).indicator (fun z => 1 / z.im ^ 2)
  have hF : ∀ w : ℍ, (box Y).indicator (fun _ => (1 : ℝ)) w = w.im ^ 2 * F w := by
    intro w
    by_cases hw : w ∈ box Y
    · have hwC : (w : ℂ) ∈ boxC Y := hw
      rw [indicator_of_mem hw]
      simp only [F, indicator_of_mem hwC]
      have : (w : ℂ).im = w.im := rfl
      rw [this]; field_simp [w.im_pos.ne']
    · have hwC : (w : ℂ) ∉ boxC Y := hw
      rw [indicator_of_notMem hw]
      simp only [F, indicator_of_notMem hwC, mul_zero]
  have h1 : (volume : Measure ℍ).real (box Y) = ∫ z in {z : ℂ | 0 < z.im}, F z := by
    rw [← integral_height_sq_chart, ← integral_indicator_one (box_measurable Y)]
    exact integral_congr_ae (Filter.Eventually.of_forall hF)
  have hsub : boxC Y ⊆ {z : ℂ | 0 < z.im} := fun z hz => by
    have := hz.2.1; show 0 < z.im; linarith
  have hlow : ∀ z, (boxC Y).indicator (fun _ => 1 / Y ^ 2) z ≤ F z := by
    intro z
    by_cases hz : z ∈ boxC Y
    · rw [indicator_of_mem hz]
      simp only [F, indicator_of_mem hz]
      have hzi : 0 < z.im := hsub hz
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hzi.le hz.2.2 2)
    · rw [indicator_of_notMem hz]
      simp only [F, indicator_of_notMem hz, le_refl]
  have hfin : volume (boxC Y) < ⊤ := by
    rw [boxC_eq, Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
      Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hiF : IntegrableOn F {z : ℂ | 0 < z.im} := by
    apply Integrable.integrableOn
    rw [integrable_indicator_iff (boxC_measurable Y)]
    refine Measure.integrableOn_of_bounded (M := 4 / Y ^ 2) hfin.ne ?_ ?_
    · exact (measurable_const.div ((Complex.measurable_im.pow_const 2))).aestronglyMeasurable
    · rw [ae_restrict_iff' (boxC_measurable Y)]
      refine Filter.Eventually.of_forall (fun z hz => ?_)
      have hzi : Y / 2 ≤ z.im := hz.2.1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
      nlinarith
  have hiC : IntegrableOn ((boxC Y).indicator (fun _ => 1 / Y ^ 2)) {z : ℂ | 0 < z.im} := by
    apply Integrable.integrableOn
    rw [integrable_indicator_iff (boxC_measurable Y)]
    exact integrableOn_const hfin.ne
  have h2 := setIntegral_mono hiC hiF hlow
  rw [integral_indicator (boxC_measurable Y), Measure.restrict_restrict (boxC_measurable Y),
    inter_eq_self_of_subset_left hsub, setIntegral_const, smul_eq_mul, measureReal_def,
    volume_boxC hY.le] at h2
  rw [h1]
  calc (1 / 4 : ℝ) = Y ^ 2 / 4 * (1 / Y ^ 2) := by field_simp
    _ ≤ _ := h2

/-- **Lower bound for the Selberg transform of the ball kernel.** For `R ≥ 2` and `0 ≤ s ≤ 2`,
`∫_{B_R(i)} (Im w)^s dμ ≥ (cosh R)^s / 16`. -/
theorem ballTransform_lower {R : ℝ} (hR : 2 ≤ R) {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    Real.cosh R ^ s / 16 ≤ ∫ w in closedBall I R, w.im ^ s := by
  set Y := Real.cosh R
  have hY : 2 ≤ Y := two_le_cosh hR
  have hcont : Continuous fun w : ℍ => w.im ^ s :=
    (continuous_im.rpow_const (fun _ => Or.inr hs0))
  have hball : IntegrableOn (fun w : ℍ => w.im ^ s) (closedBall I R) :=
    hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hboxI : IntegrableOn (fun w : ℍ => w.im ^ s) (box Y) := hball.mono_set (box_subset_closedBall hR)
  have h1 : (∫ w in box Y, w.im ^ s) ≤ ∫ w in closedBall I R, w.im ^ s :=
    setIntegral_mono_set hball
      (Filter.Eventually.of_forall (fun w => Real.rpow_nonneg w.im_pos.le s))
      (Filter.Eventually.of_forall (box_subset_closedBall hR))
  have hfin : (volume : Measure ℍ) (box Y) < ⊤ :=
    (measure_mono (box_subset_closedBall hR)).trans_lt (isCompact_closedBall _ _).measure_lt_top
  have h2 : (∫ w in box Y, (Y / 2) ^ s) ≤ ∫ w in box Y, w.im ^ s := by
    apply setIntegral_mono_on (integrableOn_const hfin.ne) hboxI (box_measurable Y)
    intro w hw
    exact Real.rpow_le_rpow (by linarith) hw.2.1 hs0
  rw [setIntegral_const, smul_eq_mul] at h2
  have h3 := measureReal_box (show 0 < Y by linarith)
  have h4 : Y ^ s / 4 ≤ (Y / 2) ^ s := by
    rw [Real.div_rpow (by linarith) (by norm_num)]
    have h2s : (2 : ℝ) ^ s ≤ 4 := by
      calc (2 : ℝ) ^ s ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs2
        _ = 4 := by norm_num
    have hpos : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    rw [div_le_div_iff₀ (by norm_num) hpos]
    exact mul_le_mul_of_nonneg_left h2s (Real.rpow_nonneg (by linarith) s)
  have hYs : 0 ≤ Y ^ s := Real.rpow_nonneg (by linarith) s
  calc Y ^ s / 16 = (1 / 4) * (Y ^ s / 4) := by ring
    _ ≤ (volume : Measure ℍ).real (box Y) * (Y / 2) ^ s :=
        mul_le_mul h3 h4 (by positivity) (by positivity)
    _ ≤ _ := h2.trans h1

end GaloisForLFunctions.RHTower.HyperbolicBallTransform
