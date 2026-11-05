import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicFormHasItsMixedJumpPairing

/-!
# The logarithmic form detects interval length

Translations longer than the source interval have disjoint supports. Their
exact loss is twice the source mass. Integrating just those jumps up to
unit length gives the sharp leading lower bound `log(1/h)`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

private theorem translation_inner_eq_zero {lo h t : ℝ} (ht : h < t) (f : RealLineL2)
    (hf : ∀ᵐ x ∂volume, x ∉ Icc lo (lo+h) → f x = 0) :
    inner ℂ (logTranslationCLM t f) f = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  have hs := (MellinL2.realTranslation_measurePreserving t).quasiMeasurePreserving.ae hf
  filter_upwards [hf, hs, logarithmicTranslation_coeFn t f] with x hx hs he
  change x+t ∉ Icc lo (lo+h) → f (x+t) = 0 at hs
  change inner ℂ ((logTranslationCLM t f) x) (f x) = 0
  by_cases hm : x ∈ Icc lo (lo+h)
  · have hn : x+t ∉ Icc lo (lo+h) := by
      intro hp
      linarith only [hm.1, hp.2, ht]
    rw [he, hs hn, inner_zero_left]
  · rw [hx hm, inner_zero_right]

/-- Translation beyond the support width has loss exactly twice the L² mass. -/
theorem logarithmic_translation_loss_of_interval_support {lo h t : ℝ}
    (ht : h < t) (f : RealLineL2)
    (hf : ∀ᵐ x ∂volume, x ∉ Icc lo (lo+h) → f x = 0) :
    ‖logTranslationCLM t f-f‖^2 = 2*‖f‖^2 := by
  have hi := translation_inner_eq_zero ht f hf
  have hn : ‖logTranslationCLM t f‖ = ‖f‖ :=
    (MellinL2.additiveTranslationUnitary t).norm_map f
  rw [norm_sub_sq (𝕜 := ℂ), hi, hn]
  simp only [map_zero, mul_zero, sub_zero]
  ring

/-- The real diagonal logarithmic form is mass plus its nonnegative jump integral. -/
theorem logarithmicFullForm_self_re {f : RealLineL2} (hf : HasLogarithmicEnergy f) :
    (logarithmicFullForm f f).re = ‖f‖^2 +
      ∫ t in Ioi (0 : ℝ), logReferenceLevyDensity t * ‖logTranslationCLM t f-f‖^2 := by
  rw [logarithmicFullForm_eq_inner_add_jump hf hf]
  have he : (fun t : ℝ => (logReferenceLevyDensity t : ℂ) *
      inner ℂ (logTranslationCLM t f-f) (logTranslationCLM t f-f)) =
      fun t => ((logReferenceLevyDensity t * ‖logTranslationCLM t f-f‖^2 : ℝ) : ℂ) := by
    funext t
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  rw [he, integral_complex_ofReal, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  norm_cast

private theorem logarithmic_truncated_tail_lower {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    Real.log (1/h)-1+h ≤ 2*∫ t in h..1, logReferenceLevyDensity t := by
  have hcont : ContinuousOn logReferenceLevyDensity (uIcc h 1) := by
    unfold logReferenceLevyDensity
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    rw [uIcc_of_le hh1] at ht
    exact mul_ne_zero (by norm_num) (hh.trans_le ht.1).ne'
  have hi : IntervalIntegrable logReferenceLevyDensity volume h 1 := hcont.intervalIntegrable
  have hr : IntervalIntegrable (fun t : ℝ => 1/t) volume h 1 := by
    apply (ContinuousOn.div continuousOn_const continuousOn_id ?_).intervalIntegrable
    intro t ht
    rw [uIcc_of_le hh1] at ht
    exact (hh.trans_le ht.1).ne'
  have h := intervalIntegral.integral_mono_on hh1
    (hr.sub (continuous_const.intervalIntegrable _ _)) (hi.const_mul 2) (fun t ht => by
      have ht0 := hh.trans_le ht.1
      change 1/t-1 ≤ 2*logReferenceLevyDensity t
      unfold logReferenceLevyDensity
      have he := Real.add_one_le_exp (-t)
      apply (mul_le_mul_iff_of_pos_right ht0).mp
      field_simp [ht0.ne']
      linarith only [he])
  rw [intervalIntegral.integral_sub hr (continuous_const.intervalIntegrable _ _),
    integral_one_div_of_pos hh zero_lt_one, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul] at h
  simp only [smul_eq_mul, mul_one] at h
  linarith only [h]

/-- A source supported in an interval of width `h≤1` pays at least `log(1/h)` times its mass. -/
theorem logarithmicFullForm_ge_log_inverse_width {lo h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (f : RealLineL2) (hf : HasLogarithmicEnergy f)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc lo (lo+h) → f x = 0) :
    Real.log (1/h)*‖f‖^2 ≤ (logarithmicFullForm f f).re := by
  let E : ℝ → ℝ := fun t => logReferenceLevyDensity t * ‖logTranslationCLM t f-f‖^2
  have hi : IntegrableOn E (Ioi 0) := (hasLogarithmicEnergy_iff_integrable_jump f).mp hf
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] E := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (logReferenceLevyDensity_nonneg ht.le) (sq_nonneg _)
  have hpart : (∫ t in Ioc h 1, E t) ≤ ∫ t in Ioi (0 : ℝ), E t := by
    apply setIntegral_mono_set hi hnonneg
    exact Eventually.of_forall fun t ht => hh.trans ht.1
  have he : (∫ t in Ioc h 1, E t) = (2*∫ t in h..1, logReferenceLevyDensity t)*‖f‖^2 := by
    rw [intervalIntegral.integral_of_le hh1, ← integral_const_mul, ← integral_mul_const]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only [E]
    rw [logarithmic_translation_loss_of_interval_support ht.1 f hs]
    ring
  rw [he] at hpart
  have htail := mul_le_mul_of_nonneg_right (logarithmic_truncated_tail_lower hh hh1) (sq_nonneg ‖f‖)
  rw [logarithmicFullForm_self_re hf]
  change _ ≤ ‖f‖^2 + ∫ t in Ioi (0 : ℝ), E t
  nlinarith only [htail, hpart, mul_nonneg hh.le (sq_nonneg ‖f‖)]

/-- The literal constant interval source as an actual L² vector. -/
def logarithmicIntervalSource (lo hi : ℝ) : RealLineL2 :=
  indicatorConstLp 2 (s := Ioc lo hi) measurableSet_Ioc
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (1 : ℂ)

theorem logarithmicIntervalSource_coeFn (lo hi : ℝ) :
    (logarithmicIntervalSource lo hi : ℝ → ℂ) =ᵐ[volume]
      (Ioc lo hi).indicator (fun _ => (1 : ℂ)) := indicatorConstLp_coeFn

theorem norm_logarithmicIntervalSource_sq {lo hi : ℝ} (hle : lo ≤ hi) :
    ‖logarithmicIntervalSource lo hi‖^2 = hi-lo := by
  have h := L2.inner_indicatorConstLp_one_indicatorConstLp_one (𝕜 := ℂ)
    (μ := (volume : Measure ℝ)) (s := Ioc lo hi) (t := Ioc lo hi)
    measurableSet_Ioc measurableSet_Ioc
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  change inner ℂ (logarithmicIntervalSource lo hi) (logarithmicIntervalSource lo hi) = _ at h
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at h
  have hr := congrArg Complex.re h
  simpa only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re, inter_self,
    Real.volume_real_Ioc_of_le hle] using hr

theorem logarithmicIntervalSource_translation (lo hi t : ℝ) :
    logTranslationCLM t (logarithmicIntervalSource lo hi) =
      logarithmicIntervalSource (lo-t) (hi-t) := by
  apply Lp.ext
  have hs := (logarithmicIntervalSource_coeFn lo hi).comp_tendsto
    (MellinL2.realTranslation_measurePreserving t).quasiMeasurePreserving.tendsto_ae
  filter_upwards [logarithmicTranslation_coeFn t (logarithmicIntervalSource lo hi), hs,
    logarithmicIntervalSource_coeFn (lo-t) (hi-t)] with x hx hs he
  change logarithmicIntervalSource lo hi (x+t) =
    (Ioc lo hi).indicator (fun _ => (1 : ℂ)) (x+t) at hs
  rw [hx, hs, he]
  have hm : x+t ∈ Ioc lo hi ↔ x ∈ Ioc (lo-t) (hi-t) := by
    constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]
  simp only [Set.indicator_apply, hm]

/-- A constant interval profile has the exact loss `2 min(t,h)` at positive translation. -/
theorem logarithmicIntervalSource_translation_loss {h t : ℝ} (hh : 0 ≤ h) (ht : 0 ≤ t) :
    ‖logTranslationCLM t (logarithmicIntervalSource 0 h)-logarithmicIntervalSource 0 h‖^2 =
      2*min t h := by
  have hinter : Ioc (-t) (h-t) ∩ Ioc (0 : ℝ) h = Ioc 0 (h-t) := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.2.1, hx.1.2⟩
    · intro hx
      exact ⟨⟨by linarith only [hx.1, ht], hx.2⟩,
        ⟨hx.1, by linarith only [hx.2, ht]⟩⟩
  have hi := L2.inner_indicatorConstLp_one_indicatorConstLp_one (𝕜 := ℂ)
    (μ := (volume : Measure ℝ)) (s := Ioc (-t) (h-t)) (t := Ioc (0 : ℝ) h)
    measurableSet_Ioc measurableSet_Ioc
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  change inner ℂ (logarithmicIntervalSource (-t) (h-t)) (logarithmicIntervalSource 0 h) = _ at hi
  rw [hinter] at hi
  have hnorm : ‖logTranslationCLM t (logarithmicIntervalSource 0 h)‖ =
      ‖logarithmicIntervalSource 0 h‖ := (MellinL2.additiveTranslationUnitary t).norm_map _
  rw [norm_sub_sq (𝕜 := ℂ), hnorm, norm_logarithmicIntervalSource_sq hh, sub_zero,
    logarithmicIntervalSource_translation, zero_sub, hi]
  simp only [RCLike.re_to_complex, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re]
  by_cases hth : t ≤ h
  · rw [Real.volume_real_Ioc_of_le (sub_nonneg.mpr hth), sub_zero, min_eq_left hth]
    ring
  · have hempty : Ioc (0 : ℝ) (h-t) = ∅ := by
      apply Ioc_eq_empty
      linarith only [le_of_not_ge hth]
    rw [hempty, measureReal_empty, min_eq_right (le_of_not_ge hth)]
    ring

private def intervalJump (h t : ℝ) : ℝ := logReferenceLevyDensity t * (2*min t h)

private theorem integrable_intervalJump {h : ℝ} (hh : 0 ≤ h) :
    IntegrableOn (intervalJump h) (Ioi 0) := by
  have he : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    simpa only [neg_mul, one_mul] using integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0
  apply he.mono'
    (measurable_logReferenceLevyDensity.mul (by fun_prop)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change (0 : ℝ) < t at ht
  change ‖logReferenceLevyDensity t * (2*min t h)‖ ≤ Real.exp (-t)
  rw [Real.norm_of_nonneg (mul_nonneg (logReferenceLevyDensity_nonneg ht.le)
    (mul_nonneg (by norm_num) (le_min ht.le hh)))]
  calc
    intervalJump h t ≤ logReferenceLevyDensity t * (2*t) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (min_le_left t h) (by norm_num))
        (logReferenceLevyDensity_nonneg ht.le)
    _ = Real.exp (-t) := by unfold logReferenceLevyDensity; field_simp [ht.ne']

/-- Constant interval profiles lie in the exact logarithmic form domain. -/
theorem hasLogarithmicEnergy_logarithmicIntervalSource {h : ℝ} (hh : 0 ≤ h) :
    HasLogarithmicEnergy (logarithmicIntervalSource 0 h) := by
  rw [hasLogarithmicEnergy_iff_integrable_jump]
  apply (integrable_intervalJump hh).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [logarithmicIntervalSource_translation_loss hh ht.le]
  rfl

private theorem intervalJump_short_le {h : ℝ} (hh : 0 ≤ h) :
    (∫ t in Ioc (0 : ℝ) h, intervalJump h t) ≤ h := by
  have hi : IntegrableOn (intervalJump h) (Ioc (0 : ℝ) h) :=
    (integrable_intervalJump hh).mono_set (fun _ ht => ht.1)
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) h) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  calc
    _ ≤ ∫ t in Ioc (0 : ℝ) h, (1 : ℝ) := by
      apply setIntegral_mono_on hi hc measurableSet_Ioc
      intro t ht
      have he : intervalJump h t = Real.exp (-t) := by
        unfold intervalJump logReferenceLevyDensity
        rw [min_eq_left ht.2]
        field_simp [ht.1.ne']
      rw [he]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.1.le)
    _ = h := by rw [setIntegral_const, Real.volume_real_Ioc_of_le hh]; simp only [sub_zero, smul_eq_mul, mul_one]

private theorem intervalJump_middle_le {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (∫ t in Ioc h 1, intervalJump h t) ≤ h*Real.log (1/h) := by
  have hi : IntegrableOn (intervalJump h) (Ioc h 1) :=
    (integrable_intervalJump hh.le).mono_set (fun _ ht => hh.trans ht.1)
  have hc : ContinuousOn (fun t : ℝ => h/t) (uIcc h 1) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    rw [uIcc_of_le hh1] at ht
    exact (hh.trans_le ht.1).ne'
  have hci : IntervalIntegrable (fun t : ℝ => h/t) volume h 1 := hc.intervalIntegrable
  have hg : IntegrableOn (fun t : ℝ => h/t) (Ioc h 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hh1).mp hci
  calc
    _ ≤ ∫ t in Ioc h 1, h/t := by
      apply setIntegral_mono_on hi hg measurableSet_Ioc
      intro t ht
      have ht0 := hh.trans ht.1
      have he : intervalJump h t = h*Real.exp (-t)/t := by
        unfold intervalJump logReferenceLevyDensity
        rw [min_eq_right ht.1.le]
        ring
      rw [he]
      exact div_le_div_of_nonneg_right
        (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht0.le)) hh.le) ht0.le
    _ = h*Real.log (1/h) := by
      rw [← intervalIntegral.integral_of_le hh1]
      have he : (fun t : ℝ => h/t) = fun t => h*(1/t) := by funext t; ring
      rw [he, intervalIntegral.integral_const_mul, integral_one_div_of_pos hh zero_lt_one]

private theorem intervalJump_remote_le {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ t in Ioi (1 : ℝ), intervalJump h t) ≤ h := by
  have hi : IntegrableOn (intervalJump h) (Ioi (1 : ℝ)) :=
    (integrable_intervalJump hh).mono_set
      (fun (t : ℝ) (ht : t ∈ Ioi (1 : ℝ)) => show t ∈ Ioi (0 : ℝ) from lt_trans (show (0 : ℝ) < 1 from zero_lt_one) ht)
  have he : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 1) := by
    simpa only [neg_mul, one_mul] using integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 1
  have hv : (∫ t in Ioi (1 : ℝ), Real.exp (-t)) = Real.exp (-1) := by
    simpa only [neg_mul, one_mul, neg_neg, div_neg, div_one] using
      integral_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 1
  calc
    _ ≤ ∫ t in Ioi (1 : ℝ), h*Real.exp (-t) := by
      apply setIntegral_mono_on hi (he.const_mul h) measurableSet_Ioi
      intro t ht
      have ht0 := (show (0 : ℝ) < 1 from zero_lt_one).trans ht
      have heq : intervalJump h t = h*Real.exp (-t)/t := by
        unfold intervalJump logReferenceLevyDensity
        rw [min_eq_right (hh1.trans ht.le)]
        ring
      rw [heq]
      exact div_le_self (mul_nonneg hh (Real.exp_pos _).le) ht.le
    _ = h*Real.exp (-1) := by rw [integral_const_mul, hv]
    _ ≤ h := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0)) hh

/-- Constant collar tests attain the leading logarithmic energy with a fixed additive error. -/
theorem logarithmicFullForm_intervalSource_upper {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (logarithmicFullForm (logarithmicIntervalSource 0 h) (logarithmicIntervalSource 0 h)).re ≤
      h*(Real.log (1/h)+3) := by
  have hE := integrable_intervalJump hh.le
  have h01 : IntegrableOn (intervalJump h) (Ioc (0 : ℝ) 1) := hE.mono_set (fun _ ht => ht.1)
  have h0h : IntegrableOn (intervalJump h) (Ioc (0 : ℝ) h) := hE.mono_set (fun _ ht => ht.1)
  have hh1i : IntegrableOn (intervalJump h) (Ioc h 1) := hE.mono_set (fun _ ht => hh.trans ht.1)
  have h1inf : IntegrableOn (intervalJump h) (Ioi (1 : ℝ)) := hE.mono_set
    (fun (t : ℝ) (ht : t ∈ Ioi (1 : ℝ)) => show t ∈ Ioi (0 : ℝ) from lt_trans (show (0 : ℝ) < 1 from zero_lt_one) ht)
  have hs : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext t
    constructor
    · rintro (ht | ht)
      · exact ht.1
      · exact (show (0 : ℝ) < 1 from zero_lt_one).trans ht
    · intro ht
      by_cases ht1 : t ≤ 1
      · exact Or.inl ⟨ht, ht1⟩
      · exact Or.inr (lt_of_not_ge ht1)
  have hd : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by
    apply disjoint_left.mpr
    intro t ht hu
    exact (not_lt.mpr ht.2) hu
  have hsplit : (∫ t in Ioi (0 : ℝ), intervalJump h t) =
      (∫ t in Ioc (0 : ℝ) h, intervalJump h t) +
        (∫ t in Ioc h 1, intervalJump h t) +
          ∫ t in Ioi (1 : ℝ), intervalJump h t := by
    rw [← hs, setIntegral_union hd measurableSet_Ioi h01 h1inf]
    congr 1
    rw [← intervalIntegral.integral_of_le zero_le_one,
      ← intervalIntegral.integral_of_le hh.le, ← intervalIntegral.integral_of_le hh1]
    exact (intervalIntegral.integral_add_adjacent_intervals
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le).mpr h0h)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hh1).mpr hh1i)).symm
  rw [logarithmicFullForm_self_re (hasLogarithmicEnergy_logarithmicIntervalSource hh.le),
    norm_logarithmicIntervalSource_sq hh.le, sub_zero]
  have he : (∫ t in Ioi (0 : ℝ), logReferenceLevyDensity t *
      ‖logTranslationCLM t (logarithmicIntervalSource 0 h)-logarithmicIntervalSource 0 h‖^2) =
      ∫ t in Ioi (0 : ℝ), intervalJump h t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change logReferenceLevyDensity t *
      ‖logTranslationCLM t (logarithmicIntervalSource 0 h)-logarithmicIntervalSource 0 h‖^2 = _
    rw [logarithmicIntervalSource_translation_loss hh.le ht.le]
    rfl
  rw [he, hsplit]
  have hshort := intervalJump_short_le hh.le
  have hmiddle := intervalJump_middle_le hh hh1
  have hremote := intervalJump_remote_le hh.le hh1
  nlinarith only [hshort, hmiddle, hremote]

/-- Translating a constant interval source places it at any prescribed left endpoint. -/
theorem logarithmicIntervalSource_shift (lo h : ℝ) :
    logTranslationCLM (-lo) (logarithmicIntervalSource 0 h) =
      logarithmicIntervalSource lo (lo+h) := by
  simpa only [sub_neg_eq_add, zero_add, add_comm h lo] using
    logarithmicIntervalSource_translation 0 h (-lo)

/-- Constant profiles on arbitrary finite intervals lie in the full energy domain. -/
theorem hasLogarithmicEnergy_logarithmicIntervalSource_at (lo : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    HasLogarithmicEnergy (logarithmicIntervalSource lo (lo+h)) := by
  have he := hasLogarithmicEnergy_translation (-lo)
    (hasLogarithmicEnergy_logarithmicIntervalSource hh)
  rwa [logarithmicIntervalSource_shift] at he

/-- The leading constant-profile energy bound depends only on interval width. -/
theorem logarithmicFullForm_intervalSource_upper_at (lo : ℝ) {h : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) :
    (logarithmicFullForm (logarithmicIntervalSource lo (lo+h))
      (logarithmicIntervalSource lo (lo+h))).re ≤ h*(Real.log (1/h)+3) := by
  have he := logarithmicFullForm_translation (-lo)
    (hasLogarithmicEnergy_logarithmicIntervalSource hh.le)
    (hasLogarithmicEnergy_logarithmicIntervalSource hh.le)
  rw [logarithmicIntervalSource_shift] at he
  rw [he]
  exact logarithmicFullForm_intervalSource_upper hh hh1

#print axioms logarithmicFullForm_intervalSource_upper_at
#print axioms logarithmicFullForm_ge_log_inverse_width
#print axioms logarithmicIntervalSource_translation_loss
#print axioms hasLogarithmicEnergy_logarithmicIntervalSource
#print axioms logarithmicFullForm_intervalSource_upper
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
