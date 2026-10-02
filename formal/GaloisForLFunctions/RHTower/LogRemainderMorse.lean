import GaloisForLFunctions.RHTower.LogPhaseMorseSubstitution

/-!
# Exact inverse-saddle logarithmic coordinate

The inverse conductor kernel has phase `v - log (1 + v)`, the negative of the
source `logRemainder`. It differs from the forward entropy profile. Its signed
Morse coordinate is analytic through zero, globally increasing on (-1,infinity),
and has an actual analytic local inverse with positive Jacobian. The exact
integral substitution retains the full amplitude and stationary orientation.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GaloisForLFunctions.RHTower

private theorem logRemainder_nonpos {v : ℝ} (hv : -1 < v) : logRemainder v ≤ 0 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + v by linarith)
  unfold logRemainder
  linarith

private theorem neg_logRemainder_pos {v : ℝ} (hv : -1 < v) (hv0 : v ≠ 0) :
    0 < -logRemainder v := by
  have h := Real.log_lt_sub_one_of_pos (show 0 < 1 + v by linarith)
    (show 1 + v ≠ 1 by intro hh; apply hv0; linarith)
  unfold logRemainder
  linarith

/-- Exact inverse-saddle coordinate, with its signed branch retained. -/
def logRemainderMorse (v : ℝ) : ℝ :=
  if 0 ≤ v then Real.sqrt (-2 * logRemainder v) else -Real.sqrt (-2 * logRemainder v)

@[simp] theorem logRemainderMorse_zero : logRemainderMorse 0 = 0 := by
  simp [logRemainderMorse]

theorem logRemainderMorse_sq {v : ℝ} (hv : -1 < v) :
    logRemainderMorse v ^ 2 = -2 * logRemainder v := by
  have hnn : 0 ≤ -2 * logRemainder v := by linarith [logRemainder_nonpos hv]
  unfold logRemainderMorse
  split_ifs
  · exact Real.sq_sqrt hnn
  · rw [neg_pow, Real.sq_sqrt hnn]
    simp

theorem logRemainderMorse_pos {v : ℝ} (hv : 0 < v) : 0 < logRemainderMorse v := by
  have hp := neg_logRemainder_pos (by linarith : -1 < v) hv.ne'
  unfold logRemainderMorse
  rw [if_pos hv.le]
  exact Real.sqrt_pos.mpr (by linarith)

theorem logRemainderMorse_neg {v : ℝ} (hv : -1 < v) (hv0 : v < 0) :
    logRemainderMorse v < 0 := by
  have hp := neg_logRemainder_pos hv hv0.ne
  unfold logRemainderMorse
  rw [if_neg (not_le.mpr hv0)]
  exact neg_neg_of_pos (Real.sqrt_pos.mpr (by linarith))

private theorem analyticAt_logRemainder {v : ℝ} (hv : -1 < v) :
    AnalyticAt ℝ logRemainder v := by
  have hu : ContDiffAt ℝ ω (fun x : ℝ => 1 + x) v := contDiffAt_const.add contDiffAt_id
  have hlog : ContDiffAt ℝ ω (fun x : ℝ => Real.log (1 + x)) v :=
    (Real.contDiffAt_log.mpr (by linarith : 1 + v ≠ 0)).comp v hu
  exact (hlog.sub contDiffAt_id).analyticAt

private def logRemainderMorseRadicand (v : ℝ) : ℝ :=
  -2 * dslope (dslope logRemainder 0) 0 v

private theorem logRemainder_eq_sq_mul (v : ℝ) :
    -2 * logRemainder v = v ^ 2 * logRemainderMorseRadicand v := by
  have h0 : dslope logRemainder 0 0 = 0 := by
    rw [dslope_same, (hasDerivAt_logRemainder (v := 0) (by norm_num)).deriv]
    simp
  have h1 := sub_smul_dslope logRemainder 0 v
  have h2 := sub_smul_dslope (dslope logRemainder 0) 0 v
  simp only [sub_zero, smul_eq_mul, logRemainder_zero, h0] at h1 h2
  unfold logRemainderMorseRadicand
  nlinarith [h1, congrArg (fun x : ℝ => v * x) h2]

private theorem analyticAt_logRemainderMorseRadicand_zero :
    AnalyticAt ℝ logRemainderMorseRadicand 0 := by
  obtain ⟨p, hp⟩ := analyticAt_logRemainder (v := 0) (by norm_num)
  exact analyticAt_const.mul
    hp.has_fpower_series_dslope_fslope.has_fpower_series_dslope_fslope.analyticAt

private theorem logRemainderMorseRadicand_zero : logRemainderMorseRadicand 0 = 1 := by
  have hderiv : deriv logRemainder =ᶠ[𝓝 (0 : ℝ)] fun x => (1 + x)⁻¹ - 1 := by
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with x hx
    exact (hasDerivAt_logRemainder hx).deriv
  have hsecond : iteratedDeriv 2 logRemainder 0 = -1 := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one,
      hderiv.deriv_eq]
    have hu : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add 1
    have hd := (hu.inv (by norm_num : 1 + (0 : ℝ) ≠ 0)).sub_const 1
    simpa using hd.deriv
  have h := _root_.HTGeometry.iterate_dslope_self_eq_iteratedDeriv_div_factorial
    (analyticAt_logRemainder (v := 0) (by norm_num)) 2
  norm_num [Function.iterate_succ_apply, Function.swap, hsecond] at h
  unfold logRemainderMorseRadicand
  rw [dslope_same, h]
  norm_num

private theorem logRemainderMorse_eq_mul_sqrt {v : ℝ} (hv : -1 < v) :
    logRemainderMorse v = v * Real.sqrt (logRemainderMorseRadicand v) := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have hp : 0 < logRemainderMorseRadicand v := by
    have h := neg_logRemainder_pos hv hv0
    have heq := logRemainder_eq_sq_mul v
    have hs := sq_pos_of_ne_zero hv0
    nlinarith
  have hsq : (v * Real.sqrt (logRemainderMorseRadicand v)) ^ 2 =
      logRemainderMorse v ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hp.le, logRemainderMorse_sq hv]
    exact (logRemainder_eq_sq_mul v).symm
  rcases lt_or_gt_of_ne hv0 with hneg | hpos
  · have h1 := logRemainderMorse_neg hv hneg
    have h2 := Real.sqrt_pos.mpr hp
    have h3 : v * Real.sqrt (logRemainderMorseRadicand v) < 0 := mul_neg_of_neg_of_pos hneg h2
    nlinarith
  · have h1 := logRemainderMorse_pos hpos
    have h2 := Real.sqrt_pos.mpr hp
    have h3 : 0 < v * Real.sqrt (logRemainderMorseRadicand v) := mul_pos hpos h2
    nlinarith

/-- The signed square root is real analytic through the saddle. -/
theorem contDiffAt_logRemainderMorse {v : ℝ} (hv : -1 < v) :
    ContDiffAt ℝ ω logRemainderMorse v := by
  rcases eq_or_ne v 0 with rfl | hv0
  · have hp : ContDiffAt ℝ ω logRemainderMorseRadicand 0 :=
      analyticAt_logRemainderMorseRadicand_zero.contDiffAt
    have hs : ContDiffAt ℝ ω (fun x => x * Real.sqrt (logRemainderMorseRadicand x)) 0 :=
      contDiffAt_id.mul ((Real.contDiffAt_sqrt
        (by rw [logRemainderMorseRadicand_zero]; norm_num)).comp 0 hp)
    apply hs.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with x hx
    exact logRemainderMorse_eq_mul_sqrt hx
  · have hbase : ContDiffAt ℝ ω (fun x => -2 * logRemainder x) v :=
      contDiffAt_const.mul (analyticAt_logRemainder hv).contDiffAt
    have hn : -2 * logRemainder v ≠ 0 := by
      have h := neg_logRemainder_pos hv hv0
      linarith
    have hs := (Real.contDiffAt_sqrt hn).comp v hbase
    rcases lt_or_gt_of_ne hv0 with hneg | hpos
    · apply hs.neg.congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hneg] with x hx
      simp [logRemainderMorse, not_le.mpr (show x < 0 from hx)]
    · apply hs.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hpos] with x hx
      simp [logRemainderMorse, (show 0 < x from hx).le]

theorem hasDerivAt_logRemainderMorse_zero : HasDerivAt logRemainderMorse 1 0 := by
  have hq := analyticAt_logRemainderMorseRadicand_zero.differentiableAt.hasDerivAt
  have hs := hq.sqrt (by rw [logRemainderMorseRadicand_zero]; norm_num)
  have hd := (hasDerivAt_id' (0 : ℝ)).mul hs
  have hd' : HasDerivAt (fun x => x * Real.sqrt (logRemainderMorseRadicand x)) 1 0 := by
    simpa only [logRemainderMorseRadicand_zero, Real.sqrt_one, mul_one, zero_mul, add_zero,
      Pi.mul_apply] using! hd
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with x hx
  exact logRemainderMorse_eq_mul_sqrt hx

/-- Exact Jacobian away from the saddle; the removable center value is one. -/
theorem hasDerivAt_logRemainderMorse {v : ℝ} (hv : -1 < v) :
    HasDerivAt logRemainderMorse
      (if v = 0 then 1 else (1 - (1 + v)⁻¹) / logRemainderMorse v) v := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simpa using hasDerivAt_logRemainderMorse_zero
  have hd := (contDiffAt_logRemainderMorse hv).differentiableAt (by simp)
  have heq : (fun x => logRemainderMorse x ^ 2) =ᶠ[𝓝 v]
      fun x => -2 * logRemainder x := by
    filter_upwards [Ioi_mem_nhds hv] with x hx
    exact logRemainderMorse_sq hx
  have h1 := hd.hasDerivAt.pow 2
  have h2 := (hasDerivAt_logRemainder hv).const_mul (-2)
  have he : 2 * logRemainderMorse v * deriv logRemainderMorse v =
      2 * (1 - (1 + v)⁻¹) := by
    have hh := (h1.congr_of_eventuallyEq heq.symm).unique h2
    simp only [Nat.cast_ofNat] at hh
    linarith
  have hn : logRemainderMorse v ≠ 0 := by
    rcases lt_or_gt_of_ne hv0 with hn | hp
    · exact (logRemainderMorse_neg hv hn).ne
    · exact (logRemainderMorse_pos hp).ne'
  have hdval : deriv logRemainderMorse v = (1 - (1 + v)⁻¹) / logRemainderMorse v := by
    apply (eq_div_iff hn).mpr
    nlinarith
  simpa [hv0, hdval] using hd.hasDerivAt

/-- The universal logarithmic phase has an actual smooth local inverse coordinate,
with positive Jacobian and exact quadratic phase throughout a fixed saddle neighborhood. -/
theorem exists_logRemainderMorse_inverse :
    ∃ (r : ℝ) (j : ℝ → ℝ), 0 < r ∧ j 0 = 0 ∧ deriv j 0 = 1 ∧
      ∀ w ∈ Icc (-r) r,
        AnalyticAt ℝ j w ∧ 0 < deriv j w ∧ -1 < j w ∧
          logRemainderMorse (j w) = w ∧ logRemainder (j w) = -(w ^ 2) / 2 := by
  have hf : AnalyticAt ℝ logRemainderMorse 0 :=
    (contDiffAt_logRemainderMorse (v := 0) (by norm_num)).analyticAt
  have hd : deriv logRemainderMorse 0 = 1 := hasDerivAt_logRemainderMorse_zero.deriv
  have hn : deriv logRemainderMorse 0 ≠ 0 := by rw [hd]; norm_num
  let j := hf.hasStrictDerivAt.localInverse logRemainderMorse (deriv logRemainderMorse 0) 0 hn
  have hj : AnalyticAt ℝ j 0 := by
    simpa only [logRemainderMorse_zero] using hf.analyticAt_localInverse hn
  have hj0 : j 0 = 0 := by
    simpa only [logRemainderMorse_zero] using
      (hf.hasStrictDerivAt.hasStrictFDerivAt_equiv hn).localInverse_apply_image
  have hjd : deriv j 0 = 1 := by
    have hh := (hf.hasStrictDerivAt.to_localInverse hn).hasDerivAt.deriv
    simpa only [logRemainderMorse_zero, hd, inv_one] using hh
  have hright : ∀ᶠ w in 𝓝 (0 : ℝ), logRemainderMorse (j w) = w := by
    simpa only [logRemainderMorse_zero] using hf.hasStrictDerivAt.eventually_right_inverse hn
  have hpos : ∀ᶠ w in 𝓝 (0 : ℝ), 0 < deriv j w :=
    hj.deriv.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by rw [hjd]; norm_num))
  have hdom : ∀ᶠ w in 𝓝 (0 : ℝ), -1 < j w :=
    hj.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by rw [hj0]; norm_num))
  have hev := hj.eventually_analyticAt.and (hpos.and (hdom.and hright))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨r / 2, j, by positivity, hj0, hjd, ?_⟩
  intro w hw
  have hwr : w ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hw.1, hw.2]
  obtain ⟨ha, hp, hdom, he⟩ := hsub hwr
  refine ⟨ha, hp, hdom, he, ?_⟩
  have hs := logRemainderMorse_sq hdom
  rw [he] at hs
  linarith

/-- The exact inverse-saddle coordinate has positive Jacobian throughout its real domain. -/
theorem deriv_logRemainderMorse_pos {v : ℝ} (hv : -1 < v) :
    0 < deriv logRemainderMorse v := by
  rw [(hasDerivAt_logRemainderMorse hv).deriv]
  split_ifs with hz
  · norm_num
  · have hden : 0 < 1 + v := by linarith
    have he : 1 - (1 + v)⁻¹ = v / (1 + v) := by field_simp; ring
    rw [he]
    rcases lt_or_gt_of_ne hz with hn | hp
    · exact div_pos_of_neg_of_neg (div_neg_of_neg_of_pos hn hden) (logRemainderMorse_neg hv hn)
    · exact div_pos (div_pos hp hden) (logRemainderMorse_pos hp)

/-- The inverse-saddle coordinate is globally order preserving on the full positive spatial domain. -/
theorem strictMonoOn_logRemainderMorse : StrictMonoOn logRemainderMorse (Ioi (-1 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi (-1 : ℝ))
    (fun v hv => (contDiffAt_logRemainderMorse hv).continuousAt.continuousWithinAt)
  intro v hv
  exact deriv_logRemainderMorse_pos (interior_subset hv)

/-- The literal inverse-frequency phase has logRemainder, with the opposite stationary orientation. -/
theorem chiInverseFrequency_phase_scaled {t v : ℝ} (ht : 0 < t) (hv : -1 < v) :
    t * (1 + v) - t * Real.log ((t * (1 + v)) / (2 * Real.pi)) =
      t - t * Real.log (t / (2 * Real.pi)) - t * logRemainder v := by
  rw [show (t * (1 + v)) / (2 * Real.pi) = (t / (2 * Real.pi)) * (1 + v) by ring,
    Real.log_mul (ne_of_gt (by positivity : 0 < t / (2 * Real.pi))) (by linarith : 1 + v ≠ 0)]
  unfold logRemainder
  ring

/-- Exact signed change of variables across the saddle, with the full Jacobian retained.
The source supplies the inverse and positive Jacobian; no amplitude regularity premise is needed. -/
theorem exists_logRemainderMorse_integral_substitution :
    ∃ (r : ℝ) (j : ℝ → ℝ), 0 < r ∧ j 0 = 0 ∧ deriv j 0 = 1 ∧
      (∀ w ∈ Icc (-r) r, AnalyticAt ℝ j w ∧ 0 < deriv j w ∧ -1 < j w) ∧
      ∀ (A : ℝ → ℂ) (lam l u : ℝ), l ∈ Icc (-r) r → u ∈ Icc (-r) r →
        (∫ v in j l..j u, A v * Complex.exp (Complex.I * ((lam * logRemainder v : ℝ) : ℂ))) =
        ∫ w in l..u, ((deriv j w : ℝ) : ℂ) * A (j w) *
          Complex.exp (Complex.I * ((-(lam * w ^ 2) / 2 : ℝ) : ℂ)) := by
  obtain ⟨r, j, hr, hj0, hjd, hj⟩ := exists_logRemainderMorse_inverse
  refine ⟨r, j, hr, hj0, hjd, fun w hw => ⟨(hj w hw).1, (hj w hw).2.1,
    (hj w hw).2.2.1⟩, ?_⟩
  intro A lam l u hl hu
  have hsub : uIcc l u ⊆ Icc (-r) r := uIcc_subset_Icc hl hu
  have hcont : ContinuousOn j (uIcc l u) :=
    fun w hw => (hj w (hsub hw)).1.continuousAt.continuousWithinAt
  have hderiv : ∀ w ∈ Ioo (min l u) (max l u), HasDerivAt j (deriv j w) w :=
    fun w hw => (hj w (hsub ⟨hw.1.le, hw.2.le⟩)).1.differentiableAt.hasDerivAt
  have hpos : ∀ w ∈ Ioo (min l u) (max l u), 0 ≤ deriv j w :=
    fun w hw => (hj w (hsub ⟨hw.1.le, hw.2.le⟩)).2.1.le
  have he := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := fun v => A v * Complex.exp (Complex.I * ((lam * logRemainder v : ℝ) : ℂ)))
    hcont hderiv hpos
  rw [← he]
  apply intervalIntegral.integral_congr
  intro w hw
  have hp := (hj w (hsub hw)).2.2.2.2
  simp only [Function.comp_apply, hp, Complex.real_smul]
  rw [mul_assoc]
  congr 2
  congr 2
  push_cast
  ring

end GaloisForLFunctions.RHTower
