import GaloisForLFunctions.RHTower.LogPhaseMorse
import GaloisForLFunctions.HTGeometry.ReflectedDividedDifference
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Exact analytic saddle coordinate for the logarithmic phase

The corpus Morse coordinate extends analytically across its apparent square-root singularity.
Its local inverse has positive Jacobian, giving an exact signed integral substitution across
the saddle. No phase Taylor remainder or amplitude regularity assumption enters that identity.
The physical stationary remainder and BAG signed self-target positivity are separate obligations.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GaloisForLFunctions.RHTower


private theorem analyticAt_logPhaseProfile {v : ℝ} (hv : -1 < v) :
    AnalyticAt ℝ logPhaseProfile v := by
  have hu : ContDiffAt ℝ ω (fun x : ℝ => 1 + x) v := contDiffAt_const.add contDiffAt_id
  have hlog : ContDiffAt ℝ ω (fun x : ℝ => Real.log (1 + x)) v :=
    (Real.contDiffAt_log.mpr (by linarith : 1 + v ≠ 0)).comp v hu
  exact (contDiffAt_id.sub (hu.mul hlog)).analyticAt

private def logPhaseMorseRadicand (v : ℝ) : ℝ :=
  -2 * dslope (dslope logPhaseProfile 0) 0 v

private theorem logPhaseProfile_eq_sq_mul (v : ℝ) :
    -2 * logPhaseProfile v = v ^ 2 * logPhaseMorseRadicand v := by
  have h0 : dslope logPhaseProfile 0 0 = 0 := by
    rw [dslope_same, (hasDerivAt_logPhaseProfile (v := 0) (by norm_num)).deriv]
    simp
  have h1 := sub_smul_dslope logPhaseProfile 0 v
  have h2 := sub_smul_dslope (dslope logPhaseProfile 0) 0 v
  simp only [sub_zero, smul_eq_mul, logPhaseProfile_zero, h0] at h1 h2
  unfold logPhaseMorseRadicand
  nlinarith [h1, congrArg (fun x : ℝ => v * x) h2]

private theorem analyticAt_logPhaseMorseRadicand_zero :
    AnalyticAt ℝ logPhaseMorseRadicand 0 := by
  obtain ⟨p, hp⟩ := analyticAt_logPhaseProfile (v := 0) (by norm_num)
  exact analyticAt_const.mul
    hp.has_fpower_series_dslope_fslope.has_fpower_series_dslope_fslope.analyticAt

private theorem logPhaseMorseRadicand_zero : logPhaseMorseRadicand 0 = 1 := by
  have hderiv : deriv logPhaseProfile =ᶠ[𝓝 (0 : ℝ)] fun x => -Real.log (1 + x) := by
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with x hx
    exact (hasDerivAt_logPhaseProfile hx).deriv
  have hsecond : iteratedDeriv 2 logPhaseProfile 0 = -1 := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one,
      hderiv.deriv_eq]
    have hu : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add 1
    have hd := ((Real.hasDerivAt_log (show (1 + (0 : ℝ)) ≠ 0 by norm_num)).comp 0 hu).neg
    simpa only [Function.comp_def, neg_mul, one_mul, inv_one, add_zero] using! hd.deriv
  have h := _root_.HTGeometry.iterate_dslope_self_eq_iteratedDeriv_div_factorial
    (analyticAt_logPhaseProfile (v := 0) (by norm_num)) 2
  norm_num [Function.iterate_succ_apply, Function.swap, hsecond] at h
  unfold logPhaseMorseRadicand
  rw [dslope_same, h]
  norm_num

private theorem logPhaseMorse_eq_mul_sqrt {v : ℝ} (hv : -1 < v) :
    logPhaseMorse v = v * Real.sqrt (logPhaseMorseRadicand v) := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have hp : 0 < logPhaseMorseRadicand v := by
    have h := neg_logPhaseProfile_pos hv hv0
    have heq := logPhaseProfile_eq_sq_mul v
    have hs := sq_pos_of_ne_zero hv0
    nlinarith
  have hsq : (v * Real.sqrt (logPhaseMorseRadicand v)) ^ 2 =
      logPhaseMorse v ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hp.le, logPhaseMorse_sq hv]
    exact (logPhaseProfile_eq_sq_mul v).symm
  rcases lt_or_gt_of_ne hv0 with hneg | hpos
  · have h1 := logPhaseMorse_neg hv hneg
    have h2 := Real.sqrt_pos.mpr hp
    have h3 : v * Real.sqrt (logPhaseMorseRadicand v) < 0 := mul_neg_of_neg_of_pos hneg h2
    nlinarith
  · have h1 := logPhaseMorse_pos hpos
    have h2 := Real.sqrt_pos.mpr hp
    have h3 : 0 < v * Real.sqrt (logPhaseMorseRadicand v) := mul_pos hpos h2
    nlinarith

/-- The signed square root is real analytic through the saddle. -/
theorem contDiffAt_logPhaseMorse {v : ℝ} (hv : -1 < v) :
    ContDiffAt ℝ ω logPhaseMorse v := by
  rcases eq_or_ne v 0 with rfl | hv0
  · have hp : ContDiffAt ℝ ω logPhaseMorseRadicand 0 :=
      analyticAt_logPhaseMorseRadicand_zero.contDiffAt
    have hs : ContDiffAt ℝ ω (fun x => x * Real.sqrt (logPhaseMorseRadicand x)) 0 :=
      contDiffAt_id.mul ((Real.contDiffAt_sqrt
        (by rw [logPhaseMorseRadicand_zero]; norm_num)).comp 0 hp)
    apply hs.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with x hx
    exact logPhaseMorse_eq_mul_sqrt hx
  · have hbase : ContDiffAt ℝ ω (fun x => -2 * logPhaseProfile x) v :=
      contDiffAt_const.mul (analyticAt_logPhaseProfile hv).contDiffAt
    have hn : -2 * logPhaseProfile v ≠ 0 := by
      have h := neg_logPhaseProfile_pos hv hv0
      linarith
    have hs := (Real.contDiffAt_sqrt hn).comp v hbase
    rcases lt_or_gt_of_ne hv0 with hneg | hpos
    · apply hs.neg.congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hneg] with x hx
      simp [logPhaseMorse, not_le.mpr (show x < 0 from hx)]
    · apply hs.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hpos] with x hx
      simp [logPhaseMorse, (show 0 < x from hx).le]

theorem hasDerivAt_logPhaseMorse_zero : HasDerivAt logPhaseMorse 1 0 := by
  have hq := analyticAt_logPhaseMorseRadicand_zero.differentiableAt.hasDerivAt
  have hs := hq.sqrt (by rw [logPhaseMorseRadicand_zero]; norm_num)
  have hd := (hasDerivAt_id' (0 : ℝ)).mul hs
  have hd' : HasDerivAt (fun x => x * Real.sqrt (logPhaseMorseRadicand x)) 1 0 := by
    simpa only [logPhaseMorseRadicand_zero, Real.sqrt_one, mul_one, zero_mul, add_zero,
      Pi.mul_apply] using! hd
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with x hx
  exact logPhaseMorse_eq_mul_sqrt hx

/-- Exact Jacobian away from the saddle; the removable center value is one. -/
theorem hasDerivAt_logPhaseMorse {v : ℝ} (hv : -1 < v) :
    HasDerivAt logPhaseMorse
      (if v = 0 then 1 else Real.log (1 + v) / logPhaseMorse v) v := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simpa using hasDerivAt_logPhaseMorse_zero
  have hd := (contDiffAt_logPhaseMorse hv).differentiableAt (by simp)
  have heq : (fun x => logPhaseMorse x ^ 2) =ᶠ[𝓝 v]
      fun x => -2 * logPhaseProfile x := by
    filter_upwards [Ioi_mem_nhds hv] with x hx
    exact logPhaseMorse_sq hx
  have h1 := hd.hasDerivAt.pow 2
  have h2 := (hasDerivAt_logPhaseProfile hv).const_mul (-2)
  have he : 2 * logPhaseMorse v * deriv logPhaseMorse v =
      2 * Real.log (1 + v) := by
    have hh := (h1.congr_of_eventuallyEq heq.symm).unique h2
    simpa using hh
  have hn : logPhaseMorse v ≠ 0 := by
    rcases lt_or_gt_of_ne hv0 with hn | hp
    · exact (logPhaseMorse_neg hv hn).ne
    · exact (logPhaseMorse_pos hp).ne'
  have hdval : deriv logPhaseMorse v = Real.log (1 + v) / logPhaseMorse v := by
    apply (eq_div_iff hn).mpr
    nlinarith
  simpa [hv0, hdval] using hd.hasDerivAt


/-- The universal logarithmic phase has an actual smooth local inverse coordinate,
with positive Jacobian and exact quadratic phase throughout a fixed saddle neighborhood. -/
theorem exists_logPhaseMorse_inverse :
    ∃ (r : ℝ) (j : ℝ → ℝ), 0 < r ∧ j 0 = 0 ∧ deriv j 0 = 1 ∧
      ∀ w ∈ Icc (-r) r,
        AnalyticAt ℝ j w ∧ 0 < deriv j w ∧ -1 < j w ∧
          logPhaseMorse (j w) = w ∧ logPhaseProfile (j w) = -(w ^ 2) / 2 := by
  have hf : AnalyticAt ℝ logPhaseMorse 0 :=
    (contDiffAt_logPhaseMorse (v := 0) (by norm_num)).analyticAt
  have hd : deriv logPhaseMorse 0 = 1 := hasDerivAt_logPhaseMorse_zero.deriv
  have hn : deriv logPhaseMorse 0 ≠ 0 := by rw [hd]; norm_num
  let j := hf.hasStrictDerivAt.localInverse logPhaseMorse (deriv logPhaseMorse 0) 0 hn
  have hj : AnalyticAt ℝ j 0 := by
    simpa only [logPhaseMorse_zero] using hf.analyticAt_localInverse hn
  have hj0 : j 0 = 0 := by
    simpa only [logPhaseMorse_zero] using
      (hf.hasStrictDerivAt.hasStrictFDerivAt_equiv hn).localInverse_apply_image
  have hjd : deriv j 0 = 1 := by
    have hh := (hf.hasStrictDerivAt.to_localInverse hn).hasDerivAt.deriv
    simpa only [logPhaseMorse_zero, hd, inv_one] using hh
  have hright : ∀ᶠ w in 𝓝 (0 : ℝ), logPhaseMorse (j w) = w := by
    simpa only [logPhaseMorse_zero] using hf.hasStrictDerivAt.eventually_right_inverse hn
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
  have hs := logPhaseMorse_sq hdom
  rw [he] at hs
  linarith

/-- Exact signed change of variables across the saddle, with the full Jacobian retained.
The source supplies the inverse and positive Jacobian; no amplitude regularity premise is needed. -/
theorem exists_logPhaseMorse_integral_substitution :
    ∃ (r : ℝ) (j : ℝ → ℝ), 0 < r ∧ j 0 = 0 ∧ deriv j 0 = 1 ∧
      (∀ w ∈ Icc (-r) r, AnalyticAt ℝ j w ∧ 0 < deriv j w ∧ -1 < j w) ∧
      ∀ (A : ℝ → ℂ) (lam l u : ℝ), l ∈ Icc (-r) r → u ∈ Icc (-r) r →
        (∫ v in j l..j u, A v * Complex.exp (Complex.I * ((lam * logPhaseProfile v : ℝ) : ℂ))) =
        ∫ w in l..u, ((deriv j w : ℝ) : ℂ) * A (j w) *
          Complex.exp (Complex.I * ((-(lam * w ^ 2) / 2 : ℝ) : ℂ)) := by
  obtain ⟨r, j, hr, hj0, hjd, hj⟩ := exists_logPhaseMorse_inverse
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
    (g := fun v => A v * Complex.exp (Complex.I * ((lam * logPhaseProfile v : ℝ) : ℂ)))
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

