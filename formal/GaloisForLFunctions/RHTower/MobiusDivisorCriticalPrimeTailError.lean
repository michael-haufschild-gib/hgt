import GaloisForLFunctions.RHTower.MobiusDivisorCriticalPrimeTailSource
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalMertensLogError

/-!
# Vanishing discrete error of the actual prime-tail convolution

The quadratic Mertens error is uniformly bounded on the moving half-ray.
The actual integrable velocity supplies a fixed majorant, so dominated
convergence preserves the second-order signed source coefficient.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

private theorem velocity_measurable : Measurable criticalAbelLogVelocity :=
  (measurable_criticalAbelLogDefect.div_const 2).sub
    (measurable_const.mul measurable_criticalAbelLogProfile)

private theorem logError_measurable : Measurable criticalMertensLogError :=
  (((measurable_of_countable Sieve.mertensS).comp Real.measurable_exp.nat_floor).sub
    Real.measurable_log).sub_const Sieve.meisselMertensConst

private def scaledPrimeError (t s : ℝ) : ℝ :=
  (Iic (t / 2)).indicator (fun s => criticalAbelLogVelocity s *
    (t ^ (2 : ℕ) * (criticalMertensLogError (t - s) - criticalMertensLogError (t / 2)))) s

private theorem scaledPrimeError_measurable (t : ℝ) : Measurable (scaledPrimeError t) :=
  (velocity_measurable.mul (measurable_const.mul
    ((logError_measurable.comp (measurable_const.sub measurable_id)).sub_const
      (criticalMertensLogError (t / 2))))).indicator measurableSet_Iic

private theorem shiftedLogError_limit (s : ℝ) :
    Tendsto (fun t : ℝ => t ^ (2 : ℕ) * criticalMertensLogError (t - s)) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t - s) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-s) tendsto_id
  have hr : Tendsto (fun t : ℝ => 1 + s / (t - s)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := s)).div_atTop ht)
  have h := (hr.pow 2).mul (tendsto_criticalMertensLogError_quadratic_zero.comp ht)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (s + 1)] with t htt
  have hn : t - s ≠ 0 := by linarith
  dsimp only [Function.comp_apply]
  field_simp [hn]
  ring

private theorem halfLogError_limit :
    Tendsto (fun t : ℝ => t ^ (2 : ℕ) * criticalMertensLogError (t / 2)) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have h := (tendsto_criticalMertensLogError_quadratic_zero.comp ht).const_mul 4
  simp only [mul_zero] at h
  convert h using 1
  funext t
  dsimp only [Function.comp_apply]
  ring

private theorem scaledPrimeError_limit (s : ℝ) :
    Tendsto (fun t : ℝ => scaledPrimeError t s) atTop (𝓝 0) := by
  have h := ((shiftedLogError_limit s).sub halfLogError_limit).const_mul
    (criticalAbelLogVelocity s)
  simp only [sub_zero, mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 * s)] with t ht
  have hs : s ∈ Iic (t / 2) := by change s ≤ t / 2; linarith
  simp only [scaledPrimeError, Set.indicator_of_mem hs]
  ring

private theorem scaledLogError_bound {t u : ℝ} (ht : 1 ≤ t) (hu : t / 2 ≤ u)
    (he : |u ^ (2 : ℕ) * criticalMertensLogError u| ≤ 1) :
    |t ^ (2 : ℕ) * criticalMertensLogError u| ≤ 4 := by
  have hs : t ^ (2 : ℕ) ≤ 4 * u ^ (2 : ℕ) := by
    have h1 : 0 ≤ 2 * u - t := by linarith
    have h2 : 0 ≤ 2 * u + t := by linarith
    nlinarith [mul_nonneg h1 h2]
  rw [abs_mul, abs_of_nonneg (sq_nonneg u)] at he
  rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
  calc
    _ ≤ (4 * u ^ (2 : ℕ)) * |criticalMertensLogError u| :=
      mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    _ ≤ 4 := by nlinarith

private theorem scaledPrimeError_bound :
    ∀ᶠ t : ℝ in atTop, ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
      ‖scaledPrimeError t s‖ ≤ 8 * ‖criticalAbelLogVelocity s‖ := by
  have h := tendsto_criticalMertensLogError_quadratic_zero.norm.eventually
    (eventually_lt_nhds (by norm_num : ‖(0 : ℝ)‖ < 1))
  obtain ⟨U, hU⟩ := eventually_atTop.mp h
  filter_upwards [eventually_ge_atTop (max (2 * U) 2)] with t ht
  have ht1 : 1 ≤ t := by have := (le_max_right (2 * U) 2).trans ht; linarith
  have htU : U ≤ t / 2 := by have := (le_max_left (2 * U) 2).trans ht; linarith
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  by_cases hst : s ≤ t / 2
  · have hshift : t / 2 ≤ t - s := by linarith
    have he1 : |(t - s) ^ (2 : ℕ) * criticalMertensLogError (t - s)| ≤ 1 := by
      simpa only [Real.norm_eq_abs] using (hU (t - s) (htU.trans hshift)).le
    have he2 : |(t / 2) ^ (2 : ℕ) * criticalMertensLogError (t / 2)| ≤ 1 := by
      simpa only [Real.norm_eq_abs] using (hU (t / 2) htU).le
    have hdiff : |t ^ (2 : ℕ) *
        (criticalMertensLogError (t - s) - criticalMertensLogError (t / 2))| ≤ 8 := by
      rw [mul_sub]
      exact (abs_sub _ _).trans (by
        have h1 := scaledLogError_bound ht1 hshift he1
        have h2 := scaledLogError_bound ht1 le_rfl he2
        linarith)
    simp only [scaledPrimeError, Set.indicator_apply, mem_Iic, if_pos hst, norm_mul, Real.norm_eq_abs]
    rw [abs_mul] at hdiff
    nlinarith [abs_nonneg (criticalAbelLogVelocity s)]
  · simp only [scaledPrimeError, Set.indicator_apply, mem_Iic, if_neg hst, norm_zero]
    positivity

/-- The actual discrete Mertens error contributes zero at second order. -/
theorem tendsto_criticalPrimeTail_scaled_error_zero :
    Tendsto (fun t : ℝ => t ^ (2 : ℕ) *
      ∫ s in (0 : ℝ)..t / 2, criticalAbelLogVelocity s *
        (criticalMertensLogError (t - s) - criticalMertensLogError (t / 2))) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun s => 8 * ‖criticalAbelLogVelocity s‖)
    (Eventually.of_forall (fun t => (scaledPrimeError_measurable t).aestronglyMeasurable.restrict))
    scaledPrimeError_bound (integrableOn_criticalAbelLogVelocity.norm.const_mul 8)
    (Eventually.of_forall scaledPrimeError_limit)
  simp only [integral_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp only [scaledPrimeError]
  rw [integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have hs : Iic (t / 2) ∩ Ioi (0 : ℝ) = Ioc 0 (t / 2) := by
    ext s
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc, and_comm]
  rw [hs, ← intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ t / 2),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  ring

end RHTower
