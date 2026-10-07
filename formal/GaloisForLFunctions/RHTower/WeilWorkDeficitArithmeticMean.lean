import GaloisForLFunctions.RHTower.WeilConeSingularDeficitEnvelope

/-!
# Arithmetic means after subtracting the Xi logarithmic derivative

Subtracting before taking the mean cancels the archimedean datum exactly. These limits use
the actual canonical continuation and require no separate asymptotic estimate for that datum.
-/

open Complex Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace RHTower.WeilSpectral

private theorem tendsto_sharp_mean_of_eight_mean {f : ℝ → ℝ} (hf : Continuous f)
    {L : ℝ} (h : Tendsto (fun T : ℝ => (∫ t in (8 : ℝ)..T, f t) / T) atTop (𝓝 L)) :
    Tendsto (fun T : ℝ => (∫ t in Ioc 0 T, f t) / T) atTop (𝓝 L) := by
  have hc : Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..8, f t) / T) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.const_mul (∫ t in (0 : ℝ)..8, f t))
  have hadd := hc.add h
  simp only [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [← intervalIntegral.integral_of_le hT,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable 0 8) (hf.intervalIntegrable 8 T), add_div]

private theorem continuation_difference_eq_series {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (weilContinuation hW ((σ : ℂ) + t * I)).re -
      (logDeriv xi ((σ : ℂ) + t * I)).re = logCosSeries (deviationCoeff lam σ) t := by
  rw [weilContinuation_eq hW (by simpa using hσ)]
  exact re_weilFunction_sub_re_logDeriv_xi hW hσ t

/-- The arithmetic coefficient is the exact linear-scale cosine mean of the difference. -/
theorem tendsto_deficit_arithmetic_cosine_mean {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {σ : ℝ} (hσ : 1 < σ) {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun T : ℝ =>
      (∫ t in Ioc 0 T,
        ((weilContinuation hW ((σ : ℂ) + t * I)).re -
          (logDeriv xi ((σ : ℂ) + t * I)).re) * Real.cos (t * Real.log n)) / T)
      atTop (𝓝 (((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) * (n : ℝ) ^ (-σ) / 2)) := by
  simp_rw [continuation_difference_eq_series hW hσ]
  have ha := summable_abs_deviationCoeff hW hσ
  have h := tendsto_mean_logCosSeries_mul_cos ha n
  rw [bohrLimit_eq_coeff (by simp [deviationCoeff]) hn] at h
  have hc : Continuous (fun t => logCosSeries (deviationCoeff lam σ) t *
      Real.cos (t * Real.log n)) := (continuous_logCosSeries ha).mul (by fun_prop)
  simpa only [deviationCoeff, if_pos hn] using tendsto_sharp_mean_of_eight_mean hc h

/-- The zero-frequency difference has zero linear-scale mean, before unsmoothing either side. -/
theorem tendsto_deficit_arithmetic_mean {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ =>
      (∫ t in Ioc 0 T,
        (weilContinuation hW ((σ : ℂ) + t * I)).re -
          (logDeriv xi ((σ : ℂ) + t * I)).re) / T) atTop (𝓝 0) := by
  simp_rw [continuation_difference_eq_series hW hσ]
  have ha := summable_abs_deviationCoeff hW hσ
  have h := tendsto_mean_logCosSeries_mul_cos ha 1
  rw [bohrLimit_one_eq_zero (by simp [deviationCoeff]) (by simp [deviationCoeff])] at h
  simp only [Nat.cast_one, Real.log_one, mul_zero, Real.cos_zero, mul_one] at h
  exact tendsto_sharp_mean_of_eight_mean (continuous_logCosSeries ha) h

end RHTower.WeilSpectral

end
