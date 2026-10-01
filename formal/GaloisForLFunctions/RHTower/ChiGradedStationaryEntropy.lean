import GaloisForLFunctions.RHTower.ChiStationaryEntropyIntegral

open Complex MeasureTheory
noncomputable section
namespace RHTower

/-- Every real grade is integrable on a positive compact height interval. -/
theorem intervalIntegrable_chiStationaryEntropy_grade (a k : ℝ) {l u : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) :
    IntervalIntegrable (fun t => bourgainOscillation (-k * chiStationaryEntropy a t))
      volume l u := by
  have hlog : ContinuousOn Real.log (Set.uIcc l u) := by
    intro t ht
    rw [Set.uIcc_of_le hlu] at ht
    exact (Real.continuousAt_log (hl.trans_le ht.1).ne').continuousWithinAt
  have hd : ContinuousOn (chiStationaryEntropy a) (Set.uIcc l u) := by
    unfold chiStationaryEntropy
    exact ((continuousOn_id.mul (hlog.sub continuousOn_const)).sub continuousOn_id).add continuousOn_const
  have hc : Continuous (fun x : ℝ => bourgainOscillation (-k * x)) := by
    unfold bourgainOscillation
    fun_prop
  exact (hc.comp_continuousOn hd).intervalIntegrable

/-- Exact simultaneous dilation of the stationary entropy. -/
theorem chiStationaryEntropy_scale {a k : ℝ} (ha : 0 < a) (hk : 0 < k) (t : ℝ) :
    chiStationaryEntropy (k * a) (k * t) = k * chiStationaryEntropy a t := by
  by_cases ht : t = 0
  · simp [ht, chiStationaryEntropy]
  · unfold chiStationaryEntropy
    rw [Real.log_mul hk.ne' ht, Real.log_mul hk.ne' ha.ne']
    ring

/-- Exact integral dilation for every positive real grade. -/
theorem integral_chiStationaryEntropy_grade_eq {a k : ℝ}
    (ha : 0 < a) (hk : 0 < k) (l u : ℝ) :
    (∫ t in l..u, bourgainOscillation (-k * chiStationaryEntropy a t)) =
      (k⁻¹ : ℂ) * ∫ t in (k * l)..(k * u),
        bourgainOscillation (-chiStationaryEntropy (k * a) t) := by
  have hf : (fun t : ℝ => bourgainOscillation (-k * chiStationaryEntropy a t)) =
      fun t : ℝ => bourgainOscillation (-chiStationaryEntropy (k * a) (k * t)) := by
    funext t
    rw [chiStationaryEntropy_scale ha hk]
    congr 1
    ring
  rw [hf, intervalIntegral.integral_comp_mul_left
    (fun t : ℝ => bourgainOscillation (-chiStationaryEntropy (k * a) t)) hk.ne', Complex.real_smul]
  norm_cast

/-- Full graded stationary model with the complete dilated remainder.
The reciprocal-grade Fresnel amplitude is left in its exact scalar form. -/
theorem norm_integral_chiStationaryEntropy_grade_sub_le {a k h l u : ℝ}
    (ha : 0 < a) (hk : 0 < k) (hh : 0 < h) (hha : h ≤ a / 2)
    (hl : a / 2 ≤ l) (hlh : l ≤ a - h) (hhu : a + h ≤ u) (hu : u ≤ 2 * a) :
    ‖(∫ t in l..u, bourgainOscillation (-k * chiStationaryEntropy a t)) -
      (k⁻¹ : ℂ) * ((Real.sqrt (2 * Real.pi * (k * a)) : ℂ) *
        bourgainOscillation (-(Real.pi / 4)))‖ ≤
      4 * k * h ^ 4 / a ^ 2 + 40 * a / (k * h) := by
  have hb := norm_integral_entropy_sub_stationary_value_le (mul_pos hk ha) (mul_pos hk hh)
    (show k * h ≤ (k * a) / 2 by nlinarith [mul_le_mul_of_nonneg_left hha hk.le])
    (show (k * a) / 2 ≤ k * l by nlinarith [mul_le_mul_of_nonneg_left hl hk.le])
    (show k * l ≤ k * a - k * h by nlinarith [mul_le_mul_of_nonneg_left hlh hk.le])
    (show k * a + k * h ≤ k * u by nlinarith [mul_le_mul_of_nonneg_left hhu hk.le])
    (show k * u ≤ 2 * (k * a) by nlinarith [mul_le_mul_of_nonneg_left hu hk.le])
  rw [integral_chiStationaryEntropy_grade_eq ha hk, ← mul_sub, norm_mul]
  have hn : ‖(k⁻¹ : ℂ)‖ = k⁻¹ := by
    rw [show (k⁻¹ : ℂ) = ((k⁻¹ : ℝ) : ℂ) by norm_cast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
  rw [hn]
  calc
    _ ≤ k⁻¹ * (4 * (k * h) ^ 4 / (k * a) ^ 2 + 40 * (k * a) / (k * h)) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hk.le)
    _ = _ := by field_simp

end RHTower
