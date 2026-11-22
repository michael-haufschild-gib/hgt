import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.RelativeStatement

/-! Estimates for the logarithmic integral on real intervals. -/

namespace QH.PrimeProgressions

theorem intervalIntegrable_inv_log' {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have h1 : ∀ t ∈ Set.uIcc a b, 1 < t := fun t ht => lt_of_lt_of_le (lt_min ha hb) ht.1
  apply ContinuousOn.div continuousOn_const
  · exact Real.continuousOn_log.mono (fun t ht => ne_of_gt (lt_trans zero_lt_one (h1 t ht)))
  · intro t ht
    exact ne_of_gt (Real.log_pos (h1 t ht))

theorem intervalIntegrable_inv_log {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume a b :=
  intervalIntegrable_inv_log' (by linarith only [ha]) (by linarith only [hb])

theorem liX_sub_ge {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (b - a) / Real.log b ≤ liX b - liX a := by
  have hb : 2 ≤ b := le_trans ha hab
  have hsub : liX b - liX a = ∫ t in a..b, 1 / Real.log t := by
    unfold liX
    exact intervalIntegral.integral_interval_sub_left (intervalIntegrable_inv_log le_rfl hb)
      (intervalIntegrable_inv_log le_rfl ha)
  rw [hsub]
  have hconst : ∫ _t in a..b, (1 / Real.log b) = (b - a) / Real.log b := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [← hconst]
  apply intervalIntegral.integral_mono_on hab intervalIntegrable_const (intervalIntegrable_inv_log ha hb)
  intro t ht
  have h2t : 2 ≤ t := le_trans ha ht.1
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  exact one_div_le_one_div_of_le hlogt (Real.log_le_log (by linarith) ht.2)

theorem liX_two : liX 2 = 0 := by
  unfold liX
  simp

theorem liX_nonneg {a : ℝ} (ha : 2 ≤ a) : 0 ≤ liX a := by
  have h := liX_sub_ge (le_refl (2:ℝ)) ha
  rw [liX_two, sub_zero] at h
  exact le_trans (div_nonneg (by linarith) (Real.log_nonneg (by linarith))) h

theorem liX_lower {X : ℝ} (hX : 4 ≤ X) : X / (2 * Real.log X) ≤ liX X := by
  have hX2 : 2 ≤ X := by linarith
  have hL : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have h := liX_sub_ge (le_refl (2 : ℝ)) hX2
  rw [liX_two, sub_zero] at h
  rw [← div_div]
  exact (div_le_div_of_nonneg_right (by linarith : X / 2 ≤ X - 2) hL).trans h

end QH.PrimeProgressions
