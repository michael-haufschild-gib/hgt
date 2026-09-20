import GaloisForLFunctions.RHTower.XiMassTwoRapidityCorrelationGeometry

/-!
# Exact two-rapidity stationary phase

The full mass covariance has an anti-ordered timelike stationary pair.  This file records its
actual phase: the difference of timelike mass shells.  For ordered nonnegative frequencies that
phase is strictly positive, so a cancellation argument cannot identify the pair with the
zero-phase diagonal.
-/

namespace RHTower

noncomputable section

/-- At the literal timelike stationary pair, the full two-rapidity covariance phase is the
difference of the two mass shells. -/
theorem xiMassTwoRapidityCorrelationPhase_at_timelike_stationary
    {u h k : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hhu : h < u) (hku : k < u) :
    xiMassTwoRapidityCorrelationPhase u h k
        (-timelikeRapidity u h) (-timelikeRapidity u k) =
      Real.sqrt (u ^ 2 - h ^ 2) - Real.sqrt (u ^ 2 - k ^ 2) := by
  unfold xiMassTwoRapidityCorrelationPhase
  rw [massPhase_timelike hu hh hhu (-timelikeRapidity u h),
    massPhase_timelike hu hk hku (-timelikeRapidity u k)]
  simp

/-- Strictly ordered nonnegative frequencies have a strictly positive full-covariance phase at
their timelike stationary pair.  In particular the anti-ordered saddle is not a zero-phase
diagonal contribution. -/
theorem xiMassTwoRapidityCorrelationPhase_at_timelike_stationary_pos
    {u h k : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hhu : h < u) (hku : k < u) (hhk : h < k) :
    0 < xiMassTwoRapidityCorrelationPhase u h k
        (-timelikeRapidity u h) (-timelikeRapidity u k) := by
  rw [xiMassTwoRapidityCorrelationPhase_at_timelike_stationary hu hh hk hhu hku]
  apply sub_pos.mpr
  apply Real.sqrt_lt_sqrt
  · nlinarith [mul_self_lt_mul_self hk hku]
  · nlinarith [mul_self_lt_mul_self hh hhk]

/-- In the deep timelike subcone, the actual stationary phase has an explicit small-phase
bound.  In particular its central phase coalesces whenever the higher frequency is sub-root
relative to the mass scale. -/
theorem xiMassTwoRapidityCorrelationPhase_at_timelike_stationary_le
    {u h k : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hhu : h < u) (hku : k < u) (hhk : h < k) (hdeep : 2 * k ≤ u) :
    xiMassTwoRapidityCorrelationPhase u h k
        (-timelikeRapidity u h) (-timelikeRapidity u k) ≤ 2 * k ^ 2 / u := by
  rw [xiMassTwoRapidityCorrelationPhase_at_timelike_stationary hu hh hk hhu hku]
  have hsqh : h ^ 2 < u ^ 2 := by
    nlinarith [mul_self_lt_mul_self hh hhu]
  have hsqk : k ^ 2 < u ^ 2 := by
    nlinarith [mul_self_lt_mul_self hk hku]
  have hrad_h : 0 ≤ u ^ 2 - h ^ 2 := by linarith
  have hrad_k : 0 ≤ u ^ 2 - k ^ 2 := by linarith
  have hrad_k_pos : 0 < u ^ 2 - k ^ 2 := by linarith
  have hsqrt_k_pos : 0 < Real.sqrt (u ^ 2 - k ^ 2) :=
    Real.sqrt_pos.2 hrad_k_pos
  have hnum : 0 ≤ k ^ 2 - h ^ 2 := by
    nlinarith [mul_self_lt_mul_self hh hhk]
  have hfactor :
      (Real.sqrt (u ^ 2 - h ^ 2) - Real.sqrt (u ^ 2 - k ^ 2)) *
          (Real.sqrt (u ^ 2 - h ^ 2) + Real.sqrt (u ^ 2 - k ^ 2)) =
        k ^ 2 - h ^ 2 := by
    nlinarith [Real.sq_sqrt hrad_h, Real.sq_sqrt hrad_k]
  have hsum_pos : 0 <
      Real.sqrt (u ^ 2 - h ^ 2) + Real.sqrt (u ^ 2 - k ^ 2) := by
    positivity
  have hquot :
      Real.sqrt (u ^ 2 - h ^ 2) - Real.sqrt (u ^ 2 - k ^ 2) =
        (k ^ 2 - h ^ 2) /
          (Real.sqrt (u ^ 2 - h ^ 2) + Real.sqrt (u ^ 2 - k ^ 2)) := by
    exact (eq_div_iff hsum_pos.ne').2 hfactor
  have hden_ge :
      Real.sqrt (u ^ 2 - k ^ 2) ≤
        Real.sqrt (u ^ 2 - h ^ 2) + Real.sqrt (u ^ 2 - k ^ 2) := by
    linarith [Real.sqrt_nonneg (u ^ 2 - h ^ 2)]
  have hfirst :
      (k ^ 2 - h ^ 2) /
          (Real.sqrt (u ^ 2 - h ^ 2) + Real.sqrt (u ^ 2 - k ^ 2)) ≤
        (k ^ 2 - h ^ 2) / Real.sqrt (u ^ 2 - k ^ 2) :=
    div_le_div_of_nonneg_left hnum hsqrt_k_pos hden_ge
  have hkhalf : k ≤ u / 2 := by linarith
  have hsqhalf : k ^ 2 ≤ (u / 2) ^ 2 :=
    (sq_le_sq₀ hk (by positivity)).2 hkhalf
  have hhalf_rad : (u / 2) ^ 2 ≤ u ^ 2 - k ^ 2 := by
    nlinarith
  have hhalf : u / 2 ≤ Real.sqrt (u ^ 2 - k ^ 2) := by
    calc
      u / 2 = Real.sqrt ((u / 2) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
        positivity
      _ ≤ Real.sqrt (u ^ 2 - k ^ 2) := Real.sqrt_le_sqrt hhalf_rad
  have hlast : (k ^ 2 - h ^ 2) / Real.sqrt (u ^ 2 - k ^ 2) ≤ 2 * k ^ 2 / u := by
    apply (div_le_iff₀ hsqrt_k_pos).2
    calc
      k ^ 2 - h ^ 2 ≤ k ^ 2 := by nlinarith
      _ = (2 * k ^ 2 / u) * (u / 2) := by field_simp
      _ ≤ (2 * k ^ 2 / u) * Real.sqrt (u ^ 2 - k ^ 2) := by
        apply mul_le_mul_of_nonneg_left hhalf
        positivity
  exact hquot.trans_le (hfirst.trans hlast)

end

end RHTower
