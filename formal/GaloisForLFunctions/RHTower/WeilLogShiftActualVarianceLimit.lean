import GaloisForLFunctions.RHTower.WeilLogShiftActualVariance
import GaloisForLFunctions.RHTower.WeilLogShiftCorrectionMeanRate
import GaloisForLFunctions.RHTower.WeilLogShiftTransportFluctuationLimit
import GaloisForLFunctions.RHTower.WeilLogShiftEdgeCorrectionExtremes

/-! Recentring at the actual means preserves both sharp fluctuation constants. -/

open Filter Topology

namespace RHTower

theorem finiteWeilCanonicalEdgeIndexMean_quadratic_bias_sq_bound (r t : ℕ) :
    (finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t) - (r : ℝ) / 2) ^ 2 ≤ 4 := by
  obtain ⟨hl, hu⟩ := abs_le.mp (finiteWeilCanonicalEdgeIndexMean_quadratic_bias_bound r t)
  have hp := mul_nonneg
    (show 0 ≤ 2 - (finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t) - (r : ℝ) / 2) by linarith only [hu])
    (show 0 ≤ 2 + (finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t) - (r : ℝ) / 2) by linarith only [hl])
  nlinarith only [hp]

theorem finiteWeilCanonicalLogTransportCorrection_quadratic_bias_sq_bound (r t : ℕ) :
    ((r + 1 : ℕ) : ℝ) * (finiteWeilCanonicalLogTransportCorrection r (2 * (r + 1) ^ 2 + t) - 1 / 2) ^ 2 ≤
      16 / ((r + 1 : ℕ) : ℝ) := by
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let b := finiteWeilCanonicalLogTransportCorrection r (2 * (r + 1) ^ 2 + t) - 1 / 2
  have hn : 0 < n := by dsimp [n]; positivity
  have hb := finiteWeilCanonicalLogTransportCorrection_quadratic_mean_rate r t
  have hscale : n * |b| ≤ 4 := by
    have h := (le_div_iff₀ hn).mp hb
    change |b| * n ≤ 4 at h
    nlinarith only [h]
  have hp := mul_nonneg (sub_nonneg.mpr hscale) (show 0 ≤ 4 + n * |b| by positivity)
  have hs : (n * |b|) ^ 2 ≤ 16 := by nlinarith only [hp]
  rw [mul_pow, sq_abs] at hs
  change n * b ^ 2 ≤ 16 / n
  apply (le_div_iff₀ hn).mpr
  nlinarith only [hs]

theorem finiteWeilCanonicalEdgeIndexVariance_quadratic_bound (r t : ℕ) :
    |finiteWeilCanonicalEdgeIndexVariance r (2 * (r + 1) ^ 2 + t) / ((r + 1 : ℕ) : ℝ) - 1 / 4| ≤
      10 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let e := Real.sqrt ((n + 1) / 2) / n
  let b := finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t) - (r : ℝ) / 2
  have hn : 0 < n := by dsimp [n]; positivity
  have hb : b ^ 2 ≤ 4 := finiteWeilCanonicalEdgeIndexMean_quadratic_bias_sq_bound r t
  have hrecip : 1 / n ≤ e := by
    have h := finiteWeil_edge_correction_reciprocal_error r
    have hid : 2 / n = 2 * (1 / n) := by ring
    change 2 / n ≤ 2 * e at h
    rw [hid] at h
    linarith only [h]
  have hid : finiteWeilCanonicalEdgeIndexVariance r (2 * (r + 1) ^ 2 + t) / n - 1 / 4 =
      (finiteWeilCanonicalEdgeCenteredSecondMoment r (2 * (r + 1) ^ 2 + t) / n - 1 / 4) - b ^ 2 / n := by
    rw [finiteWeilCanonicalEdgeIndexVariance_eq]
    dsimp [b]
    ring
  change |finiteWeilCanonicalEdgeIndexVariance r (2 * (r + 1) ^ 2 + t) / n - 1 / 4| ≤ 10 * e
  rw [hid]
  calc
    _ ≤ |finiteWeilCanonicalEdgeCenteredSecondMoment r (2 * (r + 1) ^ 2 + t) / n - 1 / 4| + |b ^ 2 / n| := abs_sub _ _
    _ = |finiteWeilCanonicalEdgeCenteredSecondMoment r (2 * (r + 1) ^ 2 + t) / n - 1 / 4| + b ^ 2 / n := by
      rw [abs_of_nonneg (show 0 ≤ b ^ 2 / n by positivity)]
    _ ≤ 6 * e + 4 / n := add_le_add
      (finiteWeilCanonicalEdgeCenteredSecondMoment_quadratic_sharp_bound r t)
      (div_le_div_of_nonneg_right hb hn.le)
    _ ≤ _ := by
      rw [show 4 / n = 4 * (1 / n) by ring]
      linarith only [hrecip]

theorem finiteWeilCanonicalEdgeLogCorrectionVariance_quadratic_bound (r t : ℕ) :
    |((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrectionVariance r (2 * (r + 1) ^ 2 + t) - 1 / 4| ≤
      38 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let e := Real.sqrt ((n + 1) / 2) / n
  let b := finiteWeilCanonicalLogTransportCorrection r (2 * (r + 1) ^ 2 + t) - 1 / 2
  have hn : 0 < n := by dsimp [n]; positivity
  have hb : n * b ^ 2 ≤ 16 / n := finiteWeilCanonicalLogTransportCorrection_quadratic_bias_sq_bound r t
  have hrecip : 1 / n ≤ e := by
    have h := finiteWeil_edge_correction_reciprocal_error r
    have hid : 2 / n = 2 * (1 / n) := by ring
    change 2 / n ≤ 2 * e at h
    rw [hid] at h
    linarith only [h]
  have hid : n * finiteWeilCanonicalEdgeLogCorrectionVariance r (2 * (r + 1) ^ 2 + t) - 1 / 4 =
      (n * finiteWeilCanonicalEdgeLogCorrectionSecondMoment r (2 * (r + 1) ^ 2 + t) - 1 / 4) - n * b ^ 2 := by
    rw [finiteWeilCanonicalEdgeLogCorrectionVariance_eq]
    dsimp [b]
    ring
  change |n * finiteWeilCanonicalEdgeLogCorrectionVariance r (2 * (r + 1) ^ 2 + t) - 1 / 4| ≤ 38 * e
  rw [hid]
  calc
    _ ≤ |n * finiteWeilCanonicalEdgeLogCorrectionSecondMoment r (2 * (r + 1) ^ 2 + t) - 1 / 4| + |n * b ^ 2| := abs_sub _ _
    _ = |n * finiteWeilCanonicalEdgeLogCorrectionSecondMoment r (2 * (r + 1) ^ 2 + t) - 1 / 4| + n * b ^ 2 := by
      rw [abs_of_nonneg (show 0 ≤ n * b ^ 2 by positivity)]
    _ ≤ 22 * e + 16 / n := add_le_add
      (finiteWeilCanonicalEdgeLogCorrectionSecondMoment_fluctuation_bound r t) hb
    _ ≤ _ := by
      rw [show 16 / n = 16 * (1 / n) by ring]
      linarith only [hrecip]

theorem tendsto_finiteWeilCanonicalEdgeIndexVariance_quarter (t : ℕ → ℕ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalEdgeIndexVariance r (2 * (r + 1) ^ 2 + t r) / ((r + 1 : ℕ) : ℝ))
      atTop (𝓝 ((1 : ℝ) / 4)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun r => abs_nonneg _) (fun r => finiteWeilCanonicalEdgeIndexVariance_quadratic_bound r (t r))
  have h := tendsto_finiteWeil_midpoint_binomial_error.const_mul (5 : ℝ)
  simpa only [mul_zero, ← mul_assoc, show (5 : ℝ) * 2 = 10 by norm_num] using h

theorem tendsto_finiteWeilCanonicalEdgeLogCorrectionVariance_quarter (t : ℕ → ℕ) :
    Tendsto (fun r : ℕ => ((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrectionVariance r (2 * (r + 1) ^ 2 + t r))
      atTop (𝓝 ((1 : ℝ) / 4)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun r => abs_nonneg _)
    (fun r => finiteWeilCanonicalEdgeLogCorrectionVariance_quadratic_bound r (t r))
  have h := tendsto_finiteWeil_midpoint_binomial_error.const_mul (19 : ℝ)
  simpa only [mul_zero, ← mul_assoc, show (19 : ℝ) * 2 = 38 by norm_num] using h

end RHTower
