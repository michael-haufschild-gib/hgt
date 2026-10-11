import GaloisForLFunctions.RHTower.WeilLogShiftTransportFluctuationComparison

/-! The local logarithmic correction has asymptotic second moment 1/(4(r+1)). -/

open Filter Topology

namespace RHTower

theorem finiteWeilCanonicalEdgeLogCorrectionSecondMoment_fluctuation_bound (r t : ℕ) :
    |((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrectionSecondMoment r (2 * (r + 1) ^ 2 + t) - 1 / 4| ≤
      22 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  have hw : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((2 * (r + 1) ^ 2 + t + 2 : ℕ) : ℝ) := by
    push_cast
    have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
    nlinarith only [ht]
  have hc := finiteWeilCanonicalEdgeLogCorrectionSecondMoment_scaled_comparison r _ hw
  have hv := finiteWeilCanonicalEdgeCenteredSecondMoment_quadratic_sharp_bound r t
  have ht := abs_add_le
    (((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrectionSecondMoment r (2 * (r + 1) ^ 2 + t) -
      finiteWeilCanonicalEdgeCenteredSecondMoment r (2 * (r + 1) ^ 2 + t) / ((r + 1 : ℕ) : ℝ))
    (finiteWeilCanonicalEdgeCenteredSecondMoment r (2 * (r + 1) ^ 2 + t) / ((r + 1 : ℕ) : ℝ) - 1 / 4)
  have hid : (((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrectionSecondMoment r (2 * (r + 1) ^ 2 + t) -
      finiteWeilCanonicalEdgeCenteredSecondMoment r (2 * (r + 1) ^ 2 + t) / ((r + 1 : ℕ) : ℝ)) +
      (finiteWeilCanonicalEdgeCenteredSecondMoment r (2 * (r + 1) ^ 2 + t) / ((r + 1 : ℕ) : ℝ) - 1 / 4) =
      ((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrectionSecondMoment r (2 * (r + 1) ^ 2 + t) - 1 / 4 := by ring
  rw [hid] at ht
  linarith only [ht, hc, hv]

theorem tendsto_finiteWeilCanonicalEdgeLogCorrectionSecondMoment_fluctuation_quarter (t : ℕ → ℕ) :
    Tendsto (fun r : ℕ => ((r + 1 : ℕ) : ℝ) *
      finiteWeilCanonicalEdgeLogCorrectionSecondMoment r (2 * (r + 1) ^ 2 + t r)) atTop (𝓝 ((1 : ℝ) / 4)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun r => abs_nonneg _)
    (fun r => finiteWeilCanonicalEdgeLogCorrectionSecondMoment_fluctuation_bound r (t r))
  have h := tendsto_finiteWeil_midpoint_binomial_error.const_mul (11 : ℝ)
  simpa only [mul_zero, ← mul_assoc, show (11 : ℝ) * 2 = 22 by norm_num] using h

end RHTower
