import GaloisForLFunctions.RHTower.WeilLogShiftIndexCorrectionCovariance
import GaloisForLFunctions.RHTower.WeilLogShiftActualVarianceLimit

/-! The joint normalized covariance converges to a positive rank-one matrix. -/

open Filter Topology

namespace RHTower

theorem tendsto_finiteWeilCanonicalFluctuationResidual_normalized_zero (t : ℕ → ℕ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalFluctuationResidual r (2 * (r + 1) ^ 2 + t r) /
      ((r + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (g := fun r : ℕ =>
    2 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)))
    (fun r => div_nonneg (finiteWeilCanonicalFluctuationResidual_nonneg r _) (by positivity))
  · intro r
    calc
      _ ≤ 1 / ((r + 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right
        (finiteWeilCanonicalFluctuationResidual_quadratic_bound r (t r)) (by positivity)
      _ ≤ 2 / ((r + 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ _ := finiteWeil_edge_correction_reciprocal_error r
  · exact tendsto_finiteWeil_midpoint_binomial_error

theorem tendsto_finiteWeilCanonicalIndexCorrectionCovariance_quarter (t : ℕ → ℕ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalIndexCorrectionCovariance r (2 * (r + 1) ^ 2 + t r))
      atTop (𝓝 ((1 : ℝ) / 4)) := by
  have h := (((tendsto_finiteWeilCanonicalEdgeLogCorrectionVariance_quarter t).add
    (tendsto_finiteWeilCanonicalEdgeIndexVariance_quarter t)).sub
    (tendsto_finiteWeilCanonicalFluctuationResidual_normalized_zero t)).div_const (2 : ℝ)
  convert h using 1
  · funext r
    have hid := finiteWeilCanonicalFluctuationResidual_normalized_eq r (2 * (r + 1) ^ 2 + t r)
    linarith only [hid]
  · norm_num

theorem tendsto_finiteWeilCanonicalEdgeVariances_product (t : ℕ → ℕ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalEdgeIndexVariance r (2 * (r + 1) ^ 2 + t r) *
      finiteWeilCanonicalEdgeLogCorrectionVariance r (2 * (r + 1) ^ 2 + t r))
      atTop (𝓝 ((1 : ℝ) / 16)) := by
  have h := (tendsto_finiteWeilCanonicalEdgeIndexVariance_quarter t).mul
    (tendsto_finiteWeilCanonicalEdgeLogCorrectionVariance_quarter t)
  convert h using 1
  · funext r
    have hn : (((r + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp
  · norm_num

theorem tendsto_finiteWeilCanonicalFluctuationDeterminant_zero (t : ℕ → ℕ) :
    Tendsto (fun r : ℕ =>
      finiteWeilCanonicalEdgeIndexVariance r (2 * (r + 1) ^ 2 + t r) *
        finiteWeilCanonicalEdgeLogCorrectionVariance r (2 * (r + 1) ^ 2 + t r) -
      finiteWeilCanonicalIndexCorrectionCovariance r (2 * (r + 1) ^ 2 + t r) ^ 2)
      atTop (𝓝 0) := by
  have hC := tendsto_finiteWeilCanonicalIndexCorrectionCovariance_quarter t
  have h := (tendsto_finiteWeilCanonicalEdgeVariances_product t).sub (hC.mul hC)
  simpa only [pow_two, show (1 : ℝ) / 16 - (1 / 4) * (1 / 4) = 0 by norm_num] using h

end RHTower
