import GaloisForLFunctions.RHTower.WeilLogShiftEdgeConcentration
import GaloisForLFunctions.RHTower.WeilLogShiftMidpointBinomialLimit

/-! Quadratic-start transport edges have central mean and vanishing normalized second moment. -/

open Filter Topology

namespace RHTower

theorem tendsto_finiteWeilCanonicalEdgeIndexMean_half (t : ℕ → ℕ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t r) /
      ((r + 1 : ℕ) : ℝ)) atTop (𝓝 ((1 : ℝ) / 2)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun r => abs_nonneg _)
    (fun r => finiteWeilCanonicalEdgeIndexMean_quadratic_bound r (t r))
    tendsto_finiteWeil_midpoint_binomial_error

theorem tendsto_finiteWeilCanonicalEdgeCenteredSecondMoment_zero (t : ℕ → ℕ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalEdgeCenteredSecondMoment r (2 * (r + 1) ^ 2 + t r) /
      ((r + 1 : ℕ) : ℝ) ^ 2) atTop (𝓝 (0 : ℝ)) := by
  apply squeeze_zero (g := fun r : ℕ =>
    2 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)))
  · intro r
    have h := finiteWeilCanonicalEdgeCenteredSecondMoment_nonneg r (2 * (r + 1) ^ 2 + t r)
    positivity
  · intro r
    have h := finiteWeilCanonicalEdgeCenteredSecondMoment_quadratic_bound r (t r)
    have he : 0 ≤ Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ) := by positivity
    linarith only [h, he]
  · exact tendsto_finiteWeil_midpoint_binomial_error

end RHTower
