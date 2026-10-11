import GaloisForLFunctions.RHTower.WeilLogShiftFluctuationRankOneLimit

/-! Index and logarithmic correction have asymptotically perfect positive correlation. -/

open Filter Topology

noncomputable section
namespace RHTower

def finiteWeilCanonicalIndexCorrectionCorrelation (r k : ℕ) : ℝ :=
  finiteWeilCanonicalIndexCorrectionCovariance r k /
    Real.sqrt (finiteWeilCanonicalEdgeIndexVariance r k * finiteWeilCanonicalEdgeLogCorrectionVariance r k)

theorem tendsto_finiteWeilCanonicalIndexCorrectionCorrelation_one (t : ℕ → ℕ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalIndexCorrectionCorrelation r (2 * (r + 1) ^ 2 + t r))
      atTop (𝓝 1) := by
  have hsqrt := (Real.continuous_sqrt.tendsto ((1 : ℝ) / 16)).comp
    (tendsto_finiteWeilCanonicalEdgeVariances_product t)
  have hs : Real.sqrt ((1 : ℝ) / 16) = 1 / 4 := by norm_num
  rw [hs] at hsqrt
  have h := (tendsto_finiteWeilCanonicalIndexCorrectionCovariance_quarter t).div hsqrt (by norm_num)
  convert h using 1
  · funext r
    rfl
  · norm_num

end RHTower
