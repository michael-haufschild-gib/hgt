import GaloisForLFunctions.HTGeometry.QuantileCompactConvergence
import GaloisForLFunctions.RHTower.WeilLogShiftGaussianQuantile
import GaloisForLFunctions.RHTower.WeilLogShiftProjectedWeakLimit

/-! The actual projected index quantiles converge uniformly on every compact set of interior
probability levels. All distributional hypotheses come from the finite Weil weak limit. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem tendstoUniformlyOn_finiteWeilCanonicalProjectedIndex_quantile
    (t : ℕ → ℕ) (K : {K : Set ℝ // IsCompact K ∧ K ⊆ Ioo (0 : ℝ) 1}) :
    TendstoUniformlyOn
      (fun r p => quantile
        (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ) p)
      (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ)) atTop K.val := by
  let μ : ℕ → ProbabilityMeasure ℝ := fun r =>
    finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0
  let v : NNReal := ⟨((1 : ℝ) + 0) ^ 2 / 4, by positivity⟩
  have hv : v ≠ 0 := by
    apply ne_of_gt
    change (0 : ℝ) < ((1 : ℝ) + 0) ^ 2 / 4
    norm_num
  exact tendstoUniformlyOn_quantile_of_tendsto_cdf (fun r => (μ r : Measure ℝ))
    (gaussianReal 0 v)
    (finiteWeil_gaussian_cdf_tendsto μ v hv
      (tendsto_finiteWeilCanonicalProjectedProbabilityLaw_gaussian t 1 0))
    (finiteWeil_gaussian_cdf_strictMono v hv) K.property.1 K.property.2

end RHTower
