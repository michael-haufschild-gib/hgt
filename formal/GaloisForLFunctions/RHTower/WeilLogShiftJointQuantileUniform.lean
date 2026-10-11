import GaloisForLFunctions.RHTower.WeilLogShiftProjectedQuantileUniform
import GaloisForLFunctions.RHTower.WeilLogShiftJointQuantileLimit

/-! Uniform convergence of the actual joint quantile realization on compact probability sets,
including rank-dependent probability levels and tests with a common Lipschitz constant. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem tendstoUniformlyOn_finiteWeilCanonicalJointQuantile_gaussian
    (t : ℕ → ℕ) (K : {K : Set ℝ // IsCompact K ∧ K ⊆ Ioo (0 : ℝ) 1}) :
    TendstoUniformlyOn
      (fun r p => finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) p)
      finiteWeilDiagonalGaussianQuantile atTop K.val := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hscalar := (Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_finiteWeilCanonicalProjectedIndex_quantile t K))
    (ε / 4) (by linarith)
  have htrans : Tendsto (fun r : ℕ => 2 / Real.sqrt (r + 1 : ℕ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_finiteWeil_inverse_sqrt_succ.const_mul (2 : ℝ)
  filter_upwards [hscalar, htrans.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < ε / 2))]
    with r hr htr p hp
  have hdiag := finiteWeilDiagonalPoint_lipschitz.dist_le_mul
    (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) p)
    (quantile
      (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ) p)
  have hbound := finiteWeilCanonicalJointQuantile_diagonal_bound r (t r) ⟨p, K.property.2 hp⟩
  have htriangle := dist_triangle (finiteWeilDiagonalGaussianQuantile p)
    (finiteWeilDiagonalPoint (quantile
      (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ) p))
    (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) p)
  change dist (finiteWeilDiagonalGaussianQuantile p) _ ≤ (2 : ℝ) * _ at hdiag
  rw [dist_comm] at hbound
  have hlevel := hr p hp
  linarith

theorem tendstoUniformlyOn_finiteWeilCanonicalJointQuantile_gaussian_interval
    (t : ℕ → ℕ) (a b : {p : ℝ // p ∈ Ioo (0 : ℝ) 1}) :
    TendstoUniformlyOn
      (fun r p => finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) p)
      finiteWeilDiagonalGaussianQuantile atTop (Icc a.val b.val) := by
  apply tendstoUniformlyOn_finiteWeilCanonicalJointQuantile_gaussian t
    ⟨Icc a.val b.val, isCompact_Icc, ?_⟩
  intro p hp
  exact ⟨a.property.1.trans_le hp.1, hp.2.trans_lt b.property.2⟩

theorem tendsto_finiteWeilCanonicalJointQuantile_moving_level_gap_zero
    (t : ℕ → ℕ) (K : {K : Set ℝ // IsCompact K ∧ K ⊆ Ioo (0 : ℝ) 1})
    (p : ℕ → K.val) :
    Tendsto (fun r => dist
      (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) (p r).val)
      (finiteWeilDiagonalGaussianQuantile (p r).val)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_finiteWeilCanonicalJointQuantile_gaussian t K)) ε hε] with r hr
  have h := hr (p r).val (p r).property
  rw [dist_comm] at h
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using h

theorem tendsto_finiteWeilCanonicalJointQuantile_moving_lipschitz_gap_zero
    (t : ℕ → ℕ) (K : {K : Set ℝ // IsCompact K ∧ K ⊆ Ioo (0 : ℝ) 1})
    (p : ℕ → K.val) (L : NNReal)
    (f : ℕ → {f : EuclideanSpace ℝ (Fin 2) → ℝ // LipschitzWith L f}) :
    Tendsto (fun r => |(f r).val
      (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) (p r).val) -
      (f r).val (finiteWeilDiagonalGaussianQuantile (p r).val)|) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => abs_nonneg _) (fun r => ?_)
    (by simpa only [mul_zero] using
      (tendsto_finiteWeilCanonicalJointQuantile_moving_level_gap_zero t K p).const_mul (L : ℝ))
  simpa only [Real.dist_eq] using (f r).property.dist_le_mul
    (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) (p r).val)
    (finiteWeilDiagonalGaussianQuantile (p r).val)

end RHTower
