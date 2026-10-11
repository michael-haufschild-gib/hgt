import GaloisForLFunctions.RHTower.WeilLogShiftJointQuantileLaw
import GaloisForLFunctions.RHTower.WeilLogShiftUniformResidual

/-! Explicit common-space joint quantiles converge at every interior probability level. -/

open MeasureTheory ProbabilityTheory GaloisForLFunctions.HTGeometry Filter Set Topology

noncomputable section
namespace RHTower

theorem tendsto_finiteWeilCanonicalProjectedIndex_quantile (t : ℕ → ℕ)
    (p : {p : ℝ // p ∈ Ioo 0 1}) :
    Tendsto (fun r => quantile (finiteWeilCanonicalProjectedProbabilityLaw r
      (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ) p.val) atTop
      (𝓝 (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) p.val)) := by
  let v : NNReal := NNReal.mk (((1 : ℝ) + 0) ^ 2 / 4) (by positivity)
  have hv : v ≠ 0 := by
    apply ne_of_gt
    change (0 : ℝ) < ((1 + 0) ^ 2 / 4)
    norm_num
  exact finiteWeil_gaussian_quantile_tendsto
    (fun r => finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0) v hv
    (tendsto_finiteWeilCanonicalProjectedProbabilityLaw_gaussian t 1 0) p

theorem finiteWeilCanonicalJointQuantile_diagonal_bound (r t : ℕ)
    (p : {p : ℝ // p ∈ Ioo 0 1}) :
    dist (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t) p.val)
      (finiteWeilDiagonalPoint (quantile (finiteWeilCanonicalProjectedProbabilityLaw r
        (2 * (r + 1) ^ 2 + t) 1 0 : Measure ℝ) p.val)) ≤
      2 / Real.sqrt ((r + 1 : ℕ) : ℝ) := by
  obtain ⟨i, hi, hq⟩ := finiteWeilCanonicalJointQuantile_at_level r (2 * (r + 1) ^ 2 + t) p
  rw [hi, hq]
  exact finiteWeilCanonicalFluctuationPoint_diagonal_quadratic_bound r t i

theorem tendsto_finiteWeilCanonicalJointQuantile_transverse_zero (t : ℕ → ℕ)
    (p : {p : ℝ // p ∈ Ioo 0 1}) :
    Tendsto (fun r => dist (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) p.val)
      (finiteWeilDiagonalPoint (quantile (finiteWeilCanonicalProjectedProbabilityLaw r
        (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ) p.val))) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => dist_nonneg)
    (g := fun r => (2 : ℝ) * (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹)
  · intro r
    simpa only [div_eq_mul_inv] using finiteWeilCanonicalJointQuantile_diagonal_bound r (t r) p
  · simpa only [mul_zero] using tendsto_finiteWeil_inverse_sqrt_succ.const_mul (2 : ℝ)

theorem tendsto_finiteWeilCanonicalJointQuantile_gaussian (t : ℕ → ℕ)
    (p : {p : ℝ // p ∈ Ioo 0 1}) :
    Tendsto (fun r => finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) p.val)
      atTop (𝓝 (finiteWeilDiagonalGaussianQuantile p.val)) := by
  have h := continuous_finiteWeilDiagonalPoint.continuousAt.tendsto.comp
    (tendsto_finiteWeilCanonicalProjectedIndex_quantile t p)
  apply h.congr_dist
  simpa only [Function.comp_apply, dist_comm] using
    tendsto_finiteWeilCanonicalJointQuantile_transverse_zero t p

theorem ae_tendsto_finiteWeilCanonicalJointQuantile_gaussian (t : ℕ → ℕ) :
    ∀ᵐ p ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Tendsto (fun r => finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) p)
        atTop (𝓝 (finiteWeilDiagonalGaussianQuantile p)) := by
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  exact Eventually.of_forall fun p hp => tendsto_finiteWeilCanonicalJointQuantile_gaussian t ⟨p, hp⟩

theorem tendsto_finiteWeilCanonicalJointQuantile_continuous_test (t : ℕ → ℕ)
    (p : {p : ℝ // p ∈ Ioo 0 1}) (f : {f : EuclideanSpace ℝ (Fin 2) → ℝ // Continuous f}) :
    Tendsto (fun r => f.val (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) p.val))
      atTop (𝓝 (f.val (finiteWeilDiagonalGaussianQuantile p.val))) :=
  f.property.continuousAt.tendsto.comp (tendsto_finiteWeilCanonicalJointQuantile_gaussian t p)

theorem tendsto_finiteWeilCanonicalJointQuantile_lipschitz_gap_zero (t : ℕ → ℕ)
    (p : {p : ℝ // p ∈ Ioo 0 1}) (L : NNReal)
    (f : ℕ → {f : EuclideanSpace ℝ (Fin 2) → ℝ // LipschitzWith L f}) :
    Tendsto (fun r => |(f r).val (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) p.val) -
      (f r).val (finiteWeilDiagonalGaussianQuantile p.val)|) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => abs_nonneg _)
    (g := fun r => (L : ℝ) * dist (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) p.val)
      (finiteWeilDiagonalGaussianQuantile p.val))
  · intro r
    simpa only [Real.dist_eq] using (f r).property.dist_le_mul
      (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) p.val)
      (finiteWeilDiagonalGaussianQuantile p.val)
  · simpa only [mul_zero] using
      (tendsto_iff_dist_tendsto_zero.mp (tendsto_finiteWeilCanonicalJointQuantile_gaussian t p)).const_mul (L : ℝ)

end RHTower
