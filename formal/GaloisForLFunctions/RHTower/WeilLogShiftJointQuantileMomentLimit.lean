import GaloisForLFunctions.HTGeometry.IntegralVariableEnvelope
import GaloisForLFunctions.RHTower.WeilLogShiftQuantileEnvelopeIntegral

/-! Every positive integer moment of the same joint quantile error tends to zero, both on the
common uniform space and under the actual joint Gaussian coupling. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem finiteWeilCanonicalJointQuantile_distance_pow_measurable (r k p : ℕ) :
    Measurable (fun u : ℝ => dist (finiteWeilCanonicalJointQuantile r k u)
      (finiteWeilDiagonalGaussianQuantile u) ^ p) :=
  ((finiteWeilCanonicalJointQuantile_measurable r k).dist
    finiteWeilDiagonalGaussianQuantile_measurable).pow_const p

theorem finiteWeilCanonicalJointQuantile_distance_pow_integrable (r t p : ℕ) :
    Integrable (fun u : ℝ => dist
      (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t) u)
      (finiteWeilDiagonalGaussianQuantile u) ^ p) (volume.restrict (Ioo (0 : ℝ) 1)) := by
  apply (finiteWeilCanonicalJointQuantile_envelope_integrable r (2 * (r + 1) ^ 2 + t) p).mono'
    (finiteWeilCanonicalJointQuantile_distance_pow_measurable r (2 * (r + 1) ^ 2 + t) p).aestronglyMeasurable
  refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun u hu => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg dist_nonneg p)]
  exact finiteWeilCanonicalJointQuantile_pow_envelope_bound r t p ⟨u, hu⟩

theorem tendsto_finiteWeilCanonicalJointQuantile_moment_gap_zero (t : ℕ → ℕ) (p : ℕ) :
    Tendsto (fun r => ∫ u : ℝ, dist
      (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) u)
      (finiteWeilDiagonalGaussianQuantile u) ^ (p + 1)
        ∂(volume.restrict (Ioo (0 : ℝ) 1))) atTop (𝓝 0) := by
  apply tendsto_integral_zero_of_variable_envelope
    (g := fun r u => finiteWeilQuantileMomentEnvelope (p + 1)
      (quantile (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ) u)
      (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u))
    (G := fun u => finiteWeilQuantileMomentEnvelope (p + 1)
      (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u)
      (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u))
  · intro r
    exact (finiteWeilCanonicalJointQuantile_distance_pow_measurable r
      (2 * (r + 1) ^ 2 + t r) (p + 1)).aestronglyMeasurable
  · intro r
    exact Eventually.of_forall fun u => pow_nonneg dist_nonneg (p + 1)
  · intro r
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun u hu => ?_)
    exact finiteWeilCanonicalJointQuantile_pow_envelope_bound r (t r) (p + 1) ⟨u, hu⟩
  · intro r
    exact finiteWeilCanonicalJointQuantile_envelope_integrable r (2 * (r + 1) ^ 2 + t r) (p + 1)
  · exact finiteWeilGaussianQuantile_envelope_integrable (p + 1)
  · exact Eventually.of_forall fun u => finiteWeilQuantileMomentEnvelope_nonneg (p + 1) _ _
  · filter_upwards [ae_tendsto_finiteWeilCanonicalJointQuantile_gaussian t] with u hu
    simpa only [zero_pow (Nat.succ_ne_zero p)] using
      (tendsto_iff_dist_tendsto_zero.mp hu).pow (p + 1)
  · exact ae_tendsto_finiteWeilCanonicalJointQuantile_envelope t (p + 1)
  · exact tendsto_finiteWeilCanonicalJointQuantile_envelope_integral t (p + 1)

theorem finiteWeilCanonicalJointQuantile_integral_dist_pow (r k p : ℕ) :
    (∫ u : ℝ, dist (finiteWeilCanonicalJointQuantile r k u)
      (finiteWeilDiagonalGaussianQuantile u) ^ p ∂(volume.restrict (Ioo (0 : ℝ) 1))) =
      ∫ z, dist z.1 z.2 ^ p ∂(finiteWeilCanonicalJointGaussianCoupling r k :
        Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) := by
  have hm := (finiteWeilCanonicalJointQuantile_measurable r k).prodMk
    finiteWeilDiagonalGaussianQuantile_measurable
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      dist z.1 z.2 ^ p) := (continuous_fst.dist continuous_snd).pow p
  have h := integral_map (μ := volume.restrict (Ioo (0 : ℝ) 1)) hm.aemeasurable hc.aestronglyMeasurable
  rw [finiteWeilCanonicalJointQuantile_pair_law] at h
  exact h.symm

theorem finiteWeilCanonicalJointGaussianCoupling_pow_integrable (r t p : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => dist z.1 z.2 ^ p)
      (finiteWeilCanonicalJointGaussianCoupling r (2 * (r + 1) ^ 2 + t) : Measure _) := by
  have hm := (finiteWeilCanonicalJointQuantile_measurable r (2 * (r + 1) ^ 2 + t)).prodMk
    finiteWeilDiagonalGaussianQuantile_measurable
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      dist z.1 z.2 ^ p) := (continuous_fst.dist continuous_snd).pow p
  rw [← finiteWeilCanonicalJointQuantile_pair_law]
  exact (integrable_map_measure hc.aestronglyMeasurable hm.aemeasurable).mpr
    (finiteWeilCanonicalJointQuantile_distance_pow_integrable r t p)

theorem tendsto_finiteWeilCanonicalJointGaussianCoupling_moment_gap_zero (t : ℕ → ℕ) (p : ℕ) :
    Tendsto (fun r => ∫ z, dist z.1 z.2 ^ (p + 1)
      ∂(finiteWeilCanonicalJointGaussianCoupling r (2 * (r + 1) ^ 2 + t r) :
        Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))) atTop (𝓝 0) :=
  (tendsto_finiteWeilCanonicalJointQuantile_moment_gap_zero t p).congr fun r =>
    finiteWeilCanonicalJointQuantile_integral_dist_pow r (2 * (r + 1) ^ 2 + t r) (p + 1)

end RHTower
