import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltDensity

/-! Every subcritical actual finite quadratic tilt converges to an explicit diagonal Gaussian. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem finiteWeilCanonicalQuadraticTiltQuantile_integral (r k : ℕ) (a b d : ℝ)
    (f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin 2)) ℝ) :
    (∫ u, finiteWeilCanonicalQuadraticTiltQuantileDensity r k a b d u *
      f (finiteWeilCanonicalJointQuantile r k u) ∂(volume.restrict (Ioo (0 : ℝ) 1))) =
      ∫ z, f z ∂(finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure _) := by
  let Z := ∫ z, Real.exp (finiteWeilJointQuadratic a b d z)
    ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2)))
  have h := integral_map (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (φ := finiteWeilCanonicalJointQuantile r k)
    (f := fun z => (Real.exp (finiteWeilJointQuadratic a b d z) / Z) * f z)
    (finiteWeilCanonicalJointQuantile_measurable r k).aemeasurable
    (((Real.continuous_exp.comp (continuous_finiteWeilJointQuadratic a b d)).div_const Z).mul
      f.continuous).aestronglyMeasurable
  rw [finiteWeilCanonicalJointQuantile_law] at h
  change (∫ u, (Real.exp (finiteWeilJointQuadratic a b d
    (finiteWeilCanonicalJointQuantile r k u)) / Z) * f (finiteWeilCanonicalJointQuantile r k u)
      ∂(volume.restrict (Ioo (0 : ℝ) 1))) = _
  rw [← h]
  change _ = ∫ z, f z ∂((finiteWeilCanonicalJointProbabilityLaw r k : Measure _).tilted
    (finiteWeilJointQuadratic a b d))
  rw [integral_tilted]
  rfl

theorem finiteWeilGaussianQuadraticTiltQuantile_integral (a b : ℝ)
    (d : {d : ℝ // a + 2 * b + d < 2})
    (f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin 2)) ℝ) :
    (∫ u, finiteWeilGaussianQuadraticTiltQuantileDensity a b d u *
      f (finiteWeilDiagonalGaussianQuantile u) ∂(volume.restrict (Ioo (0 : ℝ) 1))) =
      ∫ z, f z ∂(finiteWeilQuadraticTiltGaussian ⟨a + 2 * b + d.val, d.property⟩ : Measure _) := by
  let Z := Real.sqrt (2 / (2 - (a + 2 * b + d.val)))
  have h := integral_map (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (φ := finiteWeilDiagonalGaussianQuantile)
    (f := fun z => (Real.exp (finiteWeilJointQuadratic a b d.val z) / Z) * f z)
    finiteWeilDiagonalGaussianQuantile_measurable.aemeasurable
    (((Real.continuous_exp.comp (continuous_finiteWeilJointQuadratic a b d.val)).div_const Z).mul
      f.continuous).aestronglyMeasurable
  rw [finiteWeilDiagonalGaussianQuantile_law] at h
  change (∫ u, (Real.exp (finiteWeilJointQuadratic a b d.val
    (finiteWeilDiagonalGaussianQuantile u)) / Z) * f (finiteWeilDiagonalGaussianQuantile u)
      ∂(volume.restrict (Ioo (0 : ℝ) 1))) = _
  rw [← h, finiteWeilQuadraticTiltGaussian_integral]
  have hnorm : (fun z => (Real.exp (finiteWeilJointQuadratic a b d.val z) / Z) * f z) =
      (fun z => (Real.exp (finiteWeilJointQuadratic a b d.val z) * f z) * Z⁻¹) := by
    funext z
    ring
  rw [hnorm, integral_mul_const, div_eq_mul_inv]

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_integral
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin 2)) ℝ) :
    Tendsto (fun r => ∫ z, f z ∂(finiteWeilCanonicalJointQuadraticTilt
      r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure _)) atTop
        (𝓝 (∫ z, f z ∂(finiteWeilQuadraticTiltGaussian
          ⟨a + 2 * b + d.val, d.property⟩ : Measure (EuclideanSpace ℝ (Fin 2))))) := by
  have h := tendsto_integral_weighted_boundedContinuousFunction
    (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (fun r => finiteWeilCanonicalJointQuantile_measurable r (2 * (r + 1) ^ 2 + t r))
    finiteWeilDiagonalGaussianQuantile_measurable
    (fun r => finiteWeilCanonicalQuadraticTiltQuantileDensity_integrable
      r (2 * (r + 1) ^ 2 + t r) a b d.val)
    (finiteWeilGaussianQuadraticTiltQuantileDensity_integrable a b d)
    (fun r => Eventually.of_forall fun _ => div_nonneg (Real.exp_pos _).le
      (finiteWeilCanonicalJointQuadratic_partition_pos r _ a b d.val).le)
    (Eventually.of_forall fun _ => div_nonneg (Real.exp_pos _).le
      (finiteWeilQuadraticTilt_normalizer_pos ⟨a + 2 * b + d.val, d.property⟩).le)
    (ae_tendsto_finiteWeilCanonicalJointQuantile_gaussian t)
    (ae_tendsto_finiteWeilCanonicalQuadraticTiltQuantileDensity t a b d)
    (by
      simp only [finiteWeilCanonicalQuadraticTiltQuantileDensity_integral,
        finiteWeilGaussianQuadraticTiltQuantileDensity_integral]
      exact tendsto_const_nhds) f
  simpa only [finiteWeilCanonicalQuadraticTiltQuantile_integral,
    finiteWeilGaussianQuadraticTiltQuantile_integral] using h

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_gaussian
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) :
    Tendsto (fun r => finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val)
      atTop (𝓝 (finiteWeilQuadraticTiltGaussian ⟨a + 2 * b + d.val, d.property⟩)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  exact tendsto_finiteWeilCanonicalJointQuadraticTilt_integral t a b d

end RHTower
