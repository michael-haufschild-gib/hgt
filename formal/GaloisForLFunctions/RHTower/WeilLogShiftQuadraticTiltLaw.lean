import GaloisForLFunctions.HTGeometry.GaussianQuadraticTilt
import GaloisForLFunctions.HTGeometry.BoundedWeightedConvergence
import GaloisForLFunctions.RHTower.WeilLogShiftJointQuadraticLaw

/-! Actual finite quadratic tilts are probability laws; their candidate Gaussian has explicit variance. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

def finiteWeilCanonicalJointQuadraticTilt (r k : ℕ) (a b d : ℝ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)) :=
  ⟨(finiteWeilCanonicalJointProbabilityLaw r k : Measure _).tilted (finiteWeilJointQuadratic a b d),
    isProbabilityMeasure_tilted (finiteWeilCanonicalJoint_quadratic_exponential_integrable r k a b d)⟩

def finiteWeilQuadraticTiltVariance (s : {s : ℝ // s < 2}) : NNReal :=
  ⟨1 / (4 - 2 * s.val), by
    have hden : 0 < 4 - 2 * s.val := by linarith only [s.property]
    positivity⟩

theorem finiteWeilQuadraticTiltVariance_pos (s : {s : ℝ // s < 2}) :
    0 < finiteWeilQuadraticTiltVariance s := by
  change (0 : ℝ) < 1 / (4 - 2 * s.val)
  have hden : 0 < 4 - 2 * s.val := by linarith only [s.property]
  positivity

def finiteWeilQuadraticTiltGaussian (s : {s : ℝ // s < 2}) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)) :=
  ProbabilityMeasure.map
    (⟨gaussianReal 0 (finiteWeilQuadraticTiltVariance s), inferInstance⟩ : ProbabilityMeasure ℝ)
    continuous_finiteWeilDiagonalPoint.measurable.aemeasurable

theorem finiteWeilProjectedIndexGaussian_quadratic_tilt (s : {s : ℝ // s < 2}) :
    (finiteWeilProjectedGaussian 1 0 : Measure ℝ).tilted (fun x => s.val * x ^ 2) =
      gaussianReal 0 (finiteWeilQuadraticTiltVariance s) := by
  have hbase : (finiteWeilProjectedGaussian 1 0 : Measure ℝ) = gaussianReal 0 (1 / 4) := by
    change gaussianReal 0 _ = _
    congr 1
    ext
    norm_num
  have hcoef : 1 / (2 * ((1 / 4 : NNReal) : ℝ)) -
      1 / (2 * (finiteWeilQuadraticTiltVariance s : ℝ)) = s.val := by
    change 1 / (2 * (1 / 4 : ℝ)) - 1 / (2 * (1 / (4 - 2 * s.val))) = s.val
    field_simp
    ring
  rw [hbase, ← hcoef]
  exact gaussianZero_quadratic_tilt_precision_change _ _ (by norm_num)
    (ne_of_gt (finiteWeilQuadraticTiltVariance_pos s))

theorem finiteWeilCanonicalJointQuadratic_partition_pos (r k : ℕ) (a b d : ℝ) :
    0 < ∫ z, Real.exp (finiteWeilJointQuadratic a b d z)
      ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2))) :=
  integral_exp_pos (finiteWeilCanonicalJoint_quadratic_exponential_integrable r k a b d)

theorem finiteWeilCanonicalJointQuadraticTilt_integral (r k : ℕ) (a b d : ℝ)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) :
    (∫ z, f z ∂(finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure _)) =
      (∫ z, Real.exp (finiteWeilJointQuadratic a b d z) * f z
        ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure _)) /
      ∫ z, Real.exp (finiteWeilJointQuadratic a b d z)
        ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2))) :=
  integral_tilted_real_eq_ratio _ _ _

theorem finiteWeilQuadraticTiltGaussian_integral (a b : ℝ)
    (d : {d : ℝ // a + 2 * b + d < 2})
    (f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin 2)) ℝ) :
    (∫ z, f z ∂(finiteWeilQuadraticTiltGaussian ⟨a + 2 * b + d.val, d.property⟩ : Measure _)) =
      (∫ z, Real.exp (finiteWeilJointQuadratic a b d.val z) * f z
        ∂(finiteWeilDiagonalGaussian : Measure (EuclideanSpace ℝ (Fin 2)))) /
      Real.sqrt (2 / (2 - (a + 2 * b + d.val))) := by
  change (∫ z, f z ∂Measure.map finiteWeilDiagonalPoint
    (gaussianReal 0 (finiteWeilQuadraticTiltVariance ⟨a + 2 * b + d.val, d.property⟩))) = _
  rw [integral_map continuous_finiteWeilDiagonalPoint.measurable.aemeasurable
    f.continuous.aestronglyMeasurable,
    ← finiteWeilProjectedIndexGaussian_quadratic_tilt,
    integral_tilted_real_eq_ratio,
    finiteWeilProjectedIndexGaussian_quadratic_exponential_integral]
  congr 1
  rw [← finiteWeilDiagonalGaussian_eq_map_projected,
    integral_map (f := fun z => Real.exp (finiteWeilJointQuadratic a b d.val z) * f z)
      continuous_finiteWeilDiagonalPoint.measurable.aemeasurable
      ((Real.continuous_exp.comp (continuous_finiteWeilJointQuadratic a b d.val)).mul
        f.continuous).aestronglyMeasurable]
  simp only [finiteWeilJointQuadratic_diagonal]

end RHTower
