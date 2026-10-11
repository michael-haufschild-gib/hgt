import GaloisForLFunctions.RHTower.WeilLogShiftJointDiagonalQuadratic
import GaloisForLFunctions.RHTower.WeilLogShiftGaussianQuadraticLimit
import GaloisForLFunctions.RHTower.WeilLogShiftFluctuationRankOneLimit

/-! The actual joint Gaussian coupling has vanishing mean-square distance. -/

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section
namespace RHTower

theorem finiteWeilCanonicalJointGaussianTransportMap_dist_sq_integrable (r k : ℕ) :
    Integrable (fun z : ℝ × ℝ =>
      dist (finiteWeilCanonicalJointLift r k z.1) (finiteWeilDiagonalPoint z.2) ^ 2)
      (finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ)) := by
  have hmajor := ((finiteWeilCanonicalJointLiftDisplacement_sq_fst_integrable r k).const_mul (2 : ℝ)).add
    ((finiteWeilCanonicalGaussianCoupling_quadratic_integrable r k 1 0).const_mul (4 : ℝ))
  apply hmajor.mono'
    ((((finiteWeilCanonicalJointLift_measurable r k).comp measurable_fst).dist
      (continuous_finiteWeilDiagonalPoint.measurable.comp measurable_snd)).pow_const (2 : ℕ)).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact finiteWeilCanonicalJointGaussianTransportMap_dist_sq_bound r k z

theorem finiteWeilCanonicalJointGaussianCoupling_quadratic_integrable (r k : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => dist z.1 z.2 ^ 2)
      (finiteWeilCanonicalJointGaussianCoupling r k :
        Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) := by
  exact (integrable_map_measure ((continuous_fst.dist continuous_snd).pow 2).aestronglyMeasurable
    (finiteWeilCanonicalJointGaussianTransportMap_measurable r k).aemeasurable).mpr
    (finiteWeilCanonicalJointGaussianTransportMap_dist_sq_integrable r k)

def finiteWeilCanonicalJointGaussianQuadraticCost (r k : ℕ) : ℝ :=
  ∫ z, dist z.1 z.2 ^ 2 ∂(finiteWeilCanonicalJointGaussianCoupling r k :
    Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))

theorem finiteWeilCanonicalJointGaussianQuadraticCost_nonneg (r k : ℕ) :
    0 ≤ finiteWeilCanonicalJointGaussianQuadraticCost r k :=
  integral_nonneg fun z => sq_nonneg (dist z.1 z.2)

theorem finiteWeilCanonicalJointGaussianQuadraticCost_bound (r k : ℕ) :
    finiteWeilCanonicalJointGaussianQuadraticCost r k ≤
      2 * (finiteWeilCanonicalFluctuationResidual r k / ((r + 1 : ℕ) : ℝ)) +
        4 * finiteWeilCanonicalGaussianQuadraticCost r k 1 0 := by
  have hcontinuous : Continuous
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => dist z.1 z.2 ^ 2) :=
    (continuous_fst.dist continuous_snd).pow 2
  change (∫ z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2), dist z.1 z.2 ^ 2
    ∂Measure.map (finiteWeilCanonicalJointGaussianTransportMap r k)
      (finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ))) ≤ _
  rw [integral_map (finiteWeilCanonicalJointGaussianTransportMap_measurable r k).aemeasurable
    hcontinuous.aestronglyMeasurable]
  change (∫ z : ℝ × ℝ,
    dist (finiteWeilCanonicalJointLift r k z.1) (finiteWeilDiagonalPoint z.2) ^ 2
    ∂(finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ))) ≤ _
  have h1 := (finiteWeilCanonicalJointLiftDisplacement_sq_fst_integrable r k).const_mul (2 : ℝ)
  have h2 := (finiteWeilCanonicalGaussianCoupling_quadratic_integrable r k 1 0).const_mul (4 : ℝ)
  calc
    _ ≤ ∫ z : ℝ × ℝ, 2 * finiteWeilCanonicalJointLiftDisplacement r k z.1 ^ 2 + 4 * |z.1 - z.2| ^ 2
        ∂(finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ)) :=
      integral_mono (finiteWeilCanonicalJointGaussianTransportMap_dist_sq_integrable r k)
        (h1.add h2) (finiteWeilCanonicalJointGaussianTransportMap_dist_sq_bound r k)
    _ = _ := by
      rw [integral_add h1 h2, integral_const_mul, integral_const_mul,
        finiteWeilCanonicalJointLiftDisplacement_sq_fst_integral]
      rfl

theorem finiteWeilCanonicalJointGaussianQuadraticCost_quadratic_bound (r t : ℕ) :
    finiteWeilCanonicalJointGaussianQuadraticCost r (2 * (r + 1) ^ 2 + t) ≤
      2 / ((r + 1 : ℕ) : ℝ) +
        4 * finiteWeilCanonicalGaussianQuadraticCost r (2 * (r + 1) ^ 2 + t) 1 0 := by
  have h := div_le_div_of_nonneg_right (finiteWeilCanonicalFluctuationResidual_quadratic_bound r t)
    (show (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) by positivity)
  have hc := finiteWeilCanonicalJointGaussianQuadraticCost_bound r (2 * (r + 1) ^ 2 + t)
  calc
    _ ≤ 2 * (finiteWeilCanonicalFluctuationResidual r (2 * (r + 1) ^ 2 + t) / ((r + 1 : ℕ) : ℝ)) +
        4 * finiteWeilCanonicalGaussianQuadraticCost r (2 * (r + 1) ^ 2 + t) 1 0 := hc
    _ ≤ 2 * (1 / ((r + 1 : ℕ) : ℝ)) +
        4 * finiteWeilCanonicalGaussianQuadraticCost r (2 * (r + 1) ^ 2 + t) 1 0 := by
      linarith only [h]
    _ = _ := by ring

theorem finiteWeilCanonicalJointGaussianCost_sq_le_quadratic (r k : ℕ) :
    finiteWeilCanonicalJointGaussianCost r k ^ 2 ≤
      finiteWeilCanonicalJointGaussianQuadraticCost r k := by
  have hm : MemLp (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => dist z.1 z.2) 2
      (finiteWeilCanonicalJointGaussianCoupling r k :
        Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) :=
    (memLp_two_iff_integrable_sq (continuous_fst.dist continuous_snd).aestronglyMeasurable).mpr
      (finiteWeilCanonicalJointGaussianCoupling_quadratic_integrable r k)
  have h := variance_nonneg (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => dist z.1 z.2)
    (finiteWeilCanonicalJointGaussianCoupling r k :
      Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
  rw [variance_eq_sub hm] at h
  change 0 ≤ finiteWeilCanonicalJointGaussianQuadraticCost r k -
    finiteWeilCanonicalJointGaussianCost r k ^ 2 at h
  exact sub_nonneg.mp h

theorem finiteWeilCanonicalJointGaussianCost_le_sqrt_quadratic (r k : ℕ) :
    finiteWeilCanonicalJointGaussianCost r k ≤
      Real.sqrt (finiteWeilCanonicalJointGaussianQuadraticCost r k) :=
  (Real.le_sqrt (finiteWeilCanonicalJointGaussianCost_nonneg r k)
    (finiteWeilCanonicalJointGaussianQuadraticCost_nonneg r k)).mpr
    (finiteWeilCanonicalJointGaussianCost_sq_le_quadratic r k)

theorem tendsto_finiteWeilCanonicalJointGaussianQuadraticCost_zero (t : ℕ → ℕ) :
    Tendsto (fun r => finiteWeilCanonicalJointGaussianQuadraticCost r (2 * (r + 1) ^ 2 + t r))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun r => finiteWeilCanonicalJointGaussianQuadraticCost_nonneg r _)
    (fun r => finiteWeilCanonicalJointGaussianQuadraticCost_bound r _)
  simpa only [mul_zero, add_zero] using
    ((tendsto_finiteWeilCanonicalFluctuationResidual_normalized_zero t).const_mul (2 : ℝ)).add
      ((tendsto_finiteWeilCanonicalGaussianQuadraticCost_zero t 1 0).const_mul (4 : ℝ))

end RHTower
