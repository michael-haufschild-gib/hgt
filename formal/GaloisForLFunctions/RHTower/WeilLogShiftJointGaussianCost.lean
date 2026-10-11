import GaloisForLFunctions.RHTower.WeilLogShiftJointGaussianCoupling
import GaloisForLFunctions.RHTower.WeilLogShiftGaussianMeanGap

/-! Joint coupling cost splits into transverse displacement and scalar Gaussian transport. -/

open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped BigOperators

noncomputable section
namespace RHTower

def finiteWeilCanonicalJointLiftDisplacement (r k : ℕ) (x : ℝ) : ℝ :=
  dist (finiteWeilCanonicalJointLift r k x) (finiteWeilDiagonalPoint x)

theorem finiteWeilCanonicalJointLiftDisplacement_measurable (r k : ℕ) :
    Measurable (finiteWeilCanonicalJointLiftDisplacement r k) :=
  (finiteWeilCanonicalJointLift_measurable r k).dist continuous_finiteWeilDiagonalPoint.measurable

theorem finiteWeilCanonicalJointLiftDisplacement_fst_integrable (r k : ℕ) :
    Integrable (fun z : ℝ × ℝ => finiteWeilCanonicalJointLiftDisplacement r k z.1)
      (finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ)) := by
  have h : Integrable (finiteWeilCanonicalJointLiftDisplacement r k)
      ((finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ)).map Prod.fst) := by
    rw [(finiteWeilCanonicalGaussianCoupling_isCoupling r k 1 0).1]
    exact finiteWeilCanonicalProjectedProbabilityLaw_integrable r k 1 0 _
  exact (integrable_map_measure
    (finiteWeilCanonicalJointLiftDisplacement_measurable r k).aestronglyMeasurable
    measurable_fst.aemeasurable).mp h

theorem finiteWeilCanonicalJointLiftDisplacement_fst_integral (r k : ℕ) :
    (∫ z, finiteWeilCanonicalJointLiftDisplacement r k z.1
      ∂(finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ))) =
      finiteWeilCanonicalJointDiagonalGap r k := by
  rw [← integral_map measurable_fst.aemeasurable
    (finiteWeilCanonicalJointLiftDisplacement_measurable r k).aestronglyMeasurable,
    (finiteWeilCanonicalGaussianCoupling_isCoupling r k 1 0).1,
    finiteWeilCanonicalProjectedProbabilityLaw, finiteWeilCanonicalObservableLaw_integral_real]
  simp only [one_mul, zero_mul, add_zero]
  change (∑ i, finiteWeilCanonicalEdgeMass r k i *
    finiteWeilCanonicalJointLiftDisplacement r k (finiteWeilCanonicalFluctuationPoint r k i 0)) = _
  simp only [finiteWeilCanonicalJointLiftDisplacement, finiteWeilCanonicalJointLift_at_atom,
    finiteWeilCanonicalJointDiagonalGap]

theorem finiteWeilCanonicalJointGaussianTransportMap_dist_bound (r k : ℕ) (z : ℝ × ℝ) :
    dist (finiteWeilCanonicalJointLift r k z.1) (finiteWeilDiagonalPoint z.2) ≤
      finiteWeilCanonicalJointLiftDisplacement r k z.1 + 2 * |z.1 - z.2| := by
  have h : dist (finiteWeilDiagonalPoint z.1) (finiteWeilDiagonalPoint z.2) ≤
      (2 : ℝ) * |z.1 - z.2| := by
    simpa only [Real.dist_eq, NNReal.coe_ofNat] using
      finiteWeilDiagonalPoint_lipschitz.dist_le_mul z.1 z.2
  have ht := dist_triangle (finiteWeilCanonicalJointLift r k z.1)
    (finiteWeilDiagonalPoint z.1) (finiteWeilDiagonalPoint z.2)
  unfold finiteWeilCanonicalJointLiftDisplacement
  linarith only [h, ht]

theorem finiteWeilCanonicalJointGaussianTransportMap_dist_integrable (r k : ℕ) :
    Integrable (fun z : ℝ × ℝ =>
      dist (finiteWeilCanonicalJointLift r k z.1) (finiteWeilDiagonalPoint z.2))
      (finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ)) := by
  have hmajor := (finiteWeilCanonicalJointLiftDisplacement_fst_integrable r k).add
    ((finiteWeilCanonicalGaussianCoupling_gap_integrable r k 1 0).const_mul (2 : ℝ))
  apply hmajor.mono'
    (((finiteWeilCanonicalJointLift_measurable r k).comp measurable_fst).dist
      (continuous_finiteWeilDiagonalPoint.measurable.comp measurable_snd)).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
  exact finiteWeilCanonicalJointGaussianTransportMap_dist_bound r k z

theorem finiteWeilCanonicalJointGaussianCoupling_dist_integrable (r k : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => dist z.1 z.2)
      (finiteWeilCanonicalJointGaussianCoupling r k :
        Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) := by
  exact (integrable_map_measure (continuous_fst.dist continuous_snd).aestronglyMeasurable
    (finiteWeilCanonicalJointGaussianTransportMap_measurable r k).aemeasurable).mpr
    (finiteWeilCanonicalJointGaussianTransportMap_dist_integrable r k)

def finiteWeilCanonicalJointGaussianCost (r k : ℕ) : ℝ :=
  ∫ z, dist z.1 z.2 ∂(finiteWeilCanonicalJointGaussianCoupling r k :
    Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))

theorem finiteWeilCanonicalJointGaussianCost_nonneg (r k : ℕ) :
    0 ≤ finiteWeilCanonicalJointGaussianCost r k :=
  integral_nonneg fun _ => dist_nonneg

theorem finiteWeilCanonicalJointGaussianCost_bound (r k : ℕ) :
    finiteWeilCanonicalJointGaussianCost r k ≤
      finiteWeilCanonicalJointDiagonalGap r k + 2 * finiteWeilCanonicalGaussianMeanGap r k 1 0 := by
  change (∫ z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2), dist z.1 z.2
    ∂Measure.map (finiteWeilCanonicalJointGaussianTransportMap r k)
      (finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ))) ≤ _
  rw [integral_map (finiteWeilCanonicalJointGaussianTransportMap_measurable r k).aemeasurable
    (continuous_fst.dist continuous_snd).aestronglyMeasurable]
  change (∫ z : ℝ × ℝ, dist (finiteWeilCanonicalJointLift r k z.1) (finiteWeilDiagonalPoint z.2)
    ∂(finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ))) ≤ _
  have h1 := finiteWeilCanonicalJointLiftDisplacement_fst_integrable r k
  have h2 := (finiteWeilCanonicalGaussianCoupling_gap_integrable r k 1 0).const_mul (2 : ℝ)
  calc
    _ ≤ ∫ z : ℝ × ℝ, finiteWeilCanonicalJointLiftDisplacement r k z.1 + 2 * |z.1 - z.2|
        ∂(finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ)) :=
      integral_mono (finiteWeilCanonicalJointGaussianTransportMap_dist_integrable r k)
        (h1.add h2) (finiteWeilCanonicalJointGaussianTransportMap_dist_bound r k)
    _ = _ := by
      rw [integral_add h1 h2, integral_const_mul,
        finiteWeilCanonicalJointLiftDisplacement_fst_integral]
      rfl

end RHTower
