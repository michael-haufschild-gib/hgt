import GaloisForLFunctions.RHTower.WeilLogShiftJointLift
import GaloisForLFunctions.RHTower.WeilLogShiftGaussianCoupling

/-! An actual Euclidean coupling is the measurable lift of the scalar Gaussian coupling. -/

open MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

def finiteWeilCanonicalJointGaussianTransportMap (r k : ℕ) (z : ℝ × ℝ) :
    EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) :=
  (finiteWeilCanonicalJointLift r k z.1, finiteWeilDiagonalPoint z.2)

theorem finiteWeilCanonicalJointGaussianTransportMap_measurable (r k : ℕ) :
    Measurable (finiteWeilCanonicalJointGaussianTransportMap r k) :=
  ((finiteWeilCanonicalJointLift_measurable r k).comp measurable_fst).prodMk
    (continuous_finiteWeilDiagonalPoint.measurable.comp measurable_snd)

def finiteWeilCanonicalJointGaussianCoupling (r k : ℕ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
  ProbabilityMeasure.map (finiteWeilCanonicalGaussianCoupling r k 1 0)
    (finiteWeilCanonicalJointGaussianTransportMap_measurable r k).aemeasurable

theorem finiteWeilCanonicalJointGaussianCoupling_isCoupling (r k : ℕ) :
    IsCoupling
      (finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2)))
      (finiteWeilDiagonalGaussian : Measure (EuclideanSpace ℝ (Fin 2)))
      (finiteWeilCanonicalJointGaussianCoupling r k :
        Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) := by
  have hπ := finiteWeilCanonicalGaussianCoupling_isCoupling r k 1 0
  constructor
  · change Measure.map Prod.fst (Measure.map (finiteWeilCanonicalJointGaussianTransportMap r k)
      (finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ))) = _
    rw [Measure.map_map measurable_fst (finiteWeilCanonicalJointGaussianTransportMap_measurable r k)]
    change Measure.map (finiteWeilCanonicalJointLift r k ∘ Prod.fst)
      (finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ)) = _
    rw [← Measure.map_map (finiteWeilCanonicalJointLift_measurable r k) measurable_fst,
      hπ.1, finiteWeilCanonicalJointLift_map]
  · change Measure.map Prod.snd (Measure.map (finiteWeilCanonicalJointGaussianTransportMap r k)
      (finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ))) = _
    rw [Measure.map_map measurable_snd (finiteWeilCanonicalJointGaussianTransportMap_measurable r k)]
    change Measure.map (finiteWeilDiagonalPoint ∘ Prod.snd)
      (finiteWeilCanonicalGaussianCoupling r k 1 0 : Measure (ℝ × ℝ)) = _
    rw [← Measure.map_map continuous_finiteWeilDiagonalPoint.measurable measurable_snd,
      hπ.2, finiteWeilDiagonalGaussian_eq_map_projected]

end RHTower
