import GaloisForLFunctions.RHTower.WeilLogShiftJointTransportGeometry
import GaloisForLFunctions.RHTower.WeilLogShiftObservableCoupling
import GaloisForLFunctions.RHTower.WeilLogShiftProjectedWeakLimit

/-! A measurable finite lift recovers every joint atom from its first coordinate. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace RHTower

def finiteWeilCanonicalJointLift (r k : ℕ) (x : ℝ) : EuclideanSpace ℝ (Fin 2) := by
  classical
  exact ∑ i : Fin (r + 1), if x = finiteWeilCanonicalFluctuationPoint r k i 0
    then finiteWeilCanonicalFluctuationPoint r k i else 0

theorem finiteWeilCanonicalJointLift_measurable (r k : ℕ) :
    Measurable (finiteWeilCanonicalJointLift r k) := by
  classical
  exact Finset.measurable_sum Finset.univ fun i _ =>
    Measurable.ite (measurableSet_singleton _) measurable_const measurable_const

theorem finiteWeilCanonicalJointLift_at_atom (r k : ℕ) (i : Fin (r + 1)) :
    finiteWeilCanonicalJointLift r k (finiteWeilCanonicalFluctuationPoint r k i 0) =
      finiteWeilCanonicalFluctuationPoint r k i := by
  classical
  unfold finiteWeilCanonicalJointLift
  rw [Finset.sum_eq_single i]
  · exact if_pos rfl
  · intro j _ hji
    exact if_neg fun h => hji ((finiteWeilCanonicalFluctuationPoint_fst_injective r k h).symm)
  · simp

theorem finiteWeilCanonicalJointLift_map (r k : ℕ) :
    Measure.map (finiteWeilCanonicalJointLift r k)
      (finiteWeilCanonicalProjectedProbabilityLaw r k 1 0 : Measure ℝ) =
      (finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2))) := by
  rw [finiteWeilCanonicalProjectedProbabilityLaw,
    finiteWeilCanonicalObservableLaw_map r k _ _ (finiteWeilCanonicalJointLift_measurable r k)]
  unfold finiteWeilCanonicalJointProbabilityLaw
  apply congrArg (fun h : Fin (r + 1) → EuclideanSpace ℝ (Fin 2) =>
    (finiteWeilCanonicalObservableLaw r k h : Measure (EuclideanSpace ℝ (Fin 2))))
  funext i
  simp only [Function.comp_apply, one_mul, zero_mul, add_zero]
  exact finiteWeilCanonicalJointLift_at_atom r k i

theorem finiteWeilDiagonalGaussian_eq_map_projected :
    Measure.map finiteWeilDiagonalPoint (finiteWeilProjectedGaussian 1 0 : Measure ℝ) =
      (finiteWeilDiagonalGaussian : Measure (EuclideanSpace ℝ (Fin 2))) := by
  have hv : NNReal.mk (((1 : ℝ) + 0) ^ 2 / 4) (by positivity) = (1 / 4 : NNReal) := by
    ext
    norm_num [NNReal.coe_mk, NNReal.coe_div]
  change Measure.map finiteWeilDiagonalPoint (gaussianReal 0 _) =
    Measure.map finiteWeilDiagonalPoint (gaussianReal 0 (1 / 4))
  rw [hv]

end RHTower
