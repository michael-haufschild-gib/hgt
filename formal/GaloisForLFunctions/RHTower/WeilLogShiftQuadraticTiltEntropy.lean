import GaloisForLFunctions.HTGeometry.TiltedRelativeEntropy
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltResponse

/-! Every pair of actual finite quadratic tilts has finite, explicitly evaluated relative entropy. -/

open MeasureTheory ProbabilityTheory InformationTheory GaloisForLFunctions.HTGeometry
open scoped ENNReal

namespace RHTower

theorem finiteWeilCanonicalJointQuadraticTilt_absolutelyContinuous
    (r k : ℕ) (a b d A B D : ℝ) :
    (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure (EuclideanSpace ℝ (Fin 2))) ≪
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure (EuclideanSpace ℝ (Fin 2))) := by
  simp only [finiteWeilCanonicalJointQuadraticTilt, ProbabilityMeasure.coe_mk]
  exact tilted_absolutelyContinuous_tilted _ _ _
    (finiteWeilCanonicalJoint_quadratic_exponential_integrable r k A B D)

theorem finiteWeilCanonicalJointQuadraticTilt_llr
    (r k : ℕ) (a b d A B D : ℝ) :
    llr (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure (EuclideanSpace ℝ (Fin 2)))
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure (EuclideanSpace ℝ (Fin 2))) =ᵐ[
        (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure (EuclideanSpace ℝ (Fin 2)))]
      fun z => finiteWeilJointQuadratic a b d z - finiteWeilJointQuadratic A B D z -
        Real.log (∫ x, Real.exp (finiteWeilJointQuadratic a b d x)
          ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2)))) +
        Real.log (∫ x, Real.exp (finiteWeilJointQuadratic A B D x)
          ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2)))) := by
  simp only [finiteWeilCanonicalJointQuadraticTilt, ProbabilityMeasure.coe_mk]
  exact llr_tilted_tilted _ _ _
    (finiteWeilCanonicalJoint_quadratic_exponential_integrable r k a b d)
    (finiteWeilCanonicalJoint_quadratic_exponential_integrable r k A B D)

theorem finiteWeilCanonicalJointQuadraticTilt_klDiv
    (r k : ℕ) (a b d A B D : ℝ) :
    klDiv (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure (EuclideanSpace ℝ (Fin 2)))
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure (EuclideanSpace ℝ (Fin 2))) = ENNReal.ofReal
      ((∫ z, finiteWeilJointQuadratic a b d z - finiteWeilJointQuadratic A B D z
        ∂(finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure (EuclideanSpace ℝ (Fin 2)))) -
        Real.log (∫ x, Real.exp (finiteWeilJointQuadratic a b d x)
          ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2)))) +
        Real.log (∫ x, Real.exp (finiteWeilJointQuadratic A B D x)
          ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2))))) := by
  have hfg := finiteWeilCanonicalJointQuadraticTilt_integrable r k a b d
    (fun z => finiteWeilJointQuadratic a b d z - finiteWeilJointQuadratic A B D z)
  simp only [finiteWeilCanonicalJointQuadraticTilt, ProbabilityMeasure.coe_mk] at hfg ⊢
  exact klDiv_tilted_tilted_eq _ _ _
    (finiteWeilCanonicalJoint_quadratic_exponential_integrable r k a b d)
    (finiteWeilCanonicalJoint_quadratic_exponential_integrable r k A B D) hfg

theorem finiteWeilCanonicalJointQuadraticTilt_klDiv_toReal
    (r k : ℕ) (a b d A B D : ℝ) :
    (klDiv (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure (EuclideanSpace ℝ (Fin 2)))
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure (EuclideanSpace ℝ (Fin 2)))).toReal =
      (∫ z, finiteWeilJointQuadratic a b d z - finiteWeilJointQuadratic A B D z
        ∂(finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure (EuclideanSpace ℝ (Fin 2)))) -
        Real.log (∫ x, Real.exp (finiteWeilJointQuadratic a b d x)
          ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2)))) +
        Real.log (∫ x, Real.exp (finiteWeilJointQuadratic A B D x)
          ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2)))) := by
  have hfg := finiteWeilCanonicalJointQuadraticTilt_integrable r k a b d
    (fun z => finiteWeilJointQuadratic a b d z - finiteWeilJointQuadratic A B D z)
  simp only [finiteWeilCanonicalJointQuadraticTilt, ProbabilityMeasure.coe_mk] at hfg ⊢
  exact toReal_klDiv_tilted_tilted_eq _ _ _
    (finiteWeilCanonicalJoint_quadratic_exponential_integrable r k a b d)
    (finiteWeilCanonicalJoint_quadratic_exponential_integrable r k A B D) hfg

theorem finiteWeilCanonicalJointQuadraticTilt_klDiv_ne_top
    (r k : ℕ) (a b d A B D : ℝ) :
    klDiv (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure (EuclideanSpace ℝ (Fin 2)))
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure (EuclideanSpace ℝ (Fin 2))) ≠ ∞ := by
  rw [finiteWeilCanonicalJointQuadraticTilt_klDiv]
  exact ENNReal.ofReal_ne_top

end RHTower
