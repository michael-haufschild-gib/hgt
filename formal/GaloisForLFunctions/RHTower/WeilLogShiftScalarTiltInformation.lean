import GaloisForLFunctions.RHTower.WeilLogShiftFirstMarginalInformation
import GaloisForLFunctions.RHTower.WeilLogShiftPolynomialMarginalTilt

/-! # Scalar polynomial formulas for finite Weil pair information -/

namespace RHTower

open MeasureTheory InformationTheory
open GaloisForLFunctions.HTGeometry

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- Full joint KL equals KL between the scalar polynomial tilts. -/
theorem finiteWeilCanonicalJointQuadraticTilt_klDiv_scalar_polynomial_tilt
    (r k : ℕ) (a b d A B D : ℝ) :
    klDiv (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) =
    klDiv
      ((Measure.map (fun z : E => z 0)
        (finiteWeilCanonicalJointProbabilityLaw r k : Measure E)).tilted
        (fun x => (finiteWeilCanonicalGraphTiltPolynomial r k a b d).eval x))
      ((Measure.map (fun z : E => z 0)
        (finiteWeilCanonicalJointProbabilityLaw r k : Measure E)).tilted
        (fun x => (finiteWeilCanonicalGraphTiltPolynomial r k A B D).eval x)) := by
  rw [← finiteWeilCanonicalJointQuadraticTilt_first_marginal_klDiv r k a b d A B D,
    finiteWeilCanonicalJointQuadraticTilt_first_marginal_polynomial_tilt,
    finiteWeilCanonicalJointQuadraticTilt_first_marginal_polynomial_tilt]

/-- Full joint affinity equals affinity between the scalar polynomial tilts. -/
theorem finiteWeilCanonicalJointQuadraticTilt_bhattacharyya_scalar_polynomial_tilt
    (r k : ℕ) (a b d A B D : ℝ) :
    bhattacharyya (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) =
    bhattacharyya
      ((Measure.map (fun z : E => z 0)
        (finiteWeilCanonicalJointProbabilityLaw r k : Measure E)).tilted
        (fun x => (finiteWeilCanonicalGraphTiltPolynomial r k a b d).eval x))
      ((Measure.map (fun z : E => z 0)
        (finiteWeilCanonicalJointProbabilityLaw r k : Measure E)).tilted
        (fun x => (finiteWeilCanonicalGraphTiltPolynomial r k A B D).eval x)) := by
  rw [← finiteWeilCanonicalJointQuadraticTilt_first_marginal_bhattacharyya r k a b d A B D,
    finiteWeilCanonicalJointQuadraticTilt_first_marginal_polynomial_tilt,
    finiteWeilCanonicalJointQuadraticTilt_first_marginal_polynomial_tilt]

end RHTower
