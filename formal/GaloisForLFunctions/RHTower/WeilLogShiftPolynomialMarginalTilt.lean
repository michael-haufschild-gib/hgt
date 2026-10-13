import GaloisForLFunctions.RHTower.WeilLogShiftPolynomialGraphRecovery
import GaloisForLFunctions.HTGeometry.TiltedPushforward

/-! Every finite joint quadratic tilt is the graph image of an explicit scalar polynomial tilt. -/

open MeasureTheory GaloisForLFunctions.HTGeometry
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

noncomputable def finiteWeilCanonicalGraphTiltPolynomial (r k : ℕ) (a b d : ℝ) : Polynomial ℝ :=
  Polynomial.C a * Polynomial.X ^ 2 +
    Polynomial.C (2 * b) * Polynomial.X * finiteWeilCanonicalGraphPolynomial r k +
      Polynomial.C d * (finiteWeilCanonicalGraphPolynomial r k) ^ 2

theorem finiteWeilCanonicalGraphTiltPolynomial_eval (r k : ℕ) (a b d x : ℝ) :
    (finiteWeilCanonicalGraphTiltPolynomial r k a b d).eval x =
      finiteWeilJointQuadratic a b d (finiteWeilCanonicalPolynomialGraph r k x) := by
  simp [finiteWeilCanonicalGraphTiltPolynomial, finiteWeilJointQuadratic,
    finiteWeilCanonicalPolynomialGraph]

theorem finiteWeilCanonicalJointQuadraticTilt_first_marginal_polynomial_tilt
    (r k : ℕ) (a b d : ℝ) :
    Measure.map (fun z : E => z 0) (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) =
      (Measure.map (fun z : E => z 0) (finiteWeilCanonicalJointProbabilityLaw r k : Measure E)).tilted
        (fun x => (finiteWeilCanonicalGraphTiltPolynomial r k a b d).eval x) := by
  have hpotential :
      finiteWeilJointQuadratic a b d =ᵐ[(finiteWeilCanonicalJointProbabilityLaw r k : Measure E)]
        ((fun x => (finiteWeilCanonicalGraphTiltPolynomial r k a b d).eval x) ∘ (fun z : E => z 0)) := by
    filter_upwards [finiteWeilCanonicalPolynomialGraph_base_ae r k] with z hz
    simp only [Function.comp_apply, finiteWeilCanonicalGraphTiltPolynomial_eval, hz]
  change Measure.map (fun z : E => z 0)
    ((finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted (finiteWeilJointQuadratic a b d)) = _
  rw [tilted_congr hpotential]
  exact map_tilted_comp _ (fun z : E => z 0) (by fun_prop)
    (fun x => (finiteWeilCanonicalGraphTiltPolynomial r k a b d).eval x) (by fun_prop)

theorem finiteWeilCanonicalJointQuadraticTilt_eq_polynomial_graph_scalar_tilt
    (r k : ℕ) (a b d : ℝ) :
    (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) =
      Measure.map (finiteWeilCanonicalPolynomialGraph r k)
        ((Measure.map (fun z : E => z 0)
          (finiteWeilCanonicalJointProbabilityLaw r k : Measure E)).tilted
            (fun x => (finiteWeilCanonicalGraphTiltPolynomial r k a b d).eval x)) := by
  rw [← finiteWeilCanonicalJointQuadraticTilt_first_marginal_polynomial_tilt]
  exact (finiteWeilCanonicalPolynomialGraph_reconstruct r k a b d).symm

end RHTower
