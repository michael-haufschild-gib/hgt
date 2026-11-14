import GaloisForLFunctions.HTGeometry.ComplexAnalysis.RadialMonomialWeights
import GaloisForLFunctions.HTGeometry.ComplexAnalysis.RadialAntiholomorphicDerivative

/-!
# Antiholomorphic defect of a radial coordinate monomial

A complex-coordinate power is holomorphic on the orthogonal complex sum. Multiplying it by
a profile in logarithmic radius produces a `∂̄` norm equal to the coordinate modulus times
`|χ'(log r)|/(2r)`. The monomial degree contributes no differentiated factor.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The coordinate-power amplitude is holomorphic. -/
theorem differentiable_complexBlock_coordinate_pow (m : ℕ) :
    Differentiable ℂ (fun x : BlockSpace ℂ V => x.fst ^ m) := by
  have hf : Differentiable ℂ (fun x : BlockSpace ℂ V => x.fst) :=
    ((ContinuousLinearMap.fst ℂ ℂ V).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ V).toContinuousLinearMap).differentiable
  exact hf.pow m

/-- Exact antiholomorphic norm of a radial monomial away from the origin. -/
theorem norm_dbarDifferential_radialComplexMonomial
    (m : ℕ) {χ : ℝ → ℝ} {χ' : ℝ} {x : BlockSpace ℂ V}
    (hx : x ≠ 0) (hχ : HasDerivAt χ χ' (Real.log ‖x‖)) :
    ‖_root_.HTGeometry.dbarDifferential (radialComplexMonomial V m χ) x‖ =
      ‖x.fst‖ ^ m * (|χ'| / (2 * ‖x‖)) := by
  simpa only [radialComplexMonomial, norm_pow] using
    _root_.HTGeometry.norm_dbarDifferential_holomorphic_logRadius hx
      (differentiable_complexBlock_coordinate_pow V m x) hχ

/-- Differentiating the radial profile and dividing by twice the radius gives the full defect. -/
theorem norm_dbarDifferential_radialComplexMonomial_eq
    (m : ℕ) {χ : ℝ → ℝ} {x : BlockSpace ℂ V}
    (hx : x ≠ 0) (hχ : DifferentiableAt ℝ χ (Real.log ‖x‖)) :
    ‖_root_.HTGeometry.dbarDifferential (radialComplexMonomial V m χ) x‖ =
      ‖radialComplexMonomial V m (deriv χ) x‖ / (2 * ‖x‖) := by
  rw [norm_dbarDifferential_radialComplexMonomial V m hx hχ.hasDerivAt,
    norm_radialComplexMonomial, mul_div_assoc]

end GaloisForLFunctions.HTGeometry
