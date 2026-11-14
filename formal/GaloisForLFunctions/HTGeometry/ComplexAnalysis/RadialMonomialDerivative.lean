import GaloisForLFunctions.HTGeometry.ComplexAnalysis.RadialMonomialWeights
import GaloisForLFunctions.HTGeometry.ComplexAnalysis.RadialAntiholomorphicDerivative

/-!
# Antiholomorphic defect of a radial coordinate monomial

A complex-coordinate power is holomorphic on the orthogonal complex sum. Multiplying it by
a profile in logarithmic radius produces a `∂̄` norm equal to the coordinate modulus times
`|χ'(log r)|/(2r)`. The monomial degree contributes no differentiated factor.
-/

open MeasureTheory Set Metric

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
  change ‖_root_.HTGeometry.dbarDifferential
    (fun y : BlockSpace ℂ V => y.fst ^ m * (χ (Real.log ‖y‖) : ℂ)) x‖ = _
  simpa only [norm_pow] using
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

/-- The antiholomorphic defect shifts the radial weight by one and contributes a factor `1/2`. -/
theorem weighted_norm_dbarDifferential_radialComplexMonomial
    (m : ℕ) {χ : ℝ → ℝ} {x : BlockSpace ℂ V}
    (hx : x ≠ 0) (hχ : DifferentiableAt ℝ χ (Real.log ‖x‖)) (τ p : ℝ) :
    (‖x‖ ^ (-τ) * ‖_root_.HTGeometry.dbarDifferential (radialComplexMonomial V m χ) x‖) ^ p =
      (1 / 2 : ℝ) ^ p *
        (‖x‖ ^ (-(τ + 1)) * ‖radialComplexMonomial V m (deriv χ) x‖) ^ p := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have he : ‖x‖ ^ (-τ) * (‖radialComplexMonomial V m (deriv χ) x‖ / (2 * ‖x‖)) =
      (1 / 2 : ℝ) * (‖x‖ ^ (-(τ + 1)) * ‖radialComplexMonomial V m (deriv χ) x‖) := by
    rw [show -(τ + 1) = -τ + (-1 : ℝ) by ring, Real.rpow_add hr,
      Real.rpow_neg hr.le 1, Real.rpow_one]
    field_simp
  rw [norm_dbarDifferential_radialComplexMonomial_eq V m hx hχ, he,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity)]

local instance (priority := 50) : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Exact integral relation between the antiholomorphic defect and the differentiated profile. -/
theorem integral_weighted_dbarDifferential_radialComplexMonomial
    (m : ℕ) {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) (τ p : ℝ) :
    (∫ x : BlockSpace ℂ V,
      (‖x‖ ^ (-τ) * ‖_root_.HTGeometry.dbarDifferential (radialComplexMonomial V m χ) x‖) ^ p) =
      (1 / 2 : ℝ) ^ p * ∫ x : BlockSpace ℂ V,
        (‖x‖ ^ (-(τ + 1)) * ‖radialComplexMonomial V m (deriv χ) x‖) ^ p := by
  have hz : ∀ᵐ x : BlockSpace ℂ V, x ≠ 0 := by
    rw [ae_iff]
    simp
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hz] with x hx
  exact weighted_norm_dbarDifferential_radialComplexMonomial V m hx (hχ _) τ p

/-- At the balanced derivative weight, all radial dependence reduces to a fixed one-dimensional
profile integral. -/
theorem integral_critical_weighted_dbarDifferential_radialComplexMonomial
    (m : ℕ) {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) {p : ℝ} (hp : p ≠ 0) :
    (∫ x : BlockSpace ℂ V,
      (‖x‖ ^ (-((m : ℝ) + (Module.finrank ℝ (BlockSpace ℂ V) : ℝ) / p - 1)) *
        ‖_root_.HTGeometry.dbarDifferential (radialComplexMonomial V m χ) x‖) ^ p) =
      (1 / 2 : ℝ) ^ p *
        ((((volume : Measure (BlockSpace ℂ V)).toSphere).real univ *
          complexBlockSphereMellin V ((m : ℝ) * p / 2)) * ∫ t : ℝ, |deriv χ t| ^ p) := by
  rw [integral_weighted_dbarDifferential_radialComplexMonomial V m hχ,
    sub_add_cancel, integral_critical_weighted_radialComplexMonomial V m (deriv χ) hp]

end GaloisForLFunctions.HTGeometry
