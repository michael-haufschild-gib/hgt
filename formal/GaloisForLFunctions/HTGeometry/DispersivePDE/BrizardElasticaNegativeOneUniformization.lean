import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaHalfUniformization

/-!
# Analytic uniformization of Brizard's `m = -1` family

Appendix A of arXiv:2607.21750 sends the negative Jacobi modulus `m = -1` to the classical
modulus `1/2`, while rescaling `q₀` by `1/(1-m) = 1/2`.  Combining that exact parameter
transport with the square-lattice uniformization of the `m = 1/2` family gives an unconditional
analytic uniformization of every nonzero-scale `m = -1` Brizard curve.  The resulting trace is
one-periodic, satisfies paper equation (72), and lies on the complex base change of the original
negative-modulus curve.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- The paper's distinguished negative modulus `m = -1`. -/
def negativeOneModulus : NegativeModulus := ⟨-1, by norm_num⟩

/-- The compensating scale `q₀/(1-m) = q₀/2`. -/
noncomputable def negativeOneTransportScale (q₀ : ℝˣ) : ℝˣ :=
  q₀ / negativeGapUnit negativeOneModulus

/-- At `m = -1`, Appendix A's transported parameters are exactly the lemniscatic family. -/
theorem transportedNegativeOne_eq_halfParameters (q₀ : ℝˣ) :
    transportedClassicalParameters negativeOneModulus q₀ =
      halfParameters (negativeOneTransportScale q₀) := by
  unfold transportedClassicalParameters halfParameters
  congr 1
  change (extendedToClassical negativeOneModulus : ℝ) = 1 / 2
  rw [extendedToClassical]
  norm_num [negativeOneModulus]

/-- Square-lattice period pair scaled to the original negative-modulus curve. -/
noncomputable def negativeOneUniformizationPeriodPair (q₀ : ℝˣ) : PeriodPair :=
  halfUniformizationPeriodPair (negativeOneTransportScale q₀)

theorem negativeOneUniformizationPeriodPair_g₂ (q₀ : ℝˣ) :
    (negativeOneUniformizationPeriodPair q₀).g₂ =
      (g₂ (negativeParameters negativeOneModulus q₀) : ℂ) := by
  rw [negativeOneUniformizationPeriodPair, halfUniformizationPeriodPair_g₂]
  rw [← transportedNegativeOne_eq_halfParameters]
  exact_mod_cast transported_g₂ negativeOneModulus q₀

theorem negativeOneUniformizationPeriodPair_g₃ (q₀ : ℝˣ) :
    (negativeOneUniformizationPeriodPair q₀).g₃ =
      (g₃ (negativeParameters negativeOneModulus q₀) : ℂ) := by
  rw [negativeOneUniformizationPeriodPair, halfUniformizationPeriodPair_g₃]
  rw [← transportedNegativeOne_eq_halfParameters]
  exact_mod_cast transported_g₃ negativeOneModulus q₀

/-- Exact equality between analytic lattice curve and Brizard's `m = -1` cubic. -/
theorem negativeOneUniformization_curve (q₀ : ℝˣ) :
    analyticWeierstrassCurve (negativeOneUniformizationPeriodPair q₀) =
      (weierstrassCurve (negativeParameters negativeOneModulus q₀)).map
        Complex.ofRealHom := by
  calc
    analyticWeierstrassCurve (negativeOneUniformizationPeriodPair q₀) =
        (weierstrassCurve (halfParameters (negativeOneTransportScale q₀))).map
          Complex.ofRealHom := by
      exact halfUniformization_curve (negativeOneTransportScale q₀)
    _ = (weierstrassCurve
          (transportedClassicalParameters negativeOneModulus q₀)).map
            Complex.ofRealHom := by
      rw [transportedNegativeOne_eq_halfParameters]
    _ = (weierstrassCurve (negativeParameters negativeOneModulus q₀)).map
          Complex.ofRealHom := by
      rw [transported_weierstrassCurve]

theorem negativeOneUniformization_curve_discriminant_ne_zero (q₀ : ℝˣ) :
    (analyticWeierstrassCurve (negativeOneUniformizationPeriodPair q₀)).Δ ≠ 0 := by
  exact halfUniformization_curve_discriminant_ne_zero (negativeOneTransportScale q₀)

/-- Paper equation (72) on the analytically uniformized `m = -1` curve. -/
theorem negativeOneUniformization_trace_equation (q₀ : ℝˣ) (x : ℝ) :
    halfShiftWeierstrassPrime (negativeOneUniformizationPeriodPair q₀) x ^ 2 =
      (negativeOneUniformizationPeriodPair q₀).ω₁ ^ 2 *
        (4 * halfShiftWeierstrass (negativeOneUniformizationPeriodPair q₀) x ^ 3 -
          (g₂ (negativeParameters negativeOneModulus q₀) : ℂ) *
            halfShiftWeierstrass (negativeOneUniformizationPeriodPair q₀) x -
          (g₃ (negativeParameters negativeOneModulus q₀) : ℂ)) := by
  simpa only [negativeOneUniformizationPeriodPair_g₂,
    negativeOneUniformizationPeriodPair_g₃] using
      halfShiftWeierstrass_equation (negativeOneUniformizationPeriodPair q₀) x

theorem negativeOneUniformization_trace_periodic (q₀ : ℝˣ) :
    Function.Periodic
      (halfShiftWeierstrass (negativeOneUniformizationPeriodPair q₀)) 1 :=
  halfShiftWeierstrass_periodic (negativeOneUniformizationPeriodPair q₀)

/-- The pole-free periodic trace gives an affine point on Brizard's `m = -1` curve. -/
theorem negativeOneUniformization_trace_on_brizard_curve (q₀ : ℝˣ) (x : ℝ) :
    ((weierstrassCurve (negativeParameters negativeOneModulus q₀)).map
      Complex.ofRealHom).toAffine.Equation
        (halfShiftWeierstrass (negativeOneUniformizationPeriodPair q₀) x)
        (halfShiftWeierstrassPrime (negativeOneUniformizationPeriodPair q₀) x /
          (2 * (negativeOneUniformizationPeriodPair q₀).ω₁)) := by
  rw [← negativeOneUniformization_curve]
  exact halfShiftWeierstrass_on_curve (negativeOneUniformizationPeriodPair q₀) x

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
