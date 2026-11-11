import GaloisForLFunctions.MultiscaleMollifiedZetaField.ThePolynomialJetIntegralsAreExplicit
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShortLevinsonMollifierHasAPositiveScalarMargin

/-!
# The three-profile scalar and the linear Levinson constant

The direct and reflected arithmetic jets combine with their simple poles
and conductor exponential. At the selected length and displacement,
the resulting three-profile expression equals the linear Levinson scalar.
-/

open MeasureTheory Polynomial
open RHTower

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Limiting normalized main value for a polynomial profile. -/
def frozenMainScalarValue (P : ℝ[X]) (u τ : ℝ) : ℝ :=
  -polynomialProfilePairIntegral P P u 0 / (2 * u) +
    Real.exp (2 * τ * u) * polynomialProfilePairIntegral P P (-u) 0 / (2 * u)

/-- Limiting first main jet, including both differentiated poles. -/
def frozenMainScalarFirst (P : ℝ[X]) (u τ : ℝ) : ℝ :=
  -polynomialProfileFirstLimit P P u (-2) 2 0 / (2 * u) +
    polynomialProfilePairIntegral P P u 0 / (2 * u ^ 2) +
    Real.exp (2 * τ * u) *
      (polynomialProfileFirstLimit P P (-u) 2 0 0 / (2 * u) +
        (τ / u - 1 / (2 * u ^ 2)) * polynomialProfilePairIntegral P P (-u) 0)

/-- Limiting second main jet, including every pole and conductor cross term. -/
def frozenMainScalarSecond (P : ℝ[X]) (u τ : ℝ) : ℝ :=
  -polynomialProfileSecondLimit P P u (-2) 2 0 / (2 * u) +
    polynomialProfileFirstLimit P P u (-2) 2 0 / u ^ 2 -
    polynomialProfilePairIntegral P P u 0 / u ^ 3 +
    Real.exp (2 * τ * u) *
      (polynomialProfileSecondLimit P P (-u) 2 0 0 / (2 * u) +
        (2 * τ / u - 1 / u ^ 2) * polynomialProfileFirstLimit P P (-u) 2 0 0 +
        (2 * τ ^ 2 / u - 2 * τ / u ^ 2 + 1 / u ^ 3) *
          polynomialProfilePairIntegral P P (-u) 0)

/-- The scalar selected by the exact three-profile detector identity. -/
def threeProfileDetectorScalar (θ R : ℝ) : ℝ :=
  (1 - θ) * frozenMainScalarValue X (R * θ) (1 / θ) +
    (θ ^ 2 - θ) * frozenMainScalarValue (complementPolynomial X) (R * θ) (1 / θ) +
    θ * frozenMainScalarValue (X + complementPolynomial X) (R * θ) (1 / θ) -
    θ / 2 * ((2 - θ) * frozenMainScalarFirst X (R * θ) (1 / θ) -
      θ * frozenMainScalarFirst (complementPolynomial X) (R * θ) (1 / θ) +
      θ * frozenMainScalarFirst (X + complementPolynomial X) (R * θ) (1 / θ)) +
    θ ^ 2 / 4 * frozenMainScalarSecond X (R * θ) (1 / θ)

/-- Exact identification of the selected arithmetic-pole-conductor scalar. -/
theorem threeProfileDetectorScalar_selected :
    threeProfileDetectorScalar (13 / 50) (13 / 10) =
      levinsonLinearOptimizationConstantAt (13 / 50) := by
  rw [levinsonShortScalar_formula]
  unfold threeProfileDetectorScalar frozenMainScalarValue frozenMainScalarFirst frozenMainScalarSecond
  simp_rw [polynomialProfileFirstLimit_eq_integral, polynomialProfileSecondLimit_eq_integral]
  simp only [polynomialProfilePairIntegral, polynomialDifferentialProfile, complementPolynomial,
    Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_one, Polynomial.derivative_X, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_zero, Polynomial.eval_one,
    Polynomial.eval_X, pow_zero, one_mul]
  ring_nf
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_neg, intervalIntegral.integral_pow, intervalIntegral.integral_const]
  norm_num
  ring

/-- The exact three-profile scalar has the margin needed by Levinson's gate. -/
theorem threeProfileDetectorScalar_selected_lt :
    threeProfileDetectorScalar (13 / 50) (13 / 10) < 18 / 5 := by
  rw [threeProfileDetectorScalar_selected]
  exact levinsonLinearOptimizationConstantAt_thirteen_fiftieths_lt

end GaloisForLFunctions.MultiscaleMollifiedZetaField
