import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerUniformizerDifferentials

/-!
# Derivation with respect to a local parameter

The rational differential coordinate gives a derivation on the separable
Kummer field. Dividing by the derivative of a uniformizer normalizes this
derivation to send that uniformizer to one. Frobenius expansions show
that the normalized derivation preserves its valuation ring.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- Differentiation in the original rational coordinate, extended to the Kummer field. -/
def squareKummerCoordinateDerivation :
    Derivation (SquareConstantField p s) (SquareKummerField p s c b R) (SquareKummerField p s c b R) :=
  (squareKummerDifferentialEquiv p s c b R).toLinearMap.compDer
    (KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R))

/-- The coordinate derivation evaluates the Kähler differential coordinate. -/
theorem squareKummerCoordinateDerivation_apply (x : SquareKummerField p s c b R) :
    squareKummerCoordinateDerivation p s c b R x = squareKummerDifferentialEquiv p s c b R
      (KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R) x) := rfl

/-- The extended coordinate derivation differentiates polynomials in the usual way. -/
theorem squareKummerCoordinateDerivation_polynomial (f : (SquareConstantField p s)[X]) :
    squareKummerCoordinateDerivation p s c b R
      (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) f) =
        algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) f.derivative :=
  squareKummerDifferentialEquiv_D_polynomial p s c b R f

/-- Normalize the coordinate derivation by the derivative of a proposed local parameter. -/
def squareKummerUniformizerDerivation (π : SquareKummerField p s c b R) :
    Derivation (SquareConstantField p s) (SquareKummerField p s c b R) (SquareKummerField p s c b R) :=
  (squareKummerCoordinateDerivation p s c b R π)⁻¹ • squareKummerCoordinateDerivation p s c b R

/-- The normalized derivative is the derivative ratio. -/
theorem squareKummerUniformizerDerivation_apply (π x : SquareKummerField p s c b R) :
    squareKummerUniformizerDerivation p s c b R π x =
      (squareKummerCoordinateDerivation p s c b R π)⁻¹ * squareKummerCoordinateDerivation p s c b R x := rfl

variable (v : Valuation (SquareKummerField p s c b R) (WithZero (Multiplicative ℤ)))
    (π : SquareKummerField p s c b R) (hπ : v π = WithZero.exp (-1 : ℤ))

include v hπ

/-- The original coordinate derivative of a uniformizer is nonzero. -/
theorem squareKummerCoordinateDerivation_uniformizer_ne_zero :
    squareKummerCoordinateDerivation p s c b R π ≠ 0 := by
  rw [squareKummerCoordinateDerivation_apply]
  intro h
  apply squareKummer_uniformizer_differential_ne_zero p s c b R v π hπ
  apply (squareKummerDifferentialEquiv p s c b R).injective
  simpa only [map_zero] using h

/-- Differentiation with respect to a uniformizer sends that uniformizer to one. -/
theorem squareKummerUniformizerDerivation_self :
    squareKummerUniformizerDerivation p s c b R π π = 1 := by
  rw [squareKummerUniformizerDerivation_apply,
    inv_mul_cancel₀ (squareKummerCoordinateDerivation_uniformizer_ne_zero p s c b R v π hπ)]

/-- The uniformizer derivation preserves the actual valuation ring. -/
theorem squareKummerUniformizerDerivation_integral
    (x : SquareKummerField p s c b R) (hx : v x ≤ 1) :
    v (squareKummerUniformizerDerivation p s c b R π x) ≤ 1 := by
  obtain ⟨a, ha, hD⟩ := squareKummer_integral_differential_uniformizer_multiple p s c b R v π hπ x hx
  have he : squareKummerCoordinateDerivation p s c b R x =
      a * squareKummerCoordinateDerivation p s c b R π := by
    simp only [squareKummerCoordinateDerivation_apply, hD, map_smul, smul_eq_mul]
  rw [squareKummerUniformizerDerivation_apply, he, mul_left_comm,
    inv_mul_cancel₀ (squareKummerCoordinateDerivation_uniformizer_ne_zero p s c b R v π hπ), mul_one]
  exact ha

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
