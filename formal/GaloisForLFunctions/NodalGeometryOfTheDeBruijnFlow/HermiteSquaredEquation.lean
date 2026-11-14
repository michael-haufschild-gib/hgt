import GaloisForLFunctions.KodairaParshinAbc.Periods.SymmetricSquare
import GaloisForLFunctions.RHTower.HermiteOscillatorEigen

/-!
# A third-order equation for squared Hermite modes

The symmetric-square construction for Picard--Fuchs equations applies to the
integral Hermite equation as well. It gives an exact differential equation
for every squared oscillator polynomial, with no asymptotic approximation.
-/

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

open Polynomial KodairaParshinAbc.Periods

/-- All squared probabilists' Hermite polynomials satisfy one uniform third-order equation. -/
theorem hermite_squared_ode (n : ℕ) :
    (hermite n ^ 2).derivative.derivative.derivative -
      3 * X * (hermite n ^ 2).derivative.derivative +
      (2 * X ^ 2 + 4 * (n : ℤ[X]) - 1) * (hermite n ^ 2).derivative -
      4 * (n : ℤ[X]) * X * hermite n ^ 2 = 0 := by
  have h : secondOrder 1 (-X) (n : ℤ[X]) (hermite n) = 0 := by
    rw [secondOrder, one_mul, _root_.RHTower.hermite_oscillator_ode]
    ring
  have hs := symmetricSquare_square 1 (-X) (n : ℤ[X]) (hermite n)
  rw [h, derivative_zero, mul_zero, mul_zero, add_zero] at hs
  simp only [symmetricSquare, one_pow, one_mul, mul_one, derivative_neg,
    derivative_X, derivative_one, derivative_natCast, zero_mul, mul_zero] at hs
  linear_combination hs

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

#print axioms GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.hermite_squared_ode
