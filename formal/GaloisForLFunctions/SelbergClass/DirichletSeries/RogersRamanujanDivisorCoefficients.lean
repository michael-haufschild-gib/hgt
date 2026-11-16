import GaloisForLFunctions.SelbergClass.DirichletSeries.RealCharacterDivisorPositivity
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Quadratic-irrational divisor coefficients

The divisor expression for logarithmic Rogers–Ramanujan coefficients has
one strictly positive rational multiple of `√5`; its other terms are rational.
This file treats that arithmetic expression. Identification with an analytic
continued fraction is a separate statement.
-/

noncomputable section
namespace GaloisForLFunctions.SelbergClass

/-- The quadratic character modulo five, with rational values. -/
def quadraticCharacterFive : DirichletCharacter ℚ 5 := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact (quadraticChar (ZMod 5)).ringHomComp (Int.castRingHom ℚ)

/-- Rational part of the logarithmic divisor expression. -/
def rogersRamanujanDivisorRationalPart (N : ℕ) : ℚ :=
  -(1 / 2) * (∑ d ∈ N.divisors, 1 / (d : ℚ)) -
    (if 5 ∣ N then (1 / 2) * ∑ d ∈ (N / 5).divisors,
      quadraticCharacterFive ((N / (5 * d) : ℕ) : ZMod 5) / (d : ℚ) else 0) +
    (if 25 ∣ N then (1 / 2) * ∑ d ∈ (N / 25).divisors, 1 / (d : ℚ) else 0)

/-- Explicit arithmetic expression for a positive-degree logarithmic coefficient. -/
def rogersRamanujanDivisorCoefficient (N : ℕ) : ℝ :=
  Real.sqrt 5 / 2 *
    ((∑ d ∈ N.divisors, quadraticCharacterFive (d : ZMod 5) / (d : ℚ) : ℚ) : ℝ) +
    rogersRamanujanDivisorRationalPart N

/-- No positive-degree divisor coefficient is rational. -/
theorem rogersRamanujanDivisorCoefficient_irrational (n : ℕ) :
    Irrational (rogersRamanujanDivisorCoefficient (n + 1)) :=
  irrational_sqrt_five_character_divisor_coefficient quadraticCharacterFive n
    (rogersRamanujanDivisorRationalPart (n + 1))

/-- In particular, the arithmetic expression has no positive-degree zero. -/
theorem rogersRamanujanDivisorCoefficient_ne_zero (n : ℕ) :
    rogersRamanujanDivisorCoefficient (n + 1) ≠ 0 :=
  (rogersRamanujanDivisorCoefficient_irrational n).ne_zero

#print axioms rogersRamanujanDivisorCoefficient_irrational
#print axioms rogersRamanujanDivisorCoefficient_ne_zero
end GaloisForLFunctions.SelbergClass
