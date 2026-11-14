import GaloisForLFunctions.HTGeometry.Arithmetic.UnramifiedQuadraticNorm
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

/-!
# Explicit paired tests at primes congruent to three or five modulo eight

The quadratic character of two makes `a² - 2b²` an unramified norm at
these primes. One square-denominator condition tests both coordinates,
including arbitrary common divisibility precision.
-/

namespace GaloisForLFunctions.HTGeometry.Arithmetic

variable {p : ℕ} [Fact p.Prime]

private theorem two_nonsquare_residue (hp : p % 8 = 3 ∨ p % 8 = 5) :
    IsPadicUnit p (2 : ℚ) ∧ ¬ IsSquare (ratRes p (2 : ℚ)) := by
  have hns : ¬ IsSquare (2 : ZMod p) := by
    rw [FiniteField.isSquare_two_iff, ZMod.card]
    omega
  have hne : (2 : ZMod p) ≠ 0 := fun h => hns ⟨0, by simpa using h⟩
  refine ⟨isPadicUnit_natCast (n := 2) hne, ?_⟩
  change ¬ IsSquare (ratRes p ((2 : ℕ) : ℚ))
  rw [ratRes_natCast]
  exact hns

/-- A fixed quadratic polynomial tests two local integrality conditions
at every prime congruent to three or five modulo eight. -/
theorem squareDenominator_two_norm_iff (hp : p % 8 = 3 ∨ p % 8 = 5) (a b : ℚ) :
    SquareDenominator ((p : ℚ) * (a ^ 2 - 2 * b ^ 2) ^ 2) ↔
      0 ≤ padicValRat p a ∧ 0 ≤ padicValRat p b := by
  obtain ⟨hunit, hns⟩ := two_nonsquare_residue hp
  exact squareDenominator_quadraticNorm_iff hunit hns a b

/-- The same polynomial encodes an arbitrary shared precision. -/
theorem squareDenominator_two_norm_precision_iff
    (hp : p % 8 = 3 ∨ p % 8 = 5) (a b : ℚ) (k : ℕ) :
    SquareDenominator ((p : ℚ) * ((a ^ 2 - 2 * b ^ 2) / (p : ℚ) ^ (2 * k)) ^ 2) ↔
      (a = 0 ∨ (k : ℤ) ≤ padicValRat p a) ∧
        (b = 0 ∨ (k : ℤ) ≤ padicValRat p b) := by
  obtain ⟨hunit, hns⟩ := two_nonsquare_residue hp
  exact squareDenominator_quadraticNorm_precision_iff hunit hns a b k

#print axioms squareDenominator_two_norm_iff
#print axioms squareDenominator_two_norm_precision_iff

end GaloisForLFunctions.HTGeometry.Arithmetic
