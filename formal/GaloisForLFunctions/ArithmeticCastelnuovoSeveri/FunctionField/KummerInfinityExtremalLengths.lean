import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityConductor
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.KummerSmallDivisors
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerParameterCardinality

/-!
# Short geometric lengths with an extremal infinity gap

Within one covering exponent, the extremal infinity-gap condition
occurs only at lengths zero and one, or length two when the covering
exponent is odd. This combines the actual regular differential genus
and exact pole semigroup with the ramification gcd classification.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis

/-- The extremal infinity-gap condition has exactly three possibilities within one covering exponent. -/
theorem primePowerKummerInfinity_extremal_lengths
    (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (c : (SquareConstantField p (kummerSquareIndex d n))ˣ) (hr : r ≤ n + 1) :
    let K := SquareConstantField p (kummerSquareIndex d n)
    let L := SquareKummerField p (kummerSquareIndex d n) c (p ^ (d + 1) - 2)
      (kummerExponent (p ^ (d + 1)) r)
    let g := Module.finrank K (globalRegularDifferentials K L)
    (g = 0 ∨ ¬ ∃ x : L, IsIntegral K[X] x ∧
      squareKummerInfinityValuation p (kummerSquareIndex d n) c d r x =
        WithZero.exp ((2 * g - 1 : ℕ) : ℤ)) ↔
      r = 0 ∨ r = 1 ∨ r = 2 ∧ Odd (n + 1) := by
  dsimp only
  rw [squareKummerInfinity_last_gap_criterion, kummerSquareIndex_succ, pow_mul]
  exact kummerExponent_extremal_residue_iff (p ^ (d + 1)) n r
    (Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt) hr

/-- For every branch length, the extremal infinity-gap condition depends on exactly three residue classes modulo twice the covering exponent. -/
theorem primePowerKummerInfinity_extremal_periods
    (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (c : (SquareConstantField p (kummerSquareIndex d n))ˣ) :
    let K := SquareConstantField p (kummerSquareIndex d n)
    let L := SquareKummerField p (kummerSquareIndex d n) c (p ^ (d + 1) - 2)
      (kummerExponent (p ^ (d + 1)) r)
    let g := Module.finrank K (globalRegularDifferentials K L)
    (g = 0 ∨ ¬ ∃ x : L, IsIntegral K[X] x ∧
      squareKummerInfinityValuation p (kummerSquareIndex d n) c d r x =
        WithZero.exp ((2 * g - 1 : ℕ) : ℤ)) ↔
      r % (2 * (n + 1)) = 0 ∨ r % (2 * (n + 1)) = 1 ∨
        r % (2 * (n + 1)) = 2 ∧ Odd (n + 1) := by
  dsimp only
  rw [squareKummerInfinity_last_gap_criterion, kummerSquareIndex_succ, pow_mul]
  exact kummerExponent_extremal_residue_period_iff (p ^ (d + 1)) n r
    (Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
