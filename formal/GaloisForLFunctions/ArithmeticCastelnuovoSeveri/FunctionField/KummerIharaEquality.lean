import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRegularDifferentialDimension
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerParameterCardinality
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.KummerMaximalGenus

/-!
# Which Kummer members attain the Ihara genus bound

The actual differential genus attains `Q(Q-1)/2` precisely when the
covering prime power equals the branch prime power and the geometric
branch length is odd. The statement holds for every nonzero coefficient.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis

/-- Equality in the maximal-curve genus bound classifies the covering index and branch parity. -/
theorem primePowerKummer_genus_ihara_equality_iff
    (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (c : (SquareConstantField p (kummerSquareIndex d n))ˣ) :
    2 * Module.finrank (SquareConstantField p (kummerSquareIndex d n))
      (globalRegularDifferentials (SquareConstantField p (kummerSquareIndex d n))
        (SquareKummerField p (kummerSquareIndex d n) c (p ^ (d + 1) - 2)
          (kummerExponent (p ^ (d + 1)) r))) =
        p ^ (kummerSquareIndex d n + 1) * (p ^ (kummerSquareIndex d n + 1) - 1) ↔
      n = 0 ∧ Odd r := by
  rw [squareKummer_regularDifferential_finrank_twice, kummerSquareIndex_succ, pow_mul]
  exact kummer_genus_ihara_equality_iff (p ^ (d + 1)) n r
    (Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
