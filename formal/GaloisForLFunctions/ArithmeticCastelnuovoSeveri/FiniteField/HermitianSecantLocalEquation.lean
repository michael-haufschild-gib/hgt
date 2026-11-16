import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.HermitianTangentFactor
import Mathlib.Tactic.LinearCombination

/-!
# Hermitian coordinate differences

The difference of two Hermitian equations factors linearly in the first
coordinate difference, with a higher Frobenius term. At a point with
nonzero first coordinate this identifies the two local coordinate orders.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (E : Type*) [Field E] [CharP E p]
local notation "Q" => p ^ (s + 1)

/-- Subtracting two Hermitian equations gives the exact secant identity. -/
theorem hermitianPoint_secant_equation (P U : HermitianAffinePoint p s E) :
    (U.val.2 - P.val.2) ^ Q + (U.val.2 - P.val.2) =
      U.val.1 ^ Q * (U.val.1 - P.val.1) + P.val.1 * (U.val.1 - P.val.1) ^ Q := by
  have hP := P.property
  have hU := U.property
  rw [pow_succ P.val.1 Q] at hP
  rw [pow_succ U.val.1 Q] at hU
  rw [sub_pow_char_pow, sub_pow_char_pow]
  linear_combination hU - hP

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
