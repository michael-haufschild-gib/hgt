import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTwoTermObstruction
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerParameterCardinality

/-!
# Exact trace-period obstruction over the Kummer constants

Over the actual square constant field, a polynomial primitive of the
long Frobenius difference exists precisely when the short relative
period divides the long one. No degree bound on the primitive is needed.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)

/-- The two-term Frobenius equation over the specified Kummer constants
has a polynomial solution exactly for divisible relative periods. -/
theorem kummerConstantField_polynomial_trace_iff :
    (∃ P : (SquareConstantField p (kummerSquareIndex d n))[X],
      P ^ (p ^ (d + 1)) ^ (r + 1) - P = X ^ (p ^ (d + 1)) ^ (n + 1) - X) ↔
        r + 1 ∣ n + 1 := by
  have he : (d + 1) * (r + 1) - 1 + 1 = (d + 1) * (r + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos d) (Nat.succ_pos r))
  have h := exists_polynomial_frobenius_difference_iff
    (K := SquareConstantField p (kummerSquareIndex d n)) p
    ((d + 1) * (r + 1) - 1) ((d + 1) * (n + 1))
  simpa only [he, pow_mul, Nat.mul_dvd_mul_iff_left (Nat.succ_pos d)] using h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
