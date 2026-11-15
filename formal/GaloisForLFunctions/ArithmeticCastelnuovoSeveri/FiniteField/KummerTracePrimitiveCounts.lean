import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusPolynomialPrimitiveCounts
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerParameterCardinality

/-!
# Exact trace-primitive counts over the Kummer constants

For the actual square constant field of order `q^(2(n+1))`, the equation
`P^(q^(r+1))-P=X^(q^(n+1))-X` has exactly `q^(r+1)` polynomial solutions
when `r+1` divides `n+1`, and none otherwise. The positive count is the
size of the short Frobenius fixed field.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)

/-- The literal polynomial solution count over the specified square constant field. -/
theorem kummerConstantField_polynomial_trace_card :
    Nat.card {P : (SquareConstantField p (kummerSquareIndex d n))[X] //
      P ^ (p ^ (d + 1)) ^ (r + 1) - P = X ^ (p ^ (d + 1)) ^ (n + 1) - X} =
        if r + 1 ∣ n + 1 then (p ^ (d + 1)) ^ (r + 1) else 0 := by
  have he : (d + 1) * (r + 1) - 1 + 1 = (d + 1) * (r + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos d) (Nat.succ_pos r))
  have h := frobeniusPolynomialPrimitives_card p
    (SquareConstantField p (kummerSquareIndex d n))
    ((d + 1) * (r + 1) - 1) ((d + 1) * (n + 1))
  simp only [FrobeniusPolynomialPrimitives, he, squareConstantField_finrank,
    kummerSquareIndex_succ, Nat.mul_dvd_mul_iff_left (Nat.succ_pos d)] at h
  by_cases hd : r + 1 ∣ n + 1
  · have hperiod : (d + 1) * (r + 1) ∣ 2 * ((d + 1) * (n + 1)) :=
      (Nat.mul_dvd_mul_left (d + 1) hd).trans (dvd_mul_left _ _)
    simpa only [if_pos hd, Nat.gcd_eq_right hperiod, pow_mul] using h
  · simpa only [if_neg hd, pow_mul] using h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
