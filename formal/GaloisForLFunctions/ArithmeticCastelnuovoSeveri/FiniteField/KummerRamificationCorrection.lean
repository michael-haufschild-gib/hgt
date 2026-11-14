import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerParameterCardinality
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.KummerExponentGCD

/-!
# The ramification gcd equals the point-count correction

The trace intersection and signed-family correction add to the gcd of the
Kummer degree and the branch multiplicity. The identity follows from the
parity of the reduced exponent and holds for every constructed prime-power
family.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- The trace intersection is governed by the parity of the reduced auxiliary period. -/
theorem kummerTraceIntersectionNumber_parity (p s k : ℕ) :
    kummerTraceIntersectionNumber p s k =
      if Even (k / Nat.gcd (s + 1) k) then p ^ Nat.gcd (s + 1) k
      else if p = 2 then 0 else 1 := by
  unfold kummerTraceIntersectionNumber
  rw [gcd_double_left_eq_iff (s + 1) k (Nat.succ_pos s)]
  by_cases he : Even (k / Nat.gcd (s + 1) k) <;> simp only [he, not_true_eq_false,
    not_false_eq_true, if_true, if_false]

/-- Expressing the base size as a prime power cancels the common field-degree factor. -/
theorem kummerTraceIntersectionNumber_primePower (p d n r : ℕ) :
    kummerTraceIntersectionNumber p (kummerSquareIndex d n) ((d + 1) * (r + 1)) =
      if Even ((r + 1) / Nat.gcd (n + 1) (r + 1)) then
        (p ^ (d + 1)) ^ Nat.gcd (n + 1) (r + 1)
      else if p = 2 then 0 else 1 := by
  rw [kummerTraceIntersectionNumber_parity, kummerSquareIndex_succ,
    Nat.gcd_mul_left, Nat.mul_div_mul_left _ _ (Nat.succ_pos d), pow_mul]

variable (p : ℕ) [Fact p.Prime]

/-- The excluded trace count plus the signed correction is exactly the branch-multiplicity gcd. -/
theorem kummer_ramification_correction (d n r : ℕ) :
    Nat.gcd ((p ^ (d + 1)) ^ (n + 1) + 1) (kummerExponent (p ^ (d + 1)) (r + 1)) =
      kummerTraceIntersectionNumber p (kummerSquareIndex d n) ((d + 1) * (r + 1)) +
        (if p = 2 ∨ Even (r + 1) then 1 else 0) := by
  rw [kummerExponent_gcd, kummerTraceIntersectionNumber_primePower]
  by_cases hr : Even ((r + 1) / Nat.gcd (n + 1) (r + 1))
  · rw [if_pos hr, if_pos hr]
    have he : Even (r + 1) := by
      have hm := hr.mul_left (Nat.gcd (n + 1) (r + 1))
      rwa [Nat.mul_div_cancel' (Nat.gcd_dvd_right (n + 1) (r + 1))] at hm
    rw [if_pos (Or.inr he)]
  · rw [if_neg hr, if_neg hr]
    by_cases hp : p = 2
    · have hq : ¬Odd (p ^ (d + 1)) := by
        have he : Even (p ^ (d + 1)) :=
          Nat.even_pow.mpr ⟨(Fact.out : p.Prime).even_iff.mpr hp, Nat.succ_ne_zero d⟩
        exact fun ho => (Nat.not_even_iff_odd.mpr ho) he
      rw [if_neg (fun h => hq h.1), if_pos hp, if_pos (Or.inl hp)]
    · have hq : Odd (p ^ (d + 1)) := ((Fact.out : p.Prime).odd_of_ne_two hp).pow
      simp only [hp, hq, true_and, false_or, if_false]
      split_ifs <;> rfl

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
