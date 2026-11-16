import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.KummerExponentPeriod

/-!
# The exact divisible period of a geometric Kummer exponent

The plus-one covering degree divides a geometric exponent exactly
when its length is a multiple of twice the covering exponent. The
ramification gcd formula forces equality of the two power exponents;
the doubled geometric-sum identity proves the converse.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- The geometric branch exponent is divisible by `q^(n+1)+1` exactly at doubled periods. -/
theorem kummerExponent_cover_dvd_iff (q n r : ℕ) (hq : 2 ≤ q) :
    q ^ (n + 1) + 1 ∣ kummerExponent q r ↔ 2 * (n + 1) ∣ r := by
  constructor
  · intro hd
    have hgcd : Nat.gcd (q ^ (n + 1) + 1) (kummerExponent q r) = q ^ (n + 1) + 1 :=
      Nat.gcd_eq_left hd
    by_cases heven : Even (r / Nat.gcd (n + 1) r)
    · have h := kummerExponent_gcd_eq_pow_add_one q (n + 1) r (Nat.succ_pos n) heven
      rw [hgcd] at h
      have hg : n + 1 = Nat.gcd (n + 1) r :=
        Nat.pow_right_injective hq (Nat.add_right_cancel h)
      have hfac : r = (n + 1) * (r / Nat.gcd (n + 1) r) := by
        exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right (n + 1) r)).symm.trans
          (congrArg (fun a => a * (r / Nat.gcd (n + 1) r)) hg.symm)
      obtain ⟨t, ht⟩ := heven
      refine ⟨t, ?_⟩
      rw [hfac, ht]
      ring
    · have hd2 : q ^ (n + 1) + 1 ∣ 2 := by
        rw [← hgcd]
        exact kummerExponent_gcd_dvd_two q (n + 1) r (Nat.succ_pos n) heven
      have hle := Nat.le_of_dvd (Nat.zero_lt_succ 1) hd2
      have hpow : 1 < q ^ (n + 1) := Nat.one_lt_pow (Nat.succ_ne_zero n) hq
      omega
  · rintro ⟨t, ht⟩
    rw [ht]
    have hfactor : kummerExponent q ((2 * (n + 1)) * t) =
        kummerExponent q (2 * (n + 1)) * kummerExponent (q ^ (2 * (n + 1))) t :=
      geom_sum_mul_length q (2 * (n + 1)) t
    rw [hfactor, kummerExponent_double_length]
    exact ⟨kummerExponent q (n + 1) * kummerExponent (q ^ (2 * (n + 1))) t, mul_assoc _ _ _⟩

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
