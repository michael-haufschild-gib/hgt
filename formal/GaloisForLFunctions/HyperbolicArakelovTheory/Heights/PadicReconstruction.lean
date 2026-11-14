import GaloisForLFunctions.HyperbolicArakelovTheory.Heights.RationalHeight
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Ring

/-!
# Rational reconstruction from height and local precision

Clearing a reduced denominator turns p-adic agreement with an integer into
divisibility of an integer of size at most `(1+|n|)H(q)`. If the modulus
exceeds that size, the difference must vanish. Two rational numbers have
denominator-cleared difference at most twice the product of their heights.
No restriction on either denominator at the chosen prime is needed.
-/

namespace GaloisForLFunctions.HyperbolicArakelovTheory.CoupledProductObstruction

/-- Size of the numerator after clearing a rational-integer difference. -/
theorem integer_difference_numerator_bound (q : ℚ) (n : ℤ) :
    (q.num - n * (q.den : ℤ)).natAbs ≤ (n.natAbs + 1) * weilHeight q := by
  calc
    (q.num - n * (q.den : ℤ)).natAbs ≤ q.num.natAbs + (n * (q.den : ℤ)).natAbs :=
      Int.natAbs_sub_le _ _
    _ = q.num.natAbs + n.natAbs * q.den := by rw [Int.natAbs_mul, Int.natAbs_natCast]
    _ ≤ weilHeight q + n.natAbs * weilHeight q :=
      Nat.add_le_add (num_natAbs_le_weilHeight q)
        (Nat.mul_le_mul_left _ (den_le_weilHeight q))
    _ = (n.natAbs + 1) * weilHeight q := by ring

/-- Height-bounded rational reconstruction from agreement with an integer
modulo a prime power. -/
theorem eq_integer_of_padic_precision {p : ℕ} [Fact p.Prime]
    (q : ℚ) (n : ℤ) (k : ℕ) (hprecision : (k : ℤ) ≤ padicValRat p (q - n))
    (hheight : (n.natAbs + 1) * weilHeight q < p ^ k) : q = n := by
  by_contra hne
  have hdiff : q - (n : ℚ) ≠ 0 := sub_ne_zero.mpr hne
  have hden : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hcross : ((q.num - n * (q.den : ℤ) : ℤ) : ℚ) = (q - n) * q.den := by
    push_cast
    rw [sub_mul, Rat.mul_den_eq_num]
  have hcross_ne : q.num - n * (q.den : ℤ) ≠ 0 := by
    intro hz
    have h := mul_ne_zero hdiff hden
    apply h
    rw [← hcross, hz, Int.cast_zero]
  have hval : (k : ℤ) ≤ padicValRat p ((q.num - n * (q.den : ℤ) : ℤ) : ℚ) := by
    rw [hcross, padicValRat.mul hdiff hden]
    exact hprecision.trans (le_add_of_nonneg_right (zero_le_padicValRat_of_nat q.den))
  have hval' : k ≤ padicValNat p (q.num - n * (q.den : ℤ)).natAbs := by
    rw [padicValRat.of_int] at hval
    change (k : ℤ) ≤ (padicValNat p (q.num - n * (q.den : ℤ)).natAbs : ℤ) at hval
    exact_mod_cast hval
  have hdiv : p ^ k ∣ (q.num - n * (q.den : ℤ)).natAbs :=
    (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hcross_ne)).mpr hval'
  have hlarge := Nat.le_of_dvd (Int.natAbs_pos.mpr hcross_ne) hdiv
  exact (not_lt_of_ge (hlarge.trans (integer_difference_numerator_bound q n))) hheight

/-- The cross difference of reduced rational coordinates is bounded by
twice the product of their multiplicative heights. -/
theorem rational_cross_difference_bound (q r : ℚ) :
    (q.num * (r.den : ℤ) - r.num * (q.den : ℤ)).natAbs ≤
      2 * weilHeight q * weilHeight r := by
  calc
    (q.num * (r.den : ℤ) - r.num * (q.den : ℤ)).natAbs ≤
        (q.num * (r.den : ℤ)).natAbs + (r.num * (q.den : ℤ)).natAbs :=
      Int.natAbs_sub_le _ _
    _ = q.num.natAbs * r.den + r.num.natAbs * q.den := by
      rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    _ ≤ weilHeight q * weilHeight r + weilHeight r * weilHeight q :=
      Nat.add_le_add
        (Nat.mul_le_mul (num_natAbs_le_weilHeight q) (den_le_weilHeight r))
        (Nat.mul_le_mul (num_natAbs_le_weilHeight r) (den_le_weilHeight q))
    _ = 2 * weilHeight q * weilHeight r := by ring

/-- Sufficient local agreement uniquely determines any height-bounded
rational number, including when its denominator contains the chosen prime.
The equality alternative accounts for the total valuation convention at zero. -/
theorem eq_of_padic_precision {p : ℕ} [Fact p.Prime]
    (q r : ℚ) (k : ℕ)
    (hprecision : q = r ∨ (k : ℤ) ≤ padicValRat p (q - r))
    (hheight : 2 * weilHeight q * weilHeight r < p ^ k) : q = r := by
  rcases hprecision with h | hprecision
  · exact h
  by_contra hne
  have hdiff : q - r ≠ 0 := sub_ne_zero.mpr hne
  have hqden : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hrden : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
  have hden := mul_ne_zero hqden hrden
  have hcross : ((q.num * (r.den : ℤ) - r.num * (q.den : ℤ) : ℤ) : ℚ) =
      (q - r) * ((q.den : ℚ) * r.den) := by
    push_cast
    rw [← Rat.mul_den_eq_num q, ← Rat.mul_den_eq_num r]
    ring
  have hcross_ne : q.num * (r.den : ℤ) - r.num * (q.den : ℤ) ≠ 0 := by
    intro hz
    apply mul_ne_zero hdiff hden
    rw [← hcross, hz, Int.cast_zero]
  have hval : (k : ℤ) ≤
      padicValRat p ((q.num * (r.den : ℤ) - r.num * (q.den : ℤ) : ℤ) : ℚ) := by
    rw [hcross, padicValRat.mul hdiff hden, padicValRat.mul hqden hrden]
    exact hprecision.trans (le_add_of_nonneg_right
      (add_nonneg (zero_le_padicValRat_of_nat q.den) (zero_le_padicValRat_of_nat r.den)))
  have hval' : k ≤ padicValNat p (q.num * (r.den : ℤ) - r.num * (q.den : ℤ)).natAbs := by
    rw [padicValRat.of_int] at hval
    exact_mod_cast hval
  have hdiv : p ^ k ∣ (q.num * (r.den : ℤ) - r.num * (q.den : ℤ)).natAbs :=
    (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hcross_ne)).mpr hval'
  have hlarge := Nat.le_of_dvd (Int.natAbs_pos.mpr hcross_ne) hdiv
  exact (not_lt_of_ge (hlarge.trans (rational_cross_difference_bound q r))) hheight

/-- Above the height separation threshold, local congruence and rational
equality are equivalent. -/
theorem padic_precision_iff_eq {p : ℕ} [Fact p.Prime]
    (q r : ℚ) (k : ℕ) (hheight : 2 * weilHeight q * weilHeight r < p ^ k) :
    (q = r ∨ (k : ℤ) ≤ padicValRat p (q - r)) ↔ q = r :=
  ⟨fun h => eq_of_padic_precision q r k h hheight, Or.inl⟩

#print axioms eq_integer_of_padic_precision
#print axioms eq_of_padic_precision

end GaloisForLFunctions.HyperbolicArakelovTheory.CoupledProductObstruction
