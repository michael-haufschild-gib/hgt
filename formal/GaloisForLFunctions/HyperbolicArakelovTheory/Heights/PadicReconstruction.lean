import GaloisForLFunctions.HyperbolicArakelovTheory.Heights.RationalHeight
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Ring

/-!
# Rational reconstruction from height and one local precision

Clearing a reduced denominator turns p-adic agreement with an integer into
divisibility of an integer of size at most `(1+|n|)H(q)`. If the modulus
exceeds that size, the difference must vanish. No restriction on the
denominator at the chosen prime is needed.
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

#print axioms eq_integer_of_padic_precision

end GaloisForLFunctions.HyperbolicArakelovTheory.CoupledProductObstruction
