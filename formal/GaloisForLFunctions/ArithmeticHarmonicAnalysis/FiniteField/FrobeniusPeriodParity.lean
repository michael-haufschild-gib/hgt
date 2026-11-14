import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Ring.Parity

/-!
# Parity of doubled Frobenius periods

Doubling one period doubles its gcd with another precisely when the
second period, divided by their original gcd, is even. This distinguishes
trivial and nontrivial restrictions of a finite-field involution.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- The gcd with two records parity. -/
theorem gcd_two_left_eq (k : ℕ) : Nat.gcd 2 k = if Even k then 2 else 1 := by
  by_cases hk : Even k
  · rw [if_pos hk]
    exact Nat.gcd_eq_left hk.two_dvd
  · rw [if_neg hk, Nat.gcd_rec]
    have hmod : k % 2 = 1 := by
      have hn : k % 2 ≠ 0 := fun h => hk (Nat.even_iff.mpr h)
      have hlt := Nat.mod_lt k (by omega : 0 < 2)
      omega
    rw [hmod, Nat.gcd_one_left]

/-- A doubled period contributes a factor two exactly when the reduced second period is even. -/
theorem gcd_double_left (m k : ℕ) (hm : 0 < m) :
    Nat.gcd (2 * m) k =
      if Even (k / Nat.gcd m k) then 2 * Nat.gcd m k else Nat.gcd m k := by
  have hg := Nat.gcd_pos_of_pos_left k hm
  have hc := Nat.coprime_div_gcd_div_gcd hg
  have hm' : 2 * m = Nat.gcd m k * ((m / Nat.gcd m k) * 2) := by
    rw [← mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_left m k), mul_comm]
  have hk' : k = Nat.gcd m k * (k / Nat.gcd m k) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right m k)).symm
  calc
    Nat.gcd (2 * m) k =
        Nat.gcd (Nat.gcd m k * ((m / Nat.gcd m k) * 2))
          (Nat.gcd m k * (k / Nat.gcd m k)) := congrArg₂ Nat.gcd hm' hk'
    _ = Nat.gcd m k * Nat.gcd ((m / Nat.gcd m k) * 2) (k / Nat.gcd m k) :=
      Nat.gcd_mul_left _ _ _
    _ = Nat.gcd m k * Nat.gcd 2 (k / Nat.gcd m k) := by
      rw [hc.gcd_mul_left_cancel]
    _ = _ := by
      rw [gcd_two_left_eq]
      split_ifs <;> simp only [mul_one, mul_comm]

/-- The original gcd is unchanged exactly when the reduced second period is odd. -/
theorem gcd_double_left_eq_iff (m k : ℕ) (hm : 0 < m) :
    Nat.gcd (2 * m) k = Nat.gcd m k ↔ ¬Even (k / Nat.gcd m k) := by
  rw [gcd_double_left m k hm]
  have hg := Nat.gcd_pos_of_pos_left k hm
  split_ifs with h
  · constructor
    · intro he
      omega
    · intro hn
      exact (hn h).elim
  · exact ⟨fun _ => h, fun _ => rfl⟩

/-- When the reduced second period is even, coprimality forces the first to be odd. -/
theorem odd_div_gcd_of_even_div_gcd (m k : ℕ) (hm : 0 < m)
    (hk : Even (k / Nat.gcd m k)) : Odd (m / Nat.gcd m k) := by
  apply Nat.not_even_iff_odd.mp
  intro he
  have hc := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left k hm)
  have hd := Nat.dvd_gcd he.two_dvd hk.two_dvd
  rw [hc] at hd
  have := Nat.le_of_dvd (by omega : 0 < 1) hd
  omega

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
