import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTracePolynomials
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusPeriodParity
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.GCD

/-!
# The ramification gcd of a geometric exponent

The common divisor of `q^n+1` and the geometric sum of length `r` is
controlled by the parity of `r/gcd(n,r)`. Reduction modulo the common
divisor turns the calculation into a gcd of multiplicative periods.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

open Finset

/-- Grouping a geometric sum into blocks factors its length multiplicatively. -/
theorem geom_sum_mul_length {A : Type*} [CommSemiring A] (x : A) (m n : ℕ) :
    (∑ i ∈ range (m * n), x ^ i) =
      (∑ i ∈ range m, x ^ i) * ∑ j ∈ range n, (x ^ m) ^ j := by
  induction n with
  | zero => simp only [mul_zero, range_zero, sum_empty]
  | succ n ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]
    simp only [pow_add, pow_mul, ← mul_sum]
    ring

/-- Casting the geometric exponent gives the geometric sum in any semiring. -/
theorem cast_kummerExponent {A : Type*} [Semiring A] (q r : ℕ) :
    (kummerExponent q r : A) = ∑ i ∈ range r, (q : A) ^ i := by
  simp only [kummerExponent, Nat.cast_sum, Nat.cast_pow]

/-- An odd base gives a geometric sum with the same parity as its length. -/
theorem kummerExponent_even_iff_of_odd (q r : ℕ) (hq : Odd q) :
    Even (kummerExponent q r) ↔ Even r := by
  have hq' : (q : ZMod 2) = 1 := by
    obtain ⟨t, ht⟩ := hq
    have h2 : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    rw [ht]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      h2, zero_mul, zero_add]
  have hR : (kummerExponent q r : ZMod 2) = (r : ZMod 2) := by
    rw [cast_kummerExponent, hq', one_geom_sum]
  rw [even_iff_two_dvd, even_iff_two_dvd,
    ← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff, hR]

private theorem gcd_kummer_powers (q n r : ℕ) :
    let g := Nat.gcd (q ^ n + 1) (kummerExponent q r)
    ((q : ZMod g) ^ n = -1) ∧ ((q : ZMod g) ^ r = 1) := by
  dsimp only
  let g := Nat.gcd (q ^ n + 1) (kummerExponent q r)
  have hN : ((q ^ n + 1 : ℕ) : ZMod g) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.gcd_dvd_left _ _)
  have hR : (kummerExponent q r : ZMod g) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.gcd_dvd_right _ _)
  constructor
  · simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, add_eq_zero_iff_eq_neg] using hN
  · have he := geom_sum_mul (q : ZMod g) r
    rw [← cast_kummerExponent, hR, zero_mul] at he
    exact sub_eq_zero.mp he.symm

/-- In the odd reduced-period case the common divisor is at most two. -/
theorem kummerExponent_gcd_dvd_two (q n r : ℕ) (hn : 0 < n)
    (hr : ¬Even (r / Nat.gcd n r)) :
    Nat.gcd (q ^ n + 1) (kummerExponent q r) ∣ 2 := by
  let g := Nat.gcd (q ^ n + 1) (kummerExponent q r)
  obtain ⟨hN, hR⟩ := gcd_kummer_powers q n r
  have hN2 : (q : ZMod g) ^ (2 * n) = 1 := by
    rw [mul_comm 2 n, pow_mul, hN]
    ring
  have hh := pow_gcd_eq_one.mpr ⟨hN2, hR⟩
  rw [(gcd_double_left_eq_iff n r hn).mpr hr] at hh
  have hN' : (q : ZMod g) ^ n = 1 := by
    conv_lhs => rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_left n r), pow_mul]
    rw [hh, one_pow]
  apply (ZMod.natCast_eq_zero_iff 2 g).mp
  change (2 : ZMod g) = 0
  linear_combination hN - hN'

/-- In the even reduced-period case the common divisor is the smaller plus-one power. -/
theorem kummerExponent_gcd_eq_pow_add_one (q n r : ℕ) (hn : 0 < n)
    (hr : Even (r / Nat.gcd n r)) :
    Nat.gcd (q ^ n + 1) (kummerExponent q r) = q ^ Nat.gcd n r + 1 := by
  let h := Nat.gcd n r
  have hnodd := odd_div_gcd_of_even_div_gcd n r hn hr
  have hnfac : n = h * (n / h) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left n r)).symm
  have hrfac : r = h * (r / h) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right n r)).symm
  apply Nat.dvd_antisymm
  · let g := Nat.gcd (q ^ n + 1) (kummerExponent q r)
    obtain ⟨hN, hR⟩ := gcd_kummer_powers q n r
    have hN2 : (q : ZMod g) ^ (2 * n) = 1 := by
      rw [mul_comm 2 n, pow_mul, hN]
      ring
    have hh := pow_gcd_eq_one.mpr ⟨hN2, hR⟩
    rw [gcd_double_left n r hn, if_pos hr] at hh
    have hsq : ((q : ZMod g) ^ h) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm h 2]
      exact hh
    have hsmall : (q : ZMod g) ^ h = -1 := by
      obtain ⟨t, ht⟩ := hnodd
      have he : (q : ZMod g) ^ n = (q : ZMod g) ^ h := by
        conv_lhs => rw [hnfac, ht, pow_mul, pow_add, pow_mul, hsq, one_pow, pow_one, one_mul]
      exact he.symm.trans hN
    apply (ZMod.natCast_eq_zero_iff _ g).mp
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    change (q : ZMod g) ^ h + 1 = 0
    rw [hsmall, neg_add_cancel]
  · apply Nat.dvd_gcd
    · apply (ZMod.natCast_eq_zero_iff _ (q ^ h + 1)).mp
      have hh : (q : ZMod (q ^ h + 1)) ^ h = -1 := by
        have he := ZMod.natCast_self (q ^ h + 1)
        simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, add_eq_zero_iff_eq_neg] using he
      simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
      rw [hnfac, pow_mul, hh, hnodd.neg_one_pow, neg_add_cancel]
    · apply (ZMod.natCast_eq_zero_iff _ (q ^ h + 1)).mp
      have hh : (q : ZMod (q ^ h + 1)) ^ h = -1 := by
        have he := ZMod.natCast_self (q ^ h + 1)
        simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, add_eq_zero_iff_eq_neg] using he
      rw [cast_kummerExponent]
      conv_lhs => rw [hrfac, geom_sum_mul_length, hh, neg_one_geom_sum, if_pos hr, mul_zero]

/-- The ramification gcd has an exact three-case formula, including zero geometric length. -/
theorem kummerExponent_gcd (q n r : ℕ) :
    Nat.gcd (q ^ (n + 1) + 1) (kummerExponent q r) =
      if Even (r / Nat.gcd (n + 1) r) then q ^ Nat.gcd (n + 1) r + 1
      else if Odd q ∧ Even r then 2 else 1 := by
  by_cases hr : Even (r / Nat.gcd (n + 1) r)
  · rw [if_pos hr]
    exact kummerExponent_gcd_eq_pow_add_one q (n + 1) r (Nat.succ_pos n) hr
  · rw [if_neg hr]
    have hd := kummerExponent_gcd_dvd_two q (n + 1) r (Nat.succ_pos n) hr
    by_cases hqr : Odd q ∧ Even r
    · rw [if_pos hqr]
      apply Nat.dvd_antisymm hd
      apply Nat.dvd_gcd
      · exact (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hqr.1.pow)).two_dvd
      · exact ((kummerExponent_even_iff_of_odd q r hqr.1).mpr hqr.2).two_dvd
    · rw [if_neg hqr]
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
      · exact he
      · exfalso
        apply hqr
        have hN : Even (q ^ (n + 1) + 1) := by
          apply even_iff_two_dvd.mpr
          rw [← he]
          exact Nat.gcd_dvd_left _ _
        have hq : Odd q := by
          apply Nat.not_even_iff_odd.mp
          intro h
          exact (Nat.even_add_one.mp hN) (Nat.even_pow.mpr ⟨h, Nat.succ_ne_zero n⟩)
        refine ⟨hq, (kummerExponent_even_iff_of_odd q r hq).mp ?_⟩
        apply even_iff_two_dvd.mpr
        rw [← he]
        exact Nat.gcd_dvd_right _ _

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
