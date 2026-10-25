import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

/-!
# Nonvanishing of finite Möbius harmonic sums

A prime in the terminal half-interval appears in exactly one denominator. Its summand
has p-adic norm equal to the prime, while every other summand has norm at most one.
Thus the full sum has valuation minus one at every such prime. Bertrand's theorem
supplies a terminal prime at each cutoff above one.
-/

open Finset ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower
set_option autoImplicit false


/-- A prime in the terminal half-interval cannot divide any other positive denominator. -/
private theorem not_dvd_of_terminal_prime {N p n : ℕ}
    (hN : N < 2 * p) (hn : n ∈ Icc 1 N) (hne : n ≠ p) : ¬ p ∣ n := by
  rintro ⟨k, hk⟩
  have hk0 : k ≠ 0 := by intro h; simp [h] at hk; have := (mem_Icc.mp hn).1; omega
  have hk1 : k ≠ 1 := by intro h; simp [h] at hk; exact hne hk
  have hk2 : 2 ≤ k := by omega
  have hmul := Nat.mul_le_mul_left p hk2
  have hnp := (mem_Icc.mp hn).2
  rw [← hk] at hmul
  omega

/-- A terminal prime with a unit coefficient forces a pole in the finite rational sum. -/
theorem padicNorm_sum_int_div_nat_of_terminal_prime {N p : ℕ} (hp : p.Prime)
    (hpN : p ≤ N) (hNp : N < 2 * p) (a : ℕ → ℤ) (ha : ¬ (p : ℤ) ∣ a p) :
    padicNorm p (∑ n ∈ Icc 1 N, (a n : ℚ) / n) = p := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpI : p ∈ Icc 1 N := mem_Icc.mpr ⟨hp.one_le, hpN⟩
  have hrest : padicNorm p (∑ n ∈ (Icc 1 N).erase p, (a n : ℚ) / n) ≤ 1 := by
    apply padicNorm.sum_le' ?_ zero_le_one
    intro n hn
    obtain ⟨hne, hnI⟩ := mem_erase.mp hn
    rw [padicNorm.div, (padicNorm.nat_eq_one_iff n).mpr
      (not_dvd_of_terminal_prime hNp hnI hne), div_one]
    exact padicNorm.of_int (a n)
  have hpole : padicNorm p ((a p : ℚ) / p) = p := by
    rw [padicNorm.div, (padicNorm.int_eq_one_iff (a p)).mpr ha,
      padicNorm.padicNorm_p_of_prime, one_div, inv_inv]
  have hpR : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  rw [← sum_erase_add _ _ hpI]
  rw [padicNorm.add_eq_max_of_ne (by rw [hpole]; exact (hrest.trans_lt hpR).ne), hpole,
    max_eq_right (hrest.trans hpR.le)]

/-- The rational finite Möbius harmonic sum. -/
def moebiusHarmonicPartialRat (N : ℕ) : ℚ :=
  ∑ n ∈ Icc 1 N, (moebius n : ℚ) / n

/-- Every terminal prime has norm exactly `p` on the finite Möbius harmonic sum. -/
theorem padicNorm_moebiusHarmonicPartialRat {N p : ℕ} (hp : p.Prime)
    (hpN : p ≤ N) (hNp : N < 2 * p) :
    padicNorm p (moebiusHarmonicPartialRat N) = p := by
  apply padicNorm_sum_int_div_nat_of_terminal_prime hp hpN hNp moebius
  rw [ArithmeticFunction.moebius_apply_prime hp]
  intro h
  have h1 : (p : ℤ) ∣ 1 := (dvd_neg.mp h)
  have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  have := Int.le_of_dvd (by norm_num : (0 : ℤ) < 1) h1
  linarith only [this, hp1]

/-- Finite Möbius harmonic sums never vanish at a positive cutoff. -/
theorem moebiusHarmonicPartialRat_ne_zero {N : ℕ} (hN : 1 ≤ N) :
    moebiusHarmonicPartialRat N ≠ 0 := by
  by_cases hN1 : N = 1
  · simp [hN1, moebiusHarmonicPartialRat]
  have hN2 : 2 ≤ N := by omega
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 2) (by omega)
  have h := padicNorm_moebiusHarmonicPartialRat (N := N) hp (by omega) (by omega)
  intro hz
  rw [hz, padicNorm.zero] at h
  exact hp.ne_zero (by exact_mod_cast h.symm)

/-- Every terminal prime has valuation minus one on the finite Möbius harmonic sum. -/
theorem padicValRat_moebiusHarmonicPartialRat {N p : ℕ} (hp : p.Prime)
    (hpN : p ≤ N) (hNp : N < 2 * p) :
    padicValRat p (moebiusHarmonicPartialRat N) = -1 := by
  have hnorm := padicNorm_moebiusHarmonicPartialRat hp hpN hNp
  have hne := moebiusHarmonicPartialRat_ne_zero (hp.one_le.trans hpN)
  rw [padicNorm.eq_zpow_of_nonzero hne] at hnorm
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hp1 : (p : ℚ) ≠ 1 := by exact_mod_cast hp.ne_one
  have hpow : (p : ℚ) ^ (-padicValRat p (moebiusHarmonicPartialRat N)) =
      (p : ℚ) ^ (1 : ℤ) := by simpa only [zpow_one] using hnorm
  have h := (zpow_right_inj₀ hp0 hp1).mp hpow
  omega

/-- Reduction preserves exactly one terminal-prime factor in the denominator. -/
theorem padicValNat_den_moebiusHarmonicPartialRat {N p : ℕ} (hp : p.Prime)
    (hpN : p ≤ N) (hNp : N < 2 * p) :
    padicValNat p (moebiusHarmonicPartialRat N).den = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  let q := moebiusHarmonicPartialRat N
  have hv := padicValRat_moebiusHarmonicPartialRat hp hpN hNp
  change (padicValNat p q.num.natAbs : ℤ) - (padicValNat p q.den : ℤ) = -1 at hv
  have hn : ¬ p ∣ q.num.natAbs := by
    intro hnum
    have hden : ¬ p ∣ q.den := by
      intro hd
      have h := Nat.dvd_gcd hnum hd
      rw [q.reduced] at h
      exact hp.ne_one (Nat.dvd_one.mp h)
    rw [padicValNat.eq_zero_of_not_dvd hden] at hv
    have hnonneg : (0 : ℤ) ≤ padicValNat p q.num.natAbs := by positivity
    omega
  rw [padicValNat.eq_zero_of_not_dvd hn] at hv
  change padicValNat p q.den = 1
  omega

theorem terminal_prime_dvd_den_moebiusHarmonicPartialRat {N p : ℕ} (hp : p.Prime)
    (hpN : p ≤ N) (hNp : N < 2 * p) :
    p ∣ (moebiusHarmonicPartialRat N).den ∧ ¬ p ^ 2 ∣ (moebiusHarmonicPartialRat N).den := by
  letI : Fact p.Prime := ⟨hp⟩
  have hv := padicValNat_den_moebiusHarmonicPartialRat hp hpN hNp
  constructor
  · by_contra hn
    rw [padicValNat.eq_zero_of_not_dvd hn] at hv
    norm_num at hv
  · intro hd
    have h := (Nat.pow_dvd_iff_le_padicValNat hp.ne_one
      (moebiusHarmonicPartialRat N).den_nz).mp hd
    omega

/-- Every product of distinct terminal primes divides the reduced denominator. -/
theorem prod_terminal_primes_dvd_den_moebiusHarmonicPartialRat (N : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ≤ N ∧ N < 2 * p) :
    (∏ p ∈ s, p) ∣ (moebiusHarmonicPartialRat N).den := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    have hp := hs p (mem_insert_self _ _)
    have hs' (q : ℕ) (hq : q ∈ s) := hs q (mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hp.1 (hs' q hq).1).mpr
        (by rintro rfl; exact hps hq)
    rw [prod_insert hps]
    exact hcop.mul_dvd_of_dvd_of_dvd
      (terminal_prime_dvd_den_moebiusHarmonicPartialRat hp.1 hp.2.1 hp.2.2).1 (ih hs')

/-- The real finite harmonic sum inherits exact rational nonvanishing. -/
theorem sum_moebius_div_ne_zero {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, (moebius n : ℝ) / n) ≠ 0 := by
  have h := moebiusHarmonicPartialRat_ne_zero hN
  change (∑ n ∈ Icc 1 N, (moebius n : ℚ) / n) ≠ 0 at h
  exact_mod_cast h


end RHTower
