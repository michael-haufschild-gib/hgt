import GaloisForLFunctions.RHTower.Sieve.LevelRegroup
import GaloisForLFunctions.RHTower.Sieve.SmoothTilt

/-!
# Chernoff form of the distinct prime count tails

Mertens' second theorem turns every Euler product appearing in the two tail bounds into an explicit
power of `log z`:

`∏_{p ≤ z} (1 - c/p) ≤ exp(c·c₀) (log z)^{-c}`,  `∏_{p ≤ z} (1 + c/p) ≤ exp(c·c₁) (log z)^{c}`,

with `c₀ = mertensSecondLowerConst` and `c₁ = mertensSecondUpperConst`.  Substituting these into
the tail bounds leaves the classical Chernoff shape: a factor `t^{-k} (log z)^{-(1-t)}` for the
lower tail and `u^{-k'} (log z)^{u-1}` for the upper one, whose optimisation in the tilt reproduces
the entropy rate `I(c) = 1 - c + c log c`.

The reciprocal sum over the primes of a window `(z, b]` is the difference of two Mertens sums, so
the large-prime factor is controlled the same way.
-/

namespace RHTower.Sieve

open Finset Nat

/-- `1 - c·w ≤ exp(-c·w)` in product form, for a nonnegative weight bounded by one. -/
theorem prod_one_sub_mul_le_exp_neg (P : Finset ℕ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hP : ∀ p ∈ P, 1 ≤ p) :
    ∏ p ∈ P, (1 - 1 / (p : ℝ) * c) ≤ Real.exp (-(c * ∑ p ∈ P, 1 / (p : ℝ))) := by
  have hinv : ∀ p ∈ P, (0 : ℝ) ≤ 1 / (p : ℝ) ∧ 1 / (p : ℝ) ≤ 1 := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hP p hp
    constructor
    · positivity
    · rw [div_le_one (by linarith)]
      exact hp1
  have hnonneg : ∀ p ∈ P, (0 : ℝ) ≤ 1 - 1 / (p : ℝ) * c := by
    intro p hp
    obtain ⟨h0, h1⟩ := hinv p hp
    nlinarith
  have hstep : ∀ p ∈ P, 1 - 1 / (p : ℝ) * c ≤ Real.exp (-(c * (1 / (p : ℝ)))) := by
    intro p _
    have := Real.add_one_le_exp (-(c * (1 / (p : ℝ))))
    linarith
  calc ∏ p ∈ P, (1 - 1 / (p : ℝ) * c)
      ≤ ∏ p ∈ P, Real.exp (-(c * (1 / (p : ℝ)))) := Finset.prod_le_prod hnonneg hstep
    _ = Real.exp (∑ p ∈ P, -(c * (1 / (p : ℝ)))) := (Real.exp_sum _ _).symm
    _ = Real.exp (-(c * ∑ p ∈ P, 1 / (p : ℝ))) := by
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum]

/-- **Lower Euler product in Chernoff form.** -/
theorem prod_one_sub_mul_primesLE_le {z : ℕ} (hz : 2 ≤ z) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ) * c)
      ≤ Real.exp (c * mertensSecondLowerConst) * (Real.log z) ^ (-c) := by
  have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hP : ∀ p ∈ Nat.primesLE z, 1 ≤ p := fun p hp =>
    (Nat.prime_of_mem_primesLE hp).one_lt.le
  refine le_trans (prod_one_sub_mul_le_exp_neg (Nat.primesLE z) hc0 hc1 hP) ?_
  have hsum : (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) = mertensS z := rfl
  rw [hsum]
  have hlow := le_mertensS hz
  have hmono : Real.exp (-(c * mertensS z))
      ≤ Real.exp (-(c * (logLog z - mertensSecondLowerConst))) := by
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hlow hc0
    linarith
  refine le_trans hmono (le_of_eq ?_)
  unfold logLog
  rw [Real.rpow_def_of_pos hlogz, ← Real.exp_add]
  congr 1
  ring

/-- **Upper Euler product in Chernoff form.** -/
theorem prod_one_add_primesLE_chernoff {z : ℕ} (hz : 2 ≤ z) {c : ℝ} (hc0 : 0 ≤ c) :
    ∏ p ∈ Nat.primesLE z, (1 + c / (p : ℝ))
      ≤ Real.exp (c * mertensSecondUpperConst) * (Real.log z) ^ c :=
  prod_one_add_primesLE_le hz hc0

/-- The primes of a window are the difference of two prime sets. -/
theorem bigPrimeSet_eq_sdiff (z b : ℕ) (_hzb : z ≤ b) :
    bigPrimeSet z b = Nat.primesLE b \ Nat.primesLE z := by
  classical
  ext p
  simp only [bigPrimeSet, Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff,
    Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hz1, hpb⟩, hprime⟩
    exact ⟨⟨hpb, hprime⟩, fun hcon => by omega⟩
  · rintro ⟨⟨hpb, hprime⟩, hnot⟩
    refine ⟨⟨?_, hpb⟩, hprime⟩
    by_contra hcon
    exact hnot ⟨by omega, hprime⟩

/-- The reciprocal sum over a prime window is a difference of Mertens sums. -/
theorem sum_inv_bigPrimeSet (z b : ℕ) (hzb : z ≤ b) :
    ∑ p ∈ bigPrimeSet z b, (1 : ℝ) / p = mertensS b - mertensS z := by
  classical
  have hsub : Nat.primesLE z ⊆ Nat.primesLE b := by
    intro p hp
    obtain ⟨hpz, hprime⟩ := Nat.mem_primesLE.1 hp
    exact Nat.mem_primesLE.2 ⟨by omega, hprime⟩
  rw [bigPrimeSet_eq_sdiff z b hzb, Finset.sum_sdiff_eq_sub hsub]
  rfl

/-- **Window Euler product in Chernoff form.** -/
theorem prod_one_add_bigPrimeSet_le {z b : ℕ} (hzb : z ≤ b) {v : ℝ} (hv : 0 ≤ v) :
    ∏ p ∈ bigPrimeSet z b, (1 + v / (p : ℝ))
      ≤ Real.exp (v * (mertensS b - mertensS z)) := by
  have hw : ∀ p ∈ bigPrimeSet z b, (0 : ℝ) ≤ 1 / (p : ℝ) := by
    intro p _
    positivity
  have hrw : ∏ p ∈ bigPrimeSet z b, (1 + v / (p : ℝ))
      = ∏ p ∈ bigPrimeSet z b, (1 + v * (1 / (p : ℝ))) := by
    refine Finset.prod_congr rfl ?_
    intro p _
    rw [mul_one_div]
  rw [hrw]
  refine le_trans (prod_one_add_mul_le_exp _ hv _ hw) ?_
  rw [sum_inv_bigPrimeSet z b hzb]

/-- **Lower tail, Chernoff form.**  Every Euler product is an explicit power of `log z`. -/
theorem card_omega_le_le_chernoff (a b z k r : ℕ) (hab : a ≤ b) (hz : 2 ≤ z) (hr : Even r)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) {lam : ℝ} (hlam : 1 ≤ lam) :
    ((#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} : ℕ) : ℝ) * t ^ k
      ≤ ((b : ℝ) - a) * (Real.exp ((1 - t) * mertensSecondLowerConst) * (Real.log z) ^ (-(1 - t))
            + Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / lam ^ r)
        + ((truncDivisors (primorial z) r).card : ℝ) := by
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le zero_lt_one hlam
  have hlamr : (0 : ℝ) < lam ^ r := pow_pos hlam0 r
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  refine le_trans (card_omega_le_le_euler a b z k r hab hr ht0 ht1 hlam) ?_
  have h1 : ∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ) * (1 - t))
      ≤ Real.exp ((1 - t) * mertensSecondLowerConst) * (Real.log z) ^ (-(1 - t)) :=
    prod_one_sub_mul_primesLE_le hz (by linarith) (by linarith)
  have h2 : (∏ p ∈ Nat.primesLE z, (1 + lam / (p : ℝ))) / lam ^ r
      ≤ Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / lam ^ r := by
    rw [div_le_div_iff_of_pos_right hlamr]
    exact prod_one_add_primesLE_chernoff hz hlam0.le
  have hsum : (∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ) * (1 - t)))
        + (∏ p ∈ Nat.primesLE z, (1 + lam / (p : ℝ))) / lam ^ r
      ≤ Real.exp ((1 - t) * mertensSecondLowerConst) * (Real.log z) ^ (-(1 - t))
        + Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / lam ^ r := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hlen
  linarith

/-- **Upper tail, Chernoff form.** -/
theorem card_omega_ge_le_chernoff (a b z k k' J c D : ℕ) (hab : a ≤ b) (hz : 2 ≤ z) (hzb : z ≤ b)
    (hJ : 1 ≤ J) (hc : 1 ≤ c) (hD : b < (D + 1) ^ c) (hk : k' + c * J ≤ k + 1)
    {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) {v : ℝ} (hv : 1 ≤ v) :
    ((#{n ∈ Finset.Ioc a b | k ≤ n.primeFactors.card} : ℕ) : ℝ)
      ≤ (((b : ℝ) - a) * (Real.exp ((u - 1) * mertensSecondUpperConst) * (Real.log z) ^ (u - 1))
            + ((truncDivisors (primorial z) k').card : ℝ)) / u ^ k'
        + (((b : ℝ) - a) * (Real.exp (v * (mertensS b - mertensS z)) / v ^ J) + (D : ℝ)) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
  have huk : (0 : ℝ) < u ^ k' := pow_pos hu0 k'
  have hv0 : (0 : ℝ) < v := lt_of_lt_of_le zero_lt_one hv
  have hvJ : (0 : ℝ) < v ^ J := pow_pos hv0 J
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  refine le_trans (card_omega_ge_le_euler a b z k k' J c D hab hJ hc hD hk hu1 hu2 hv) ?_
  have hsmall : (((b : ℝ) - a) * (∏ p ∈ Nat.primesLE z, (1 + (u - 1) / (p : ℝ)))
        + ((truncDivisors (primorial z) k').card : ℝ)) / u ^ k'
      ≤ (((b : ℝ) - a) * (Real.exp ((u - 1) * mertensSecondUpperConst) * (Real.log z) ^ (u - 1))
          + ((truncDivisors (primorial z) k').card : ℝ)) / u ^ k' := by
    rw [div_le_div_iff_of_pos_right huk]
    have := mul_le_mul_of_nonneg_left
      (prod_one_add_primesLE_chernoff (c := u - 1) hz (by linarith)) hlen
    linarith
  have hbig : ((b : ℝ) - a) * ((∏ p ∈ bigPrimeSet z b, (1 + v / (p : ℝ))) / v ^ J) + (D : ℝ)
      ≤ ((b : ℝ) - a) * (Real.exp (v * (mertensS b - mertensS z)) / v ^ J) + (D : ℝ) := by
    have hdiv : (∏ p ∈ bigPrimeSet z b, (1 + v / (p : ℝ))) / v ^ J
        ≤ Real.exp (v * (mertensS b - mertensS z)) / v ^ J := by
      rw [div_le_div_iff_of_pos_right hvJ]
      exact prod_one_add_bigPrimeSet_le hzb hv0.le
    have := mul_le_mul_of_nonneg_left hdiv hlen
    linarith
  linarith

end RHTower.Sieve
