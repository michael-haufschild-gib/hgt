import GaloisForLFunctions.RHTower.Sieve.HardyRamanujanRecursion

/-!
# The prime power reciprocal sum

The Hardy–Ramanujan recursion sums over prime powers, so its weight is

`∑_{q = p^e ≤ b} 1/q = ∑_{p ≤ b} ∑_{e ≥ 1} p^{-e} = ∑_{p ≤ b} 1/(p-1) ≤ ∑_{p ≤ b} 1/p + 1`,

the last step being the telescoping correction already proved in `SmoothTilt.lean`.  So passing
from primes to prime powers costs at most one, and Mertens' second theorem still evaluates the
whole sum as `log log b + O(1)`.

The prime power parametrisation `(p, e) ↦ p^e` is injective by unique factorisation, so the
reindexing is an equality, not an inequality.
-/

namespace RHTower.Sieve

open Finset Nat

/-- The geometric tail of a prime's reciprocal powers. -/
theorem sum_inv_pow_Icc_le {p : ℕ} (hp : 2 ≤ p) (L : ℕ) :
    ∑ e ∈ Finset.Icc 1 L, (1 : ℝ) / (p : ℝ) ^ e ≤ 1 / ((p : ℝ) - 1) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  set r : ℝ := 1 / (p : ℝ) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr, div_lt_one (by linarith)]
    linarith
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hterm : ∀ e ∈ Finset.Icc 1 L, (1 : ℝ) / (p : ℝ) ^ e = r ^ e := by
    intro e _
    rw [hr, div_pow, one_pow]
  rw [Finset.sum_congr rfl hterm]
  have hIcc : Finset.Icc 1 L = Finset.Ico 1 (L + 1) := by
    ext x
    simp
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  have hshift : ∑ i ∈ Finset.range L, r ^ (1 + i) = r * ∑ i ∈ Finset.range L, r ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_add, pow_one]
  rw [hshift]
  have hbound : ∑ i ∈ Finset.range L, r ^ i ≤ 1 / (1 - r) := by
    have hne' : (1 : ℝ) - r ≠ 0 := ne_of_gt h1r
    have hpow : (0 : ℝ) ≤ r ^ L := pow_nonneg hr0 L
    have hkey : (r ^ L - 1) / (r - 1) = (1 - r ^ L) / (1 - r) := by
      rw [show (1 : ℝ) - r ^ L = -(r ^ L - 1) by ring, show (1 : ℝ) - r = -(r - 1) by ring,
        neg_div_neg_eq]
    rw [geom_sum_eq (by intro h; linarith [h] : r ≠ 1), hkey, div_le_div_iff_of_pos_right h1r]
    linarith
  have hval : r * (1 / (1 - r)) = 1 / ((p : ℝ) - 1) := by
    rw [hr]
    field_simp
  calc r * ∑ i ∈ Finset.range L, r ^ i ≤ r * (1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left hbound hr0
    _ = 1 / ((p : ℝ) - 1) := hval

/-- The prime power parametrisation is injective. -/
theorem primePow_injOn {z Y : ℕ} :
    ∀ x ∈ Nat.primesLE z ×ˢ Finset.Icc 1 (Nat.log 2 Y),
      ∀ y ∈ Nat.primesLE z ×ˢ Finset.Icc 1 (Nat.log 2 Y),
        x.1 ^ x.2 = y.1 ^ y.2 → x = y := by
  rintro ⟨p, e⟩ hx ⟨p', e'⟩ hy hxy
  obtain ⟨hp, he⟩ := Finset.mem_product.1 hx
  obtain ⟨hp', he'⟩ := Finset.mem_product.1 hy
  have hpprime : p.Prime := Nat.prime_of_mem_primesLE hp
  have hp'prime : p'.Prime := Nat.prime_of_mem_primesLE hp'
  have he1 : 1 ≤ e := (Finset.mem_Icc.1 he).1
  have hpp : p = p' := by
    have hdvd : p ∣ p' ^ e' := by
      rw [← hxy]
      exact dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hpprime hp'prime).1 (hpprime.dvd_of_dvd_pow hdvd)
  subst hpp
  have hee : e = e' := Nat.pow_right_injective hpprime.two_le hxy
  subst hee
  rfl

/-- **Prime power reciprocal sum.**  Summing over prime powers rather than primes costs at most
one. -/
theorem sum_inv_primePowerSet_le (b : ℕ) :
    ∑ q ∈ primePowerSet b b, (1 : ℝ) / (q : ℝ) ≤ mertensS b + 1 := by
  classical
  have hsum : ∑ q ∈ primePowerSet b b, (1 : ℝ) / (q : ℝ)
      = ∑ x ∈ Nat.primesLE b ×ˢ Finset.Icc 1 (Nat.log 2 b),
          (1 : ℝ) / ((x.1 ^ x.2 : ℕ) : ℝ) := by
    rw [primePowerSet]
    exact Finset.sum_image primePow_injOn
  rw [hsum, Finset.sum_product]
  refine le_trans (Finset.sum_le_sum ?_) (sum_inv_pred_primesLE_le b)
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primesLE hp
  have hcast : ∀ e ∈ Finset.Icc 1 (Nat.log 2 b),
      (1 : ℝ) / ((p ^ e : ℕ) : ℝ) = (1 : ℝ) / (p : ℝ) ^ e := by
    intro e _
    push_cast
    ring
  rw [Finset.sum_congr rfl hcast]
  exact sum_inv_pow_Icc_le hprime.two_le (Nat.log 2 b)

end RHTower.Sieve
