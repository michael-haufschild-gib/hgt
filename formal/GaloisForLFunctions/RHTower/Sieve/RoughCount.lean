import GaloisForLFunctions.RHTower.Sieve.MertensSecond
import GaloisForLFunctions.RHTower.Sieve.Mertens

/-!
# Counting rough integers in an interval

Feeding Mertens' second theorem into Brun's pure sieve at the primorial modulus turns both Euler
products into explicit powers of `log z`:

`∏_{p ≤ z} (1 - 1/p) ≤ exp(mertensSecondLowerConst) / log z`,
`∏_{p ≤ z} (1 + λ/p) ≤ exp(λ · mertensSecondUpperConst) · (log z)^λ`.

The first is the sieve main term, the second the truncation defect.  Consequently the number of
integers in `Ioc a b` with no prime factor at most `z` is at most

`(b - a) · exp(c₀)/log z  +  (b - a) · exp(λ c₁) (log z)^λ / λ^r  +  #{d ∣ z# : ω d ≤ r}`,

for every even truncation level `r` and every tilt `λ ≥ 1`.  This is the fundamental-lemma input
for Shiu-type short-interval bounds.
-/

namespace RHTower.Sieve

open Finset Nat

/-- The sifting modulus of the primes up to `z` is squarefree with the expected prime support. -/
theorem squarefree_primorial' (z : ℕ) : Squarefree (primorial z) := squarefree_primorial z

/-- The Euler density of the primes up to `z` decays like `1 / log z`. -/
theorem prod_one_sub_inv_primesLE_le {z : ℕ} (hz : 2 ≤ z) :
    ∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ))
      ≤ Real.exp mertensSecondLowerConst / Real.log z := by
  have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hprod : ∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ)) ≤ Real.exp (-mertensS z) := by
    have hP : ∀ p ∈ Nat.primesLE z, 1 ≤ p := fun p hp =>
      (Nat.prime_of_mem_primesLE hp).one_lt.le
    have := prod_one_sub_inv_le_exp_neg_sum (Nat.primesLE z) hP
    simpa [mertensS] using this
  have hlow := le_mertensS hz
  have hexp : Real.exp (-mertensS z)
      ≤ Real.exp (-(logLog z - mertensSecondLowerConst)) := by
    exact Real.exp_le_exp.2 (by linarith)
  have hval : Real.exp (-(logLog z - mertensSecondLowerConst))
      = Real.exp mertensSecondLowerConst / Real.log z := by
    unfold logLog
    rw [neg_sub, Real.exp_sub, Real.exp_log hlogz]
  calc ∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ)) ≤ Real.exp (-mertensS z) := hprod
    _ ≤ Real.exp (-(logLog z - mertensSecondLowerConst)) := hexp
    _ = Real.exp mertensSecondLowerConst / Real.log z := hval

/-- The tilted Euler product grows at most like a fixed power of `log z`. -/
theorem prod_one_add_primesLE_le {z : ℕ} (hz : 2 ≤ z) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∏ p ∈ Nat.primesLE z, (1 + lam / (p : ℝ))
      ≤ Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam := by
  have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hprod : ∏ p ∈ Nat.primesLE z, (1 + lam / (p : ℝ)) ≤ Real.exp (lam * mertensS z) := by
    have := prod_one_add_le_exp_sum (Nat.primesLE z) hlam
    simpa [mertensS] using this
  have hup := mertensS_le hz
  have hexp : Real.exp (lam * mertensS z)
      ≤ Real.exp (lam * (logLog z + mertensSecondUpperConst)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hup hlam)
  have hval : Real.exp (lam * (logLog z + mertensSecondUpperConst))
      = Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam := by
    unfold logLog
    rw [Real.rpow_def_of_pos hlogz, mul_add, Real.exp_add, mul_comm]
    ring_nf
  calc ∏ p ∈ Nat.primesLE z, (1 + lam / (p : ℝ)) ≤ Real.exp (lam * mertensS z) := hprod
    _ ≤ Real.exp (lam * (logLog z + mertensSecondUpperConst)) := hexp
    _ = Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam := hval

/-- Being coprime to the primorial `z#` is exactly having no prime factor at most `z`. -/
theorem coprime_primorial_iff {z n : ℕ} :
    Nat.Coprime n (primorial z) ↔ ∀ p ∈ Nat.primesLE z, ¬ p ∣ n := by
  rw [primorial_eq_prod_primesLE]
  exact coprime_prod_primes_iff (fun p hp => Nat.prime_of_mem_primesLE hp) n

/-- **Rough integers in an interval.**  The fundamental-lemma bound produced by Brun's pure sieve
at the primorial modulus, with both Euler products evaluated by Mertens' second theorem. -/
theorem card_rough_Ioc_le {z a b r : ℕ} (hz : 2 ≤ z) (hab : a ≤ b) (hr : Even r)
    {lam : ℝ} (hlam : 1 ≤ lam) :
    (#{n ∈ Finset.Ioc a b | ∀ p ∈ Nat.primesLE z, ¬ p ∣ n} : ℝ)
      ≤ ((b : ℝ) - a) * (Real.exp mertensSecondLowerConst / Real.log z)
        + ((b : ℝ) - a)
            * (Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / lam ^ r)
        + (truncDivisors (primorial z) r).card := by
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le zero_lt_one hlam
  have hlamr : (0 : ℝ) < lam ^ r := pow_pos hlam0 r
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hset : {n ∈ Finset.Ioc a b | ∀ p ∈ Nat.primesLE z, ¬ p ∣ n}
      = {n ∈ Finset.Ioc a b | Nat.Coprime n (primorial z)} := by
    refine Finset.filter_congr ?_
    intro n _
    exact (coprime_primorial_iff (z := z) (n := n)).symm
  rw [hset]
  have hbase := card_coprime_Ioc_le_prod (primorial z) a b r (squarefree_primorial z) hab hr
    hlam
  rw [primeFactors_primorial_eq] at hbase
  have hmain : ((b : ℝ) - a) * ∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ))
      ≤ ((b : ℝ) - a) * (Real.exp mertensSecondLowerConst / Real.log z) :=
    mul_le_mul_of_nonneg_left (prod_one_sub_inv_primesLE_le hz) hlen
  have hdef : ((b : ℝ) - a) * ((∏ p ∈ Nat.primesLE z, (1 + lam / (p : ℝ))) / lam ^ r)
      ≤ ((b : ℝ) - a)
          * (Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / lam ^ r) := by
    refine mul_le_mul_of_nonneg_left ?_ hlen
    rw [div_le_div_iff_of_pos_right hlamr]
    exact prod_one_add_primesLE_le hz hlam0.le
  linarith

end RHTower.Sieve
