import GaloisForLFunctions.RHTower.Sieve.DivisorMomentMeanSquare
import GaloisForLFunctions.RHTower.Sieve.Mertens
import GaloisForLFunctions.RHTower.Sieve.MertensSecond
import GaloisForLFunctions.RHTower.Sieve.BuchstabIdentity

/-!
# Euler-product bound for the minorant divisor moment

This file evaluates the Rankin tilt used for the `c₁,n` term of the
Matomäki--Teräväinen minorant. At `α = 1 / log z`, primes below `z` contribute at most `e` to the
first tilted product and at most `e²` to the second. Mertens' second theorem then makes the whole
divisor pair sum `exp (O(log log z))`.
-/

namespace RHTower.Sieve

open Finset Nat

/-- The sifting modulus is squarefree. -/
lemma siftModulus_squarefree (z : ℕ) : Squarefree (siftModulus z) := by
  unfold siftModulus
  exact Sieve.prodDistinctPrimes_squarefree z.primesBelow
    (fun p hp => (Nat.mem_primesBelow.mp hp).2)

/-- The prime factors of the sifting modulus are exactly the primes below its cutoff. -/
lemma primeFactors_siftModulus (z : ℕ) :
    (siftModulus z).primeFactors = z.primesBelow := by
  unfold siftModulus
  exact Nat.primeFactors_prod (fun p hp => (Nat.mem_primesBelow.mp hp).2)

/-- A finite Euler product with prime tilt `p^α ≤ λ` is controlled by the prime reciprocal sum. -/
theorem prod_one_add_rpow_sub_one_le_exp_sum
    (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    {α lam : ℝ} (hlam : 0 ≤ lam) (htilt : ∀ p ∈ S, (p : ℝ) ^ α ≤ lam) :
    ∏ p ∈ S, (1 + (p : ℝ) ^ (α - 1)) ≤
      Real.exp (lam * ∑ p ∈ S, 1 / (p : ℝ)) := by
  have hnonneg : ∀ p ∈ S, (0 : ℝ) ≤ 1 + (p : ℝ) ^ (α - 1) := by
    intro p _
    positivity
  have hfactor : ∀ p ∈ S,
      1 + (p : ℝ) ^ (α - 1) ≤ 1 + lam / (p : ℝ) := by
    intro p hp
    have hpR : 0 < (p : ℝ) := by exact_mod_cast (hprime p hp).pos
    rw [Real.rpow_sub hpR, Real.rpow_one]
    gcongr
    exact htilt p hp
  calc
    ∏ p ∈ S, (1 + (p : ℝ) ^ (α - 1)) ≤
        ∏ p ∈ S, (1 + lam / (p : ℝ)) :=
      Finset.prod_le_prod hnonneg hfactor
    _ ≤ Real.exp (lam * ∑ p ∈ S, 1 / (p : ℝ)) :=
      prod_one_add_le_exp_sum S hlam

/-- If `p < z`, then `p^(c/log z) ≤ exp c`. -/
lemma rpow_mul_inv_log_le_exp
    {p z : ℕ} (hp : Nat.Prime p) (hz : 2 ≤ z) (hpz : p < z)
    {c : ℝ} (hc : 0 ≤ c) :
    (p : ℝ) ^ (c / Real.log z) ≤ Real.exp c := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hlogz : 0 < Real.log z := by
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hz))
  have hpzR : (p : ℝ) ≤ (z : ℝ) := by exact_mod_cast hpz.le
  have hlogle : Real.log p ≤ Real.log z := Real.log_le_log hpR hpzR
  have hquot : Real.log p / Real.log z ≤ 1 := (div_le_one hlogz).2 hlogle
  rw [Real.rpow_def_of_pos hpR, Real.exp_le_exp]
  have hmul := mul_le_mul_of_nonneg_left hquot hc
  calc
    Real.log (p : ℝ) * (c / Real.log (z : ℝ)) =
        c * (Real.log (p : ℝ) / Real.log (z : ℝ)) := by ring
    _ ≤ c * 1 := hmul
    _ = c := mul_one c

/-- The tilted Euler product below `z` is bounded by the full Mertens reciprocal sum. -/
theorem prod_primesBelow_one_add_rpow_invLog_sub_one_le
    {z : ℕ} (hz : 2 ≤ z) (c : ℝ) (hc : 0 ≤ c) :
    ∏ p ∈ z.primesBelow,
        (1 + (p : ℝ) ^ (c / Real.log z - 1)) ≤
      Real.exp (Real.exp c * mertensS z) := by
  have hprod := prod_one_add_rpow_sub_one_le_exp_sum z.primesBelow
    (fun p hp => (Nat.mem_primesBelow.mp hp).2) (Real.exp_pos c).le
    (fun p hp => rpow_mul_inv_log_le_exp
      (Nat.mem_primesBelow.mp hp).2 hz (Nat.mem_primesBelow.mp hp).1 hc)
  refine hprod.trans ?_
  rw [Real.exp_le_exp]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos c).le
  unfold mertensS
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => by
      rw [Nat.mem_primesLE]
      exact ⟨(Nat.mem_primesBelow.mp hp).1.le,
        (Nat.mem_primesBelow.mp hp).2⟩)
    (fun p _ _ => by positivity)

/-- At the Rankin parameter `α = 1/log z`, the sifting-modulus divisor pair sum is bounded by an
explicit exponential of the prime reciprocal sum. -/
theorem sum_pair_gcd_siftModulus_invLog_le
    {z : ℕ} (hz : 2 ≤ z) :
    ∑ e₁ ∈ (siftModulus z).divisors, ∑ e₂ ∈ (siftModulus z).divisors,
        ((e₁ : ℝ) * (e₂ : ℝ)) ^ (1 / Real.log z - 1) *
          (e₁.gcd e₂ : ℝ) ≤
      Real.exp ((2 * Real.exp 1 + Real.exp 2) * mertensS z) := by
  have hpair := sum_pair_gcd_le_eulerProducts (siftModulus_pos z)
    (siftModulus_squarefree z) (1 / Real.log z)
  rw [primeFactors_siftModulus] at hpair
  have hA :
      ∏ p ∈ z.primesBelow, (1 + (p : ℝ) ^ (1 / Real.log z - 1)) ≤
        Real.exp (Real.exp 1 * mertensS z) := by
    simpa using prod_primesBelow_one_add_rpow_invLog_sub_one_le hz 1 (by norm_num)
  have hB :
      ∏ p ∈ z.primesBelow, (1 + (p : ℝ) ^ (2 * (1 / Real.log z) - 1)) ≤
        Real.exp (Real.exp 2 * mertensS z) := by
    simpa [div_eq_mul_inv] using
      prod_primesBelow_one_add_rpow_invLog_sub_one_le hz 2 (by norm_num)
  calc
    ∑ e₁ ∈ (siftModulus z).divisors, ∑ e₂ ∈ (siftModulus z).divisors,
        ((e₁ : ℝ) * (e₂ : ℝ)) ^ (1 / Real.log z - 1) *
          (e₁.gcd e₂ : ℝ) ≤
        (∏ p ∈ z.primesBelow,
          (1 + (p : ℝ) ^ (1 / Real.log z - 1))) ^ 2 *
          ∏ p ∈ z.primesBelow,
            (1 + (p : ℝ) ^ (2 * (1 / Real.log z) - 1)) := by
      simpa [add_comm] using hpair
    _ ≤ (Real.exp (Real.exp 1 * mertensS z)) ^ 2 *
        Real.exp (Real.exp 2 * mertensS z) := by gcongr
    _ = Real.exp ((2 * Real.exp 1 + Real.exp 2) * mertensS z) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

/-- Mertens' second theorem converts the divisor pair sum to an explicit `exp (O(log log z))`
bound. -/
theorem sum_pair_gcd_siftModulus_invLog_le_logLog
    {z : ℕ} (hz : 2 ≤ z) :
    ∑ e₁ ∈ (siftModulus z).divisors, ∑ e₂ ∈ (siftModulus z).divisors,
        ((e₁ : ℝ) * (e₂ : ℝ)) ^ (1 / Real.log z - 1) *
          (e₁.gcd e₂ : ℝ) ≤
      Real.exp ((2 * Real.exp 1 + Real.exp 2) *
        (logLog z + mertensSecondUpperConst)) := by
  refine (sum_pair_gcd_siftModulus_invLog_le hz).trans ?_
  rw [Real.exp_le_exp]
  exact mul_le_mul_of_nonneg_left (mertensS_le hz) (by positivity)

end RHTower.Sieve
