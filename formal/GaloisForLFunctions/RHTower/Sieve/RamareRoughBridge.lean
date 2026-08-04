import GaloisForLFunctions.RHTower.Sieve.RamareWeight
import GaloisForLFunctions.RHTower.Sieve.RoughCount

/-!
# Ramaré's decomposition with the remainder bounded by the sieve

Ramaré's identity turns a sum into a bilinear sum over designated primes and their cofactors, plus
the part carried by integers with no designated prime factor.  That remainder is a sum over rough
integers, so Brun's sieve bounds it: for a bounded function the whole error is at most the sup norm
times the rough count.

Taking the designated primes to be all primes up to `z` and the range to be an interval, the error
is `O((b−a)/log z)`, which is the reduction the bilinear method needs before any Dirichlet
polynomial appears.
-/

namespace RHTower.Sieve

open Finset

/-- Having no designated prime factor is having no designated prime divisor. -/
theorem primeFactorsIn_eq_empty_iff {P : Finset ℕ} {n : ℕ} :
    primeFactorsIn P n = ∅ ↔ ∀ p ∈ P, ¬ p ∣ n := by
  classical
  rw [primeFactorsIn, Finset.filter_eq_empty_iff]

/-- **The Ramaré remainder is a rough-integer sum.** -/
theorem abs_sum_sub_ramare_le (P S : Finset ℕ) (f : ℕ → ℝ) {B : ℝ}
    (hf : ∀ n ∈ S, |f n| ≤ B) :
    |∑ n ∈ S, f n
        - ∑ p ∈ P, ∑ n ∈ {n ∈ S | p ∣ n}, f n / ((primeFactorsIn P n).card : ℝ)|
      ≤ B * ((({n ∈ S | ∀ p ∈ P, ¬ p ∣ n}).card : ℕ) : ℝ) := by
  classical
  have hsplit := sum_eq_ramare_add_rough P S f
  have hset : {n ∈ S | primeFactorsIn P n = ∅} = {n ∈ S | ∀ p ∈ P, ¬ p ∣ n} := by
    refine Finset.filter_congr ?_
    intro n _
    rw [primeFactorsIn_eq_empty_iff]
  have hrw : ∑ n ∈ S, f n
      - ∑ p ∈ P, ∑ n ∈ {n ∈ S | p ∣ n}, f n / ((primeFactorsIn P n).card : ℝ)
      = ∑ n ∈ {n ∈ S | ∀ p ∈ P, ¬ p ∣ n}, f n := by
    rw [hsplit, hset]
    ring
  rw [hrw]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun n hn => hf n (Finset.mem_filter.1 hn).1)) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact le_of_eq (by ring)

/-- **Ramaré's decomposition on an interval, with the sieve error.**  Every bounded sum over an
interval is its Ramaré bilinear part up to an error of order `(b−a)/log z`. -/
theorem abs_sum_sub_ramare_Ioc_le {z a b r : ℕ} (hz : 2 ≤ z) (hab : a ≤ b) (hr : Even r)
    {lam : ℝ} (hlam : 1 ≤ lam) (f : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ n ∈ Finset.Ioc a b, |f n| ≤ B) :
    |∑ n ∈ Finset.Ioc a b, f n
        - ∑ p ∈ Nat.primesLE z, ∑ n ∈ {n ∈ Finset.Ioc a b | p ∣ n},
            f n / ((primeFactorsIn (Nat.primesLE z) n).card : ℝ)|
      ≤ B * (((b : ℝ) - a) * (Real.exp mertensSecondLowerConst / Real.log z)
          + ((b : ℝ) - a)
              * (Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / lam ^ r)
          + (truncDivisors (primorial z) r).card) := by
  refine le_trans (abs_sum_sub_ramare_le (Nat.primesLE z) (Finset.Ioc a b) f hf) ?_
  exact mul_le_mul_of_nonneg_left (card_rough_Ioc_le hz hab hr hlam) hB

end RHTower.Sieve
