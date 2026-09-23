import GaloisForLFunctions.RHTower.Sieve.RamareRoughBridge
import GaloisForLFunctions.RHTower.Sieve.SharedPrimeTail

/-!
# The square-divisible part of the Ramaré decomposition

In the bilinear sum an integer `n` divisible by a designated prime `p` is written `n = p·m`, and the
factorization `f(p·m) = f(p)·f(m)` needs `p ∤ m`, that is `p² ∤ n`.  The integers failing this are
those divisible by `p²`, and they are few: their count in an interval is `(b−a)/p² + O(1)`.

Summed over designated primes in a range `(P₁, P₂]`, the total is at most `(b−a)/P₁ + #P`, so the
obstruction to factorization is negligible exactly when the designated primes are large — which is
why the bilinear method designates primes from a high dyadic range.
-/

namespace RHTower.Sieve

open Finset

/-- The count of multiples of `p²` in an interval, from above. -/
theorem card_filter_sq_dvd_Ioc_lt {p a b : ℕ} (hp : 0 < p) (hab : a ≤ b) :
    (((({n ∈ Finset.Ioc a b | p * p ∣ n}).card : ℕ) : ℝ))
      < ((b : ℝ) - a) / ((p : ℝ) * (p : ℝ)) + 1 := by
  have hpp : 0 < p * p := Nat.mul_pos hp hp
  have hbound := abs_card_filter_dvd_Ioc_sub_lt (p * p) a b hpp hab
  have hcast : (((p * p : ℕ) : ℝ)) = (p : ℝ) * (p : ℝ) := by push_cast; ring
  rw [hcast] at hbound
  have := (abs_lt.1 hbound).2
  linarith

/-- **The square-divisible part is negligible for large designated primes.**  Summed over the
designated primes of a range, the integers whose designated prime divides them to the second power
number at most `(b−a)/P₁ + #P`. -/
theorem sum_card_filter_sq_dvd_le {P₁ P₂ a b : ℕ} (hP : 1 ≤ P₁) (hab : a ≤ b) :
    ∑ p ∈ bigPrimeSet P₁ P₂,
        (((({n ∈ Finset.Ioc a b | p * p ∣ n}).card : ℕ) : ℝ))
      ≤ ((b : ℝ) - a) / (P₁ : ℝ) + (((bigPrimeSet P₁ P₂).card : ℕ) : ℝ) := by
  classical
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hterm : ∀ p ∈ bigPrimeSet P₁ P₂,
      (((({n ∈ Finset.Ioc a b | p * p ∣ n}).card : ℕ) : ℝ))
        ≤ ((b : ℝ) - a) * (1 / (p : ℝ) ^ (2 : ℕ)) + 1 := by
    intro p hp
    have hppos : 0 < p := (prime_of_mem_bigPrimeSet hp).pos
    have hlt := card_filter_sq_dvd_Ioc_lt hppos hab
    have heq : ((b : ℝ) - a) / ((p : ℝ) * (p : ℝ)) = ((b : ℝ) - a) * (1 / (p : ℝ) ^ (2 : ℕ)) := by
      rw [pow_two]
      ring
    rw [heq] at hlt
    linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsq := sum_inv_sq_bigPrimeSet_le (P := P₁) hP P₂
  have hmul : ((b : ℝ) - a) * (∑ p ∈ bigPrimeSet P₁ P₂, (1 : ℝ) / (p : ℝ) ^ (2 : ℕ))
      ≤ ((b : ℝ) - a) * (1 / (P₁ : ℝ)) := mul_le_mul_of_nonneg_left hsq hlen
  have hdiv : ((b : ℝ) - a) * (1 / (P₁ : ℝ)) = ((b : ℝ) - a) / (P₁ : ℝ) := by ring
  linarith

end RHTower.Sieve
