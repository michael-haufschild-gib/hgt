import GaloisForLFunctions.RHTower.Sieve.TruncationDefect
import Mathlib.NumberTheory.Primorial

/-!
# Euler products against the prime reciprocal sum, and Chebyshev's upper bound

Two elementary comparisons turn the Euler products appearing in Brun's pure sieve into the single
quantity `∑_{p ∈ P} 1/p`:

`∏_{p ∈ P} (1 - 1/p) ≤ exp (-∑_{p ∈ P} 1/p)`,  `∏_{p ∈ P} (1 + λ/p) ≤ exp (λ ∑_{p ∈ P} 1/p)`.

Both follow from `1 + x ≤ exp x`.  The first turns the sieve main term into an exponential
decay, the second turns the truncation defect into an exponential growth, so the sieve output is
governed entirely by the prime reciprocal sum.

The file also records Chebyshev's upper bound `∑_{p ≤ n} log p ≤ n log 4`, read off from the
primorial bound `n# ≤ 4^n`.
-/

namespace RHTower.Sieve

open Finset Nat

/-- `1 - x ≤ exp (-x)`, the form used for the sieve main term. -/
theorem one_sub_le_exp_neg (x : ℝ) : 1 - x ≤ Real.exp (-x) := by
  have := Real.add_one_le_exp (-x)
  linarith

/-- **Main-term comparison.**  An Euler product of sieve densities is at most the exponential of
minus the prime reciprocal sum. -/
theorem prod_one_sub_inv_le_exp_neg_sum (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) :
    ∏ p ∈ P, (1 - 1 / (p : ℝ)) ≤ Real.exp (-∑ p ∈ P, 1 / (p : ℝ)) := by
  have hnonneg : ∀ p ∈ P, (0 : ℝ) ≤ 1 - 1 / (p : ℝ) := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hP p hp
    have : 1 / (p : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hp1
    linarith
  have hstep : ∀ p ∈ P, 1 - 1 / (p : ℝ) ≤ Real.exp (-(1 / (p : ℝ))) := fun p _ =>
    one_sub_le_exp_neg _
  calc ∏ p ∈ P, (1 - 1 / (p : ℝ))
      ≤ ∏ p ∈ P, Real.exp (-(1 / (p : ℝ))) := Finset.prod_le_prod hnonneg hstep
    _ = Real.exp (∑ p ∈ P, -(1 / (p : ℝ))) := (Real.exp_sum _ _).symm
    _ = Real.exp (-∑ p ∈ P, 1 / (p : ℝ)) := by rw [Finset.sum_neg_distrib]

/-- **Defect comparison.**  A tilted Euler product is at most the exponential of the tilted prime
reciprocal sum. -/
theorem prod_one_add_le_exp_sum (P : Finset ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∏ p ∈ P, (1 + lam / (p : ℝ)) ≤ Real.exp (lam * ∑ p ∈ P, 1 / (p : ℝ)) := by
  have hnonneg : ∀ p ∈ P, (0 : ℝ) ≤ 1 + lam / (p : ℝ) := by
    intro p _
    have : (0 : ℝ) ≤ lam / (p : ℝ) := by positivity
    linarith
  have hstep : ∀ p ∈ P, 1 + lam / (p : ℝ) ≤ Real.exp (lam * (1 / (p : ℝ))) := by
    intro p _
    have := Real.add_one_le_exp (lam * (1 / (p : ℝ)))
    have hrw : lam / (p : ℝ) = lam * (1 / (p : ℝ)) := by ring
    rw [hrw]
    linarith
  calc ∏ p ∈ P, (1 + lam / (p : ℝ))
      ≤ ∏ p ∈ P, Real.exp (lam * (1 / (p : ℝ))) := Finset.prod_le_prod hnonneg hstep
    _ = Real.exp (∑ p ∈ P, lam * (1 / (p : ℝ))) := (Real.exp_sum _ _).symm
    _ = Real.exp (lam * ∑ p ∈ P, 1 / (p : ℝ)) := by rw [← Finset.mul_sum]

/-- **Chebyshev's upper bound.**  The logarithmic prime counting function is at most `n log 4`. -/
theorem sum_log_primesLE_le (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, Real.log p ≤ (n : ℝ) * Real.log 4 := by
  have hpos : ∀ p ∈ Nat.primesLE n, (0 : ℝ) < (p : ℝ) := by
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
  have hprodcast : ((primorial n : ℕ) : ℝ) = ∏ p ∈ Nat.primesLE n, (p : ℝ) := by
    rw [primorial_eq_prod_primesLE]
    push_cast
    ring
  have hle : (∏ p ∈ Nat.primesLE n, (p : ℝ)) ≤ (4 : ℝ) ^ n := by
    rw [← hprodcast]
    exact_mod_cast primorial_le_four_pow n
  have hlog : Real.log (∏ p ∈ Nat.primesLE n, (p : ℝ)) = ∑ p ∈ Nat.primesLE n, Real.log p :=
    Real.log_prod fun p hp => (hpos p hp).ne'
  have hprodpos : (0 : ℝ) < ∏ p ∈ Nat.primesLE n, (p : ℝ) := Finset.prod_pos hpos
  calc ∑ p ∈ Nat.primesLE n, Real.log p
      = Real.log (∏ p ∈ Nat.primesLE n, (p : ℝ)) := hlog.symm
    _ ≤ Real.log ((4 : ℝ) ^ n) := Real.log_le_log hprodpos hle
    _ = (n : ℝ) * Real.log 4 := by rw [Real.log_pow]

/-- The prime support of the primorial is the set of primes up to `n`, so Brun's pure sieve with
modulus `n#` sifts exactly by those primes. -/
theorem primeFactors_primorial_eq (n : ℕ) : (primorial n).primeFactors = Nat.primesLE n :=
  primeFactors_primorial n

end RHTower.Sieve
