import GaloisForLFunctions.RHTower.Sieve.RoughPairSieve

/-!
# The two-dimensional Euler factor dominates the square of the one-dimensional one

The Euler product of the shifted-pair sieve has local factor `1 + c_p/(p − c_p)` with `c_p ∈ {1,2}`.
Off the shift this is `p/(p−2)`, which exceeds `(p/(p−1))²` because `(p−1)² ≥ p(p−2)`; on the shift
it is `p/(p−1)`, which is `(p/(p−1))²` times `(p−1)/p`.

So the whole product is at least the **square** of the classical Mertens product, times one factor
`(p−1)/p` for each sifting prime dividing the shift — and since every sifting prime exceeds `P₁`,
which in the application dwarfs the number of prime divisors of the shift, that correction is
bounded below by a constant.  This is what turns the sieve into the `(log P₁/log h)²` saving.
-/

namespace RHTower.Sieve

open Finset

/-- **The local factor dominates the square of the classical one.** -/
theorem pairFactor_ge (d : ℕ) {p : ℕ} (hp : 3 ≤ p) :
    ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 * (if p ∣ d then ((p : ℝ) - 1) / (p : ℝ) else 1)
      ≤ pairClassCount d p / ((p : ℝ) - pairClassCount d p) + 1 := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  rw [pairClassCount]
  split_ifs with hd
  · have hval : ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 * (((p : ℝ) - 1) / (p : ℝ))
        = 1 / ((p : ℝ) - 1) + 1 := by
      field_simp
      ring
    exact le_of_eq hval
  · rw [mul_one]
    have hR : (2 : ℝ) / ((p : ℝ) - 2) + 1 = (p : ℝ) / ((p : ℝ) - 2) := by
      field_simp
      ring
    rw [hR, div_pow, div_le_div_iff₀ (by positivity) hp2]
    nlinarith [hp3, hp0, hp1, hp2]

/-- **The Euler product of the pair sieve dominates the square of the Mertens product.** -/
theorem prod_pairFactor_ge (d : ℕ) {s : Finset ℕ} (hs : ∀ p ∈ s, 3 ≤ p) :
    (∏ p ∈ s, ((p : ℝ) / ((p : ℝ) - 1))) ^ 2
        * ∏ p ∈ s.filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ))
      ≤ ∏ p ∈ s, (pairClassCount d p / ((p : ℝ) - pairClassCount d p) + 1) := by
  classical
  have hsplit : (∏ p ∈ s, ((p : ℝ) / ((p : ℝ) - 1))) ^ 2
      * ∏ p ∈ s.filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ))
      = ∏ p ∈ s, (((p : ℝ) / ((p : ℝ) - 1)) ^ 2
          * (if p ∣ d then ((p : ℝ) - 1) / (p : ℝ) else 1)) := by
    rw [Finset.prod_mul_distrib, ← Finset.prod_pow]
    congr 1
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
  rw [hsplit]
  refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => pairFactor_ge d (hs p hp))
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hs p hp
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  split_ifs <;> positivity

end RHTower.Sieve
