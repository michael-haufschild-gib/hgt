import GaloisForLFunctions.RHTower.Sieve.AverageBalancedDivisors

/-!
# The second moment of the balanced divisor count

Squaring the divisor count and exchanging the order of summation replaces the single divisibility by
a pair of them, which is one divisibility by the least common multiple:

`∑_{m ≤ X} (#{d ∣ m : y ≤ d ≤ 2y})² ≤ X ∑_{d₁,d₂ ∈ [y,2y]} 1/lcm(d₁,d₂)`.

This is the quantity a Cauchy–Schwarz passage from a representation count to a distinct-image count
needs: `#image ≥ (#representations)² / ∑ mult²`.  Unlike the first moment, which is bounded by `2`,
the second moment carries a logarithm, and that logarithm is exactly the `1/log x` in the card's
target shape.
-/

namespace RHTower.Sieve

open Finset

/-- **The second moment of the balanced divisor count.** -/
theorem sum_sq_card_divisors_window_le (X y : ℕ) :
    ∑ m ∈ Finset.Icc 1 X, ((((Finset.Icc y (2 * y)).filter (fun d => d ∣ m)).card : ℕ) : ℝ) ^ (2 : ℕ)
      ≤ (X : ℝ) * ∑ p ∈ (Finset.Icc y (2 * y)) ×ˢ (Finset.Icc y (2 * y)),
          1 / ((Nat.lcm p.1 p.2 : ℕ) : ℝ) := by
  classical
  have hIcc : Finset.Icc 1 X = Finset.Ioc 0 X := by
    ext x
    simp [Nat.lt_iff_add_one_le]
  have hsq : ∀ m : ℕ,
      ((((Finset.Icc y (2 * y)).filter (fun d => d ∣ m)).card : ℕ) : ℝ) ^ (2 : ℕ)
        = ∑ p ∈ (Finset.Icc y (2 * y)) ×ˢ (Finset.Icc y (2 * y)),
            (if Nat.lcm p.1 p.2 ∣ m then (1 : ℝ) else 0) := by
    intro m
    have hcount : ((((Finset.Icc y (2 * y)).filter (fun d => d ∣ m)).card : ℕ) : ℝ)
        = ∑ d ∈ Finset.Icc y (2 * y), (if d ∣ m then (1 : ℝ) else 0) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [sq, hcount, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
    by_cases h1 : d₁ ∣ m
    · by_cases h2 : d₂ ∣ m
      · rw [if_pos h1, if_pos h2, if_pos (Nat.lcm_dvd h1 h2), mul_one]
      · rw [if_pos h1, if_neg h2, mul_zero, if_neg]
        intro hc
        exact h2 (dvd_trans (Nat.dvd_lcm_right d₁ d₂) hc)
    · rw [if_neg h1, zero_mul, if_neg]
      intro hc
      exact h1 (dvd_trans (Nat.dvd_lcm_left d₁ d₂) hc)
  rw [Finset.sum_congr rfl fun m _ => hsq m, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  rcases Nat.eq_zero_or_pos (Nat.lcm p.1 p.2) with hl | hl
  · have hzero : ∑ m ∈ Finset.Icc 1 X, (if Nat.lcm p.1 p.2 ∣ m then (1 : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [Finset.mem_Icc] at hm
      rw [if_neg]
      intro hdvd
      rw [hl] at hdvd
      have := Nat.eq_zero_of_zero_dvd hdvd
      omega
    rw [hzero, hl]
    simp
  · have hinner : ∑ m ∈ Finset.Icc 1 X, (if Nat.lcm p.1 p.2 ∣ m then (1 : ℝ) else 0)
        = (((X / Nat.lcm p.1 p.2 : ℕ) : ℕ) : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hIcc]
      congr 1
      exact Nat.Ioc_filter_dvd_card_eq_div X (Nat.lcm p.1 p.2)
    rw [hinner]
    have hlR : (0 : ℝ) < ((Nat.lcm p.1 p.2 : ℕ) : ℝ) := by exact_mod_cast hl
    have hdiv : (((X / Nat.lcm p.1 p.2 : ℕ) : ℕ) : ℝ) ≤ (X : ℝ) / ((Nat.lcm p.1 p.2 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hlR]
      have := Nat.div_mul_le_self X (Nat.lcm p.1 p.2)
      exact_mod_cast this
    calc (((X / Nat.lcm p.1 p.2 : ℕ) : ℕ) : ℝ)
        ≤ (X : ℝ) / ((Nat.lcm p.1 p.2 : ℕ) : ℝ) := hdiv
      _ = (X : ℝ) * (1 / ((Nat.lcm p.1 p.2 : ℕ) : ℝ)) := by ring

end RHTower.Sieve
