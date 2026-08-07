import GaloisForLFunctions.RHTower.Sieve.MultiplicativeLogRecursion

/-!
# The partial sum as a prime-weighted average of its divided values

Dividing the prime-only recursion by `log N` puts it in the form the mean-value theory uses:

`S_f(N) = (1/log N) ∑_{p ≤ N} f(p) log p · S_f(⌊N/p⌋) + O(N/log N)`.

The prime weights `log p` sum to `≍ N`, so the right-hand side is a genuine average: no cancellation is
assumed, and the error is smaller than the trivial size by a full logarithm.  Iterating this identity is
what produces the triple convolution of the Granville–Harper–Soundararajan argument, in which one factor
is estimated pointwise and the other two in mean square.
-/

noncomputable section

namespace RHTower.Sieve

open ArithmeticFunction Finset

variable {f : ℕ → ℂ}

/-- **The averaged recursion.**  The prime-only recursion divided by `log N`. -/
theorem norm_sum_Icc_sub_prime_average_le (hf : ∀ a b : ℕ, f (a * b) = f a * f b)
    (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) {N : ℕ} (hN : 2 ≤ N) :
    ‖(∑ n ∈ Finset.Icc 1 N, f n)
        - (∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
              ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k)
            / ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      ≤ (9 + RHTower.Mertens.mertensTail) * (N : ℝ) / Real.log (N : ℝ) := by
  classical
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN.trans_lt' one_lt_two
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hL : ((Real.log (N : ℝ) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hlog.ne'
  have hmain := norm_sum_Icc_mul_log_sub_sum_primes_le' hf hbdd N
  have hid : (∑ n ∈ Finset.Icc 1 N, f n)
        - (∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
              ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k)
            / ((Real.log (N : ℝ) : ℝ) : ℂ)
      = ((∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
          - ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
              ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k)
          / ((Real.log (N : ℝ) : ℝ) : ℂ) := by
    field_simp
  rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
  gcongr

/-- The averaged recursion, with the divided partial sums at their trivial size.  This is the shape a
second application of the recursion consumes: every inner sum is over a range at most `⌊N/2⌋`. -/
theorem norm_prime_average_le (hf : ∀ a b : ℕ, f (a * b) = f a * f b)
    (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) {N : ℕ} (hN : 2 ≤ N) :
    ‖∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
        ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k‖
      ≤ (N : ℝ) * Real.log (N : ℝ) + (9 + RHTower.Mertens.mertensTail) * (N : ℝ) := by
  classical
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN.trans_lt' one_lt_two
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hmain := norm_sum_Icc_mul_log_sub_sum_primes_le' hf hbdd N
  have htriv : ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤ (N : ℝ) := norm_sum_Icc_le hbdd N
  have hsplit : ‖∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
        ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
        + ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
            - ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
                ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k‖ := by
    have h := norm_sub_le ((∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ))
      ((∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
        - ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
            ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k)
    rwa [sub_sub_cancel] at h
  have hprod : ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      ≤ (N : ℝ) * Real.log (N : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
    exact mul_le_mul_of_nonneg_right htriv hlog.le
  linarith [hsplit, hprod, hmain]


/-- **The second application of the recursion.**  Replacing every inner partial sum `S_f(⌊N/p⌋)` by its
own prime-weighted average turns the prime-only recursion into a double prime average — the triple
multiplicative convolution of the Granville–Harper–Soundararajan argument.  The cost is the sum of the
individual averaging errors, one per prime of the chosen range. -/
theorem norm_sum_primes_sub_double_average_le (hf : ∀ a b : ℕ, f (a * b) = f a * f b)
    (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (N : ℕ) (P : Finset ℕ) (hP2 : ∀ p ∈ P, 2 ≤ N / p) :
    ‖(∑ p ∈ P, ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k)
        - ∑ p ∈ P, ((Real.log (p : ℝ) : ℝ) : ℂ) * f p *
            ((∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
                ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k)
              / ((Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ))‖
      ≤ ∑ p ∈ P, Real.log (p : ℝ)
          * ((9 + RHTower.Mertens.mertensTail) * ((N / p : ℕ) : ℝ)
              / Real.log ((N / p : ℕ) : ℝ)) := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p hp => ?_)
  have h2 : 2 ≤ N / p := hP2 p hp
  have hinner := norm_sum_Icc_sub_prime_average_le hf hbdd h2
  have hfactor : ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * (∑ k ∈ Finset.Icc 1 (N / p), f k)
      - ((Real.log (p : ℝ) : ℝ) : ℂ) * f p *
          ((∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
              ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k)
            / ((Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ))
      = ((Real.log (p : ℝ) : ℝ) : ℂ) * f p
          * ((∑ k ∈ Finset.Icc 1 (N / p), f k)
              - (∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
                  ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k)
                / ((Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ)) := by
    ring
  rw [hfactor, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hlogp : (0 : ℝ) ≤ Real.log (p : ℝ) := by
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hp0)
  rw [abs_of_nonneg hlogp, mul_assoc]
  have hstep : ‖f p‖ * ‖(∑ k ∈ Finset.Icc 1 (N / p), f k)
        - (∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
            ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k)
          / ((Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ)‖
      ≤ (9 + RHTower.Mertens.mertensTail) * ((N / p : ℕ) : ℝ)
          / Real.log ((N / p : ℕ) : ℝ) := by
    calc ‖f p‖ * ‖(∑ k ∈ Finset.Icc 1 (N / p), f k)
          - (∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
              ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k)
            / ((Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ)‖
        ≤ 1 * ((9 + RHTower.Mertens.mertensTail) * ((N / p : ℕ) : ℝ)
              / Real.log ((N / p : ℕ) : ℝ)) := by
          refine mul_le_mul (hbdd p) hinner (norm_nonneg _) zero_le_one
      _ = (9 + RHTower.Mertens.mertensTail) * ((N / p : ℕ) : ℝ)
            / Real.log ((N / p : ℕ) : ℝ) := one_mul _
  calc Real.log (p : ℝ) * (‖f p‖ * ‖(∑ k ∈ Finset.Icc 1 (N / p), f k)
        - (∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
            ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k)
          / ((Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ)‖)
      ≤ Real.log (p : ℝ) * ((9 + RHTower.Mertens.mertensTail) * ((N / p : ℕ) : ℝ)
            / Real.log ((N / p : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hstep hlogp
    _ = Real.log (p : ℝ) * ((9 + RHTower.Mertens.mertensTail) * ((N / p : ℕ) : ℝ)
            / Real.log ((N / p : ℕ) : ℝ)) := rfl

end RHTower.Sieve

end
