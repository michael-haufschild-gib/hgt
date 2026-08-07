import GaloisForLFunctions.RHTower.Sieve.MultiplicativeLogRecursion
import GaloisForLFunctions.RHTower.Sieve.PrimeLogQuotientSum
/-!
# The second application of the logarithmic recursion

The recursion at scale `⌊N/p⌋`, divided by `log⌊N/p⌋` and weighted by `f(p)log p`, replaces the inner
partial sum of the outer prime average by the inner prime average:

`f(p)log p·∑_{k ≤ N/p} f(k) = (f(p)log p/log⌊N/p⌋)·∑_q f(q)log q ∑_{k ≤ N/pq} f(k) + error_p`,
`‖error_p‖ ≤ (9 + mertensTail)·(log p/log⌊N/p⌋)·⌊N/p⌋`.

Summed over the primes whose complementary scale is at least `2` — the condition that keeps the divisor
`log⌊N/p⌋` positive — the dyadic quotient-window estimate evaluates the total error:

`∑_p (log p/log⌊N/p⌋)·⌊N/p⌋ ≤ N·(B/log 2)·(1 + log log₂ N)`,

so the second application costs `O(N log log N)` against a main term of size `N log N`.  The whole saving of
the second application is a logarithm up to `log log`, and it is the quotient-window blocking — not a
double-exponential dissection — that delivers it.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

variable {f : ℕ → ℂ}

/-- **The second application of the logarithmic recursion, at one prime.**  Dividing the recursion at scale
`⌊N/p⌋` by `log⌊N/p⌋` and weighting it by `f(p)log p` replaces the inner partial sum by the inner prime
average, at the cost of the weighted error of the recursion. -/
theorem norm_log_mul_partialSum_sub_inner_le (hf : ∀ a b : ℕ, f (a * b) = f a * f b)
    (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) {p N : ℕ} (h2 : 2 ≤ N / p) :
    ‖((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k
        - ((Real.log (p : ℝ) / Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ) * f p
            * ∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
                ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k‖
      ≤ (9 + RHTower.Mertens.mertensTail)
          * (Real.log (p : ℝ) / Real.log ((N / p : ℕ) : ℝ)) * ((N / p : ℕ) : ℝ) := by
  classical
  set M : ℕ := N / p with hM
  set L : ℝ := Real.log ((M : ℕ) : ℝ) with hL
  have hMR : (2 : ℝ) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast h2
  have hLpos : 0 < L := by
    rw [hL]
    refine Real.log_pos ?_
    linarith
  have hlogp : (0 : ℝ) ≤ Real.log (p : ℝ) := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      exact Real.log_nonneg this
  have hrec := norm_sum_Icc_mul_log_sub_sum_primes_le' hf hbdd M
  set S : ℂ := ∑ k ∈ Finset.Icc 1 M, f k with hS
  set T : ℂ := ∑ q ∈ Finset.Icc 1 M with Nat.Prime q,
      ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (M / q), f k with hT
  have hid : ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * S
      - ((Real.log (p : ℝ) / L : ℝ) : ℂ) * f p * T
      = ((Real.log (p : ℝ) / L : ℝ) : ℂ) * f p * (S * ((L : ℝ) : ℂ) - T) := by
    have hLne : ((L : ℝ) : ℂ) ≠ 0 := by
      simpa using hLpos.ne'
    push_cast
    field_simp
  rw [hid, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.log (p : ℝ) / L)]
  have hstep : ‖S * ((L : ℝ) : ℂ) - T‖ ≤ (9 + RHTower.Mertens.mertensTail) * ((M : ℕ) : ℝ) := by
    rw [hS, hT, hL]
    exact hrec
  calc Real.log (p : ℝ) / L * ‖f p‖ * ‖S * ((L : ℝ) : ℂ) - T‖
      ≤ Real.log (p : ℝ) / L * 1 * ((9 + RHTower.Mertens.mertensTail) * ((M : ℕ) : ℝ)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (hbdd p) (by positivity)) hstep
          (norm_nonneg _) (by positivity)
    _ = (9 + RHTower.Mertens.mertensTail) * (Real.log (p : ℝ) / L) * ((M : ℕ) : ℝ) := by ring

/-- **The second application, summed over the outer primes.**  Over the primes whose complementary scale is
at least `2`, the outer prime average is replaced by the double prime average with the weighted error of the
recursion summed over the primes. -/
theorem norm_sum_primes_sub_double_prime_average_le (hf : ∀ a b : ℕ, f (a * b) = f a * f b)
    (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (N : ℕ) :
    ‖∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ≤ N / p),
          (((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k
            - ((Real.log (p : ℝ) / Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ) * f p
                * ∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
                    ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k)‖
      ≤ (9 + RHTower.Mertens.mertensTail)
          * ∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ≤ N / p),
              (Real.log (p : ℝ) / Real.log ((N / p : ℕ) : ℝ)) * ((N / p : ℕ) : ℝ) := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [Finset.mem_filter] at hp
  refine le_trans (norm_log_mul_partialSum_sub_inner_le hf hbdd hp.2.2) (le_of_eq ?_)
  ring

end RHTower.Sieve
end

noncomputable section
namespace RHTower.Sieve
open Finset

variable {f : ℕ → ℂ}

/-- The weighted error of the second application, against the dyadic quotient-window estimate: the sum of
the outer weights times the inner scales is `N` times an `O(log log N)` quantity. -/
theorem sum_prime_log_div_log_quotient_mul_quotient_le (N : ℕ) (hN : 2 ≤ N) :
    (∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ≤ N / p),
        (Real.log (p : ℝ) / Real.log ((N / p : ℕ) : ℝ)) * ((N / p : ℕ) : ℝ))
      ≤ (N : ℝ)
          * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                / Real.log 2)
              * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ))) := by
  classical
  have hterm : ∀ p ∈ Finset.filter (fun p => Nat.Prime p ∧ 2 ≤ N / p) (Finset.Icc 1 N),
      (Real.log (p : ℝ) / Real.log ((N / p : ℕ) : ℝ)) * ((N / p : ℕ) : ℝ)
        ≤ (N : ℝ) * ((Real.log (p : ℝ) / (p : ℝ)) * (1 / Real.log ((N / p : ℕ) : ℝ))) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, _⟩, _, h2⟩ := hp
    have hpR : (0 : ℝ) < (p : ℝ) := by
      have : 0 < p := by omega
      exact_mod_cast this
    have hMR : (2 : ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast h2
    have hLpos : 0 < Real.log ((N / p : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hlogp : (0 : ℝ) ≤ Real.log (p : ℝ) := by
      have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
      exact Real.log_nonneg this
    have hfl : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) := Nat.cast_div_le
    have hnn : (0 : ℝ) ≤ Real.log (p : ℝ) / Real.log ((N / p : ℕ) : ℝ) := by positivity
    calc (Real.log (p : ℝ) / Real.log ((N / p : ℕ) : ℝ)) * ((N / p : ℕ) : ℝ)
        ≤ (Real.log (p : ℝ) / Real.log ((N / p : ℕ) : ℝ)) * ((N : ℝ) / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hfl hnn
      _ = (N : ℝ) * ((Real.log (p : ℝ) / (p : ℝ)) * (1 / Real.log ((N / p : ℕ) : ℝ))) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (sum_prime_log_div_inv_log_quotient_le N hN)
    (by positivity)

/-- **The second application of the recursion, with the error evaluated.**  Replacing the outer prime
average by the double prime average costs `O(N log log N)`, against a main term of size `N log N`: the
dyadic quotient-window estimate is what makes the saving a whole logarithm up to `log log`. -/
theorem norm_sum_primes_sub_double_prime_average_le_explicit
    (hf : ∀ a b : ℕ, f (a * b) = f a * f b) (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (N : ℕ) (hN : 2 ≤ N) :
    ‖∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ≤ N / p),
          (((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k
            - ((Real.log (p : ℝ) / Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ) * f p
                * ∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
                    ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k)‖
      ≤ (9 + RHTower.Mertens.mertensTail)
          * ((N : ℝ)
              * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                    / Real.log 2)
                  * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))) := by
  refine le_trans (norm_sum_primes_sub_double_prime_average_le hf hbdd N) ?_
  refine mul_le_mul_of_nonneg_left (sum_prime_log_div_log_quotient_mul_quotient_le N hN) ?_
  have h : (0 : ℝ) ≤ RHTower.Mertens.mertensTail := by
    rw [RHTower.Mertens.mertensTail]
    exact tsum_nonneg fun i => by positivity
  linarith

end RHTower.Sieve
end
