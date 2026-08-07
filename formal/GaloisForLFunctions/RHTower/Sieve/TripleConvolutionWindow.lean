import GaloisForLFunctions.RHTower.Sieve.PrimeLogQuotientSum
import GaloisForLFunctions.RHTower.Sieve.MultiplicativePrimeAverage

/-!
# One dyadic window of the triple convolution

The double prime average of the recursion is a sum over primes `p` of a weight `log p/log⌊N/p⌋` against
the inner double sum `∑_{q ≤ ⌊N/p⌋} f(q) log q · S_f(⌊N/p/q⌋)`.  Restricted to a window of dyadic
quotient sizes `2^m ≤ ⌊N/p⌋ < 2^n`, the whole contribution admits the trivial bound

`≪ N · ((n − m) + 1)`,

because the inner double sum is at most `⌊N/p⌋(log⌊N/p⌋ + O(1))` — Mertens' first theorem against the
trivial size of `S_f` — while the outer weight against `⌊N/p⌋ ≤ N/p` is the window's Mertens mass.

With `m = 2^i` and `n = 2^{i+1}` this is `O(2^i N)`: the geometric decay in the block index that
Granville–Harper–Soundararajan use to discard all blocks beyond the analytic range.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

variable {f : ℕ → ℂ}

/-- The inner double sum of the triple convolution, at its trivial size. -/
theorem norm_inner_double_le (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) {M : ℕ} (hM : 1 ≤ M) :
    ‖∑ q ∈ Finset.Icc 1 M with Nat.Prime q,
        ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (M / q), f k‖
      ≤ (M : ℝ) * (Real.log (M : ℝ) + ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail))) := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ q ∈ Finset.filter Nat.Prime (Finset.Icc 1 M),
      ‖((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (M / q), f k‖
        ≤ (M : ℝ) * (Real.log (q : ℝ) / (q : ℝ)) := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq1, hqM⟩, hqprime⟩ := hq
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq1)
    have hin : ‖∑ k ∈ Finset.Icc 1 (M / q), f k‖ ≤ ((M / q : ℕ) : ℝ) :=
      norm_sum_Icc_le hbdd _
    have hcast : ((M / q : ℕ) : ℝ) ≤ (M : ℝ) / (q : ℝ) := Nat.cast_div_le
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogq]
    calc Real.log (q : ℝ) * ‖f q‖ * ‖∑ k ∈ Finset.Icc 1 (M / q), f k‖
        ≤ Real.log (q : ℝ) * 1 * ((M : ℝ) / (q : ℝ)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (hbdd q) hlogq) (hin.trans hcast)
            (norm_nonneg _) (by positivity)
      _ = (M : ℝ) * (Real.log (q : ℝ) / (q : ℝ)) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hmert := RHTower.Mertens.mertens_first_prime M hM
  rw [abs_le] at hmert
  exact mul_le_mul_of_nonneg_left (by linarith [hmert.2]) hMnn


/-- **The trivial bound for one dyadic window of the triple convolution.**  On the window
`2^m ≤ ⌊N/p⌋ < 2^n` the inner double sum is at its trivial size and the outer weight is the window's
Mertens mass, so the whole contribution is `O(N·(n − m + 1))` — geometric in the block index when
`m = 2^i`, `n = 2^{i+1}`. -/
theorem norm_window_triple_le (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (N : ℕ) {m n : ℕ} (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    ‖∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ^ m ≤ N / p ∧ N / p < 2 ^ n),
        ((Real.log (p : ℝ) : ℝ) : ℂ) * f p
          * ((∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
                ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k)
              / ((Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ))‖
      ≤ (1 + ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)) / Real.log 2) * (N : ℝ)
          * (((n : ℝ) - (m : ℝ) + 1) * Real.log 2
              + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail))) := by
  classical
  set C : ℝ := (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail) with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    have h1 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h2 : (0:ℝ) ≤ RHTower.Mertens.mertensTail := by
      rw [RHTower.Mertens.mertensTail]
      exact tsum_nonneg fun i => by positivity
    linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hK : (0:ℝ) ≤ 1 + C / Real.log 2 := by positivity
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ Finset.filter (fun p => Nat.Prime p ∧ 2 ^ m ≤ N / p ∧ N / p < 2 ^ n)
      (Finset.Icc 1 N),
      ‖((Real.log (p : ℝ) : ℝ) : ℂ) * f p
          * ((∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
                ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k)
              / ((Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ))‖
        ≤ (1 + C / Real.log 2) * (N : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hpN⟩, hpprime, hwlow, hwhigh⟩ := hp
    have hp0 : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp1
    have hlogp : (0:ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp1)
    have h2m : (2:ℕ) ≤ 2 ^ m := by
      calc (2:ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hM2 : 2 ≤ N / p := le_trans h2m hwlow
    have hM1 : 1 ≤ N / p := by omega
    have hMR : (2:ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast hM2
    have hlogM : Real.log 2 ≤ Real.log ((N / p : ℕ) : ℝ) := Real.log_le_log (by norm_num) hMR
    have hlogMpos : (0:ℝ) < Real.log ((N / p : ℕ) : ℝ) := lt_of_lt_of_le hlog2 hlogM
    have hinner := norm_inner_double_le hbdd hM1
    rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogp, abs_of_pos hlogMpos]
    have hstep1 : ‖f p‖ * (‖∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
          ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k‖
            / Real.log ((N / p : ℕ) : ℝ))
        ≤ ((N / p : ℕ) : ℝ) * (1 + C / Real.log 2) := by
      have hnum : ‖∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
            ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k‖
              / Real.log ((N / p : ℕ) : ℝ)
          ≤ ((N / p : ℕ) : ℝ) * (1 + C / Real.log 2) := by
        rw [div_le_iff₀ hlogMpos]
        refine le_trans hinner ?_
        have hexpand : ((N / p : ℕ) : ℝ) * (1 + C / Real.log 2) * Real.log ((N / p : ℕ) : ℝ)
            = ((N / p : ℕ) : ℝ) * (Real.log ((N / p : ℕ) : ℝ)
                + (C / Real.log 2) * Real.log ((N / p : ℕ) : ℝ)) := by ring
        rw [hexpand]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have hCle : C ≤ (C / Real.log 2) * Real.log ((N / p : ℕ) : ℝ) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
          exact mul_le_mul_of_nonneg_left hlogM hCnn
        linarith
      calc ‖f p‖ * (‖∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
            ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k‖
              / Real.log ((N / p : ℕ) : ℝ))
          ≤ 1 * (((N / p : ℕ) : ℝ) * (1 + C / Real.log 2)) := by
            refine mul_le_mul (hbdd p) hnum (by positivity) zero_le_one
        _ = ((N / p : ℕ) : ℝ) * (1 + C / Real.log 2) := one_mul _
    have hcast : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) := Nat.cast_div_le
    calc Real.log (p : ℝ) * ‖f p‖
          * (‖∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
                ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k‖
              / Real.log ((N / p : ℕ) : ℝ))
        = Real.log (p : ℝ) * (‖f p‖
            * (‖∑ q ∈ Finset.Icc 1 (N / p) with Nat.Prime q,
                  ((Real.log (q : ℝ) : ℝ) : ℂ) * f q * ∑ k ∈ Finset.Icc 1 (N / p / q), f k‖
                / Real.log ((N / p : ℕ) : ℝ))) := by ring
      _ ≤ Real.log (p : ℝ) * (((N / p : ℕ) : ℝ) * (1 + C / Real.log 2)) :=
          mul_le_mul_of_nonneg_left hstep1 hlogp
      _ ≤ Real.log (p : ℝ) * (((N : ℝ) / (p : ℝ)) * (1 + C / Real.log 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hlogp
          exact mul_le_mul_of_nonneg_right hcast hK
      _ = (1 + C / Real.log 2) * (N : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact sum_quotient_window_prime_log_div_le N m n hmn

end RHTower.Sieve
end
