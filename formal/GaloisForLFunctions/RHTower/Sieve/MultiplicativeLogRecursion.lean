import GaloisForLFunctions.RHTower.Sieve.DivisorSwap
import GaloisForLFunctions.RHTower.Sieve.MertensFirst
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# From the log-weighted recursion to the primes

Halász's recursion for a completely multiplicative `f`,

`∑_{m ≤ N} f(m) log m = ∑_{d ≤ N} Λ(d) f(d) · S_f(⌊N/d⌋)`,   `S_f(M) = ∑_{m ≤ M} f(m)`,

becomes a statement about the primes alone at a cost of `O(N)`.  Two elementary passages do it:

* replacing the weight `log m` by the constant `log N` costs `∑_{m ≤ N} (log N − log m) = N log N − log N!
  ≤ N`, by Stirling's lower bound;
* the prime-power excess of `Λ` costs `∑_{d ≤ N, d not prime} Λ(d)/d ≤ 8 + mertensTail` against the
  trivial divided size `⌊N/d⌋`, by Abel summation against Chebyshev's `ψ − θ`.

What remains is

`S_f(N)·log N = ∑_{p ≤ N} f(p) log p · S_f(⌊N/p⌋) + O(N)`,

with the values of `f` entering signed, at the primes only, and with no partial sum longer than `⌊N/2⌋`.
-/

noncomputable section

namespace RHTower.Sieve

open ArithmeticFunction Finset

variable {f : ℕ → ℂ}

/-- The partial sums of `log` over `Icc 1 N` are the log-factorial. -/
theorem sum_Icc_log_eq_log_factorial (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) = Real.log ((Nat.factorial N : ℕ) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih, Nat.factorial_succ]
      have hfac : ((Nat.factorial N : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero N
      have hsucc : (((N + 1 : ℕ)) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero N
      rw [Nat.cast_mul, Real.log_mul hsucc hfac]
      ring

/-- **Replacing the weight `log m` by the constant `log N`.**  The cost is
`∑_{m ≤ N} (log N − log m) = N log N − log N! ≤ N`. -/
theorem norm_sum_Icc_mul_log_sub_le (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (N : ℕ) :
    ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
        - ∑ n ∈ Finset.Icc 1 N, f n * ((Real.log (n : ℝ) : ℝ) : ℂ)‖ ≤ (N : ℝ) := by
  have hmono : ∀ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) ≤ Real.log (N : ℝ) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h1 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := hn.1
      exact_mod_cast this
    exact Real.log_le_log h1 (by exact_mod_cast hn.2)
  have hrewrite : (∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
      - ∑ n ∈ Finset.Icc 1 N, f n * ((Real.log (n : ℝ) : ℝ) : ℂ)
      = ∑ n ∈ Finset.Icc 1 N,
          f n * (((Real.log (N : ℝ) - Real.log (n : ℝ) : ℝ) : ℂ)) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.ofReal_sub]
    ring
  rw [hrewrite]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      ‖f n * (((Real.log (N : ℝ) - Real.log (n : ℝ) : ℝ) : ℂ))‖
        ≤ Real.log (N : ℝ) - Real.log (n : ℝ) := by
    intro n hn
    have hd : 0 ≤ Real.log (N : ℝ) - Real.log (n : ℝ) := by linarith [hmono n hn]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
    calc ‖f n‖ * (Real.log (N : ℝ) - Real.log (n : ℝ))
        ≤ 1 * (Real.log (N : ℝ) - Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (hbdd n) hd
      _ = Real.log (N : ℝ) - Real.log (n : ℝ) := one_mul _
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_sub_distrib, Finset.sum_const, sum_Icc_log_eq_log_factorial,
    Nat.card_Icc, nsmul_eq_mul]
  have hcard : ((N + 1 - 1 : ℕ) : ℝ) = (N : ℝ) := by
    simp
  rw [hcard]
  have := le_log_factorial N
  linarith

/-- The trivial size of a partial sum of a bounded function. -/
theorem norm_sum_Icc_le (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (M : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 M, f m‖ ≤ (M : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun m _ => hbdd m) ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  simp

/-- **The prime-power excess is `O(N)` against any weight of the trivial divided size.**  This is the
Abel bound `∑_{d ≤ N, d not prime} Λ(d)/d ≤ 8 + mertensTail` applied termwise. -/
theorem norm_sum_notPrimeVonMangoldt_weight_le {N : ℕ} (w : ℕ → ℂ)
    (hw : ∀ d ∈ Finset.Icc 1 N, ‖w d‖ ≤ ((N / d : ℕ) : ℝ)) :
    ‖∑ d ∈ Finset.Icc 1 N, ((RHTower.Mertens.notPrimeVonMangoldt d : ℝ) : ℂ) * w d‖
      ≤ (8 + RHTower.Mertens.mertensTail) * (N : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  have hstep : ∀ d ∈ Finset.Icc 1 N,
      ‖((RHTower.Mertens.notPrimeVonMangoldt d : ℝ) : ℂ) * w d‖
        ≤ (N : ℝ) * (RHTower.Mertens.notPrimeVonMangoldt d / (d : ℝ)) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.1 hd).1
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hnn : 0 ≤ RHTower.Mertens.notPrimeVonMangoldt d := by
      rw [RHTower.Mertens.notPrimeVonMangoldt]
      by_cases hp : d.Prime
      · simp [hp]
      · simp only [hp, if_false]
        exact vonMangoldt_nonneg
    have h2 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
    have h3 := mul_le_mul_of_nonneg_left ((hw d hd).trans h2) hnn
    have hid : RHTower.Mertens.notPrimeVonMangoldt d * ((N : ℝ) / (d : ℝ))
        = (N : ℝ) * (RHTower.Mertens.notPrimeVonMangoldt d / (d : ℝ)) := by
      field_simp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    linarith [h3, hid.le, hid.ge]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  calc (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, RHTower.Mertens.notPrimeVonMangoldt d / (d : ℝ)
      ≤ (N : ℝ) * (8 + RHTower.Mertens.mertensTail) :=
        mul_le_mul_of_nonneg_left (RHTower.Mertens.tail_bounded N) hN0
    _ = (8 + RHTower.Mertens.mertensTail) * (N : ℝ) := by ring

/-- **The signed prime-only identity.**  In Halász's recursion the composite prime powers contribute
`O(N)` in total, so

`∑_{m ≤ N} f(m) log m = ∑_{p ≤ N} f(p) log p · S_f(⌊N/p⌋) + O(N)`.

The values of `f` enter signed: all cancellation among them is preserved. -/
theorem norm_sum_Icc_mul_log_sub_sum_primes_le (hf : ∀ a b : ℕ, f (a * b) = f a * f b)
    (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (N : ℕ) :
    ‖(∑ n ∈ Finset.Icc 1 N, f n * ((Real.log (n : ℝ) : ℝ) : ℂ))
        - ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
            ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k‖
      ≤ (8 + RHTower.Mertens.mertensTail) * (N : ℝ) := by
  classical
  have hrec := sum_mul_log_eq_vonMangoldt hf N
  have hsplit : ∑ d ∈ Finset.Icc 1 N,
        ((Λ d : ℝ) : ℂ) * f d * ∑ k ∈ Finset.Icc 1 (N / d), f k
      = (∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
            ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k)
        + ∑ d ∈ Finset.Icc 1 N, ((RHTower.Mertens.notPrimeVonMangoldt d : ℝ) : ℂ) *
            (f d * ∑ k ∈ Finset.Icc 1 (N / d), f k) := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [RHTower.Mertens.notPrimeVonMangoldt]
    by_cases hp : d.Prime
    · rw [if_pos hp, if_pos hp, vonMangoldt_apply_prime hp]
      push_cast
      ring
    · rw [if_neg hp, if_neg hp]
      ring
  have htail : ‖∑ d ∈ Finset.Icc 1 N, ((RHTower.Mertens.notPrimeVonMangoldt d : ℝ) : ℂ) *
      (f d * ∑ k ∈ Finset.Icc 1 (N / d), f k)‖
      ≤ (8 + RHTower.Mertens.mertensTail) * (N : ℝ) := by
    refine norm_sum_notPrimeVonMangoldt_weight_le _ fun d _ => ?_
    rw [norm_mul]
    calc ‖f d‖ * ‖∑ k ∈ Finset.Icc 1 (N / d), f k‖
        ≤ 1 * ((N / d : ℕ) : ℝ) :=
          mul_le_mul (hbdd d) (norm_sum_Icc_le hbdd _) (norm_nonneg _) zero_le_one
      _ = ((N / d : ℕ) : ℝ) := one_mul _
  rw [hrec, hsplit, add_sub_cancel_left]
  exact htail

/-- **The entry point of the Halász method.**  For a bounded completely multiplicative `f`,

`S_f(N) log N = ∑_{p ≤ N} f(p) log p · S_f(⌊N/p⌋) + O(N)`,

with the explicit constant `9 + mertensTail`.  Every ingredient is elementary: the divisor swap,
`∑_{d ∣ m} Λ(d) = log m`, Stirling's lower bound for `log N!`, and Chebyshev's `ψ − θ`.  Decay of `S_f`
is therefore equivalent to cancellation in the prime sum on the right — and no Dirichlet polynomial of
length `N` and no mean-value theorem at a short height occurs anywhere in the statement. -/
theorem norm_sum_Icc_mul_log_sub_sum_primes_le' (hf : ∀ a b : ℕ, f (a * b) = f a * f b)
    (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (N : ℕ) :
    ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
        - ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
            ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k‖
      ≤ (9 + RHTower.Mertens.mertensTail) * (N : ℝ) := by
  classical
  have h1 := norm_sum_Icc_mul_log_sub_le hbdd N
  have h2 := norm_sum_Icc_mul_log_sub_sum_primes_le hf hbdd N
  have hid : (∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
        - ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
            ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k
      = ((∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
            - ∑ n ∈ Finset.Icc 1 N, f n * ((Real.log (n : ℝ) : ℝ) : ℂ))
        + ((∑ n ∈ Finset.Icc 1 N, f n * ((Real.log (n : ℝ) : ℝ) : ℂ))
            - ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
                ((Real.log (p : ℝ) : ℝ) : ℂ) * f p * ∑ k ∈ Finset.Icc 1 (N / p), f k) := by
    ring
  rw [hid]
  refine le_trans (norm_add_le _ _) ?_
  have hexp : (9 + RHTower.Mertens.mertensTail) * (N : ℝ)
      = (N : ℝ) + (8 + RHTower.Mertens.mertensTail) * (N : ℝ) := by ring
  rw [hexp]
  linarith

end RHTower.Sieve

end
