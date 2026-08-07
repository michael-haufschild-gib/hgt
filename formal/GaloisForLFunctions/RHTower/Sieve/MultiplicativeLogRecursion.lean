import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import GaloisForLFunctions.RHTower.Sieve.MertensFirst
import GaloisForLFunctions.RHTower.MertensFirst
import GaloisForLFunctions.HTGeometry.GeneralisedVonMangoldt

/-!
# The log-weighted recursion for a multiplicative partial sum

For a completely multiplicative `f` the identity `f·log = f * (f·Λ)` and the finite hyperbola swap turn
the log-weighted partial sum into a `Λ`-average of the partial sums of `f` itself:

`∑_{n ≤ N} f(n) log n = ∑_{d ≤ N} f(d) Λ(d) · S_f(⌊N/d⌋)`,   `S_f(M) = ∑_{m ≤ M} f(m)`.

Replacing `log n` by `log N` costs `N log N − log N! ≤ N`, and the prime-power excess of `Λ` contributes
`O(N)` because `∑_{d ≤ N, d not prime} Λ(d)/d` is bounded.  What remains is the prime sum:

`S_f(N)·log N = ∑_{p ≤ N} f(p) log p · S_f(⌊N/p⌋) + O(N)`.

No Dirichlet polynomial and no mean-value theorem at a short height occur: only partial sums at the
*divided* scales `⌊N/p⌋` appear, and the values of `f` enter signed, at the primes only.
-/

noncomputable section

namespace RHTower.Sieve

open ArithmeticFunction Finset GaloisForLFunctions.HTGeometry

variable {f : ArithmeticFunction ℝ}

/-- **The log-weighted recursion.**  The convolution identity `f·log = f * (f·Λ)` of a completely
multiplicative function, fed through the finite hyperbola swap. -/
theorem sum_Icc_mul_log_eq (hf : ∀ m n : ℕ, f (m * n) = f m * f n) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n * Real.log (n : ℝ)
      = ∑ d ∈ Finset.Icc 1 N, f d * Λ d * ∑ m ∈ Finset.Icc 1 (N / d), f m := by
  have hpm : ∀ n : ℕ, (pmul f ArithmeticFunction.log) n = f n * Real.log (n : ℝ) := by
    intro n
    rw [pmul_apply, ArithmeticFunction.log_apply]
  have hstep : ∑ n ∈ Finset.Icc 1 N, f n * Real.log (n : ℝ)
      = ∑ n ∈ Finset.Icc 1 N, (pmul f Λ * f) n := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← hpm n, pmul_log_eq_mul_pmul_vonMangoldt f hf, mul_comm f (pmul f Λ)]
  rw [hstep, RHTower.sum_Icc_mul_apply]
  exact Finset.sum_congr rfl fun d _ => by rw [pmul_apply]

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

/-- **Replacing the weight `log n` by the constant `log N`.**  The cost is
`∑_{n ≤ N} (log N − log n) = N log N − log N! ≤ N`. -/
theorem abs_sum_Icc_mul_log_sub_le (hbdd : ∀ n : ℕ, |f n| ≤ 1) (N : ℕ) :
    |(∑ n ∈ Finset.Icc 1 N, f n) * Real.log (N : ℝ)
        - ∑ n ∈ Finset.Icc 1 N, f n * Real.log (n : ℝ)| ≤ (N : ℝ) := by
  have hmono : ∀ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) ≤ Real.log (N : ℝ) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h1 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := hn.1
      exact_mod_cast this
    exact Real.log_le_log h1 (by exact_mod_cast hn.2)
  have hrewrite : (∑ n ∈ Finset.Icc 1 N, f n) * Real.log (N : ℝ)
      - ∑ n ∈ Finset.Icc 1 N, f n * Real.log (n : ℝ)
      = ∑ n ∈ Finset.Icc 1 N, f n * (Real.log (N : ℝ) - Real.log (n : ℝ)) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hrewrite]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      |f n * (Real.log (N : ℝ) - Real.log (n : ℝ))| ≤ Real.log (N : ℝ) - Real.log (n : ℝ) := by
    intro n hn
    have hd : 0 ≤ Real.log (N : ℝ) - Real.log (n : ℝ) := by linarith [hmono n hn]
    rw [abs_mul, abs_of_nonneg hd]
    calc |f n| * (Real.log (N : ℝ) - Real.log (n : ℝ))
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
theorem abs_sum_Icc_le (hbdd : ∀ n : ℕ, |f n| ≤ 1) (M : ℕ) :
    |∑ m ∈ Finset.Icc 1 M, f m| ≤ (M : ℝ) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun m _ => hbdd m) ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  simp

/-- **The self-referential estimate.**  The partial sum of a bounded completely multiplicative function
at `N` is controlled by the von Mangoldt average of the partial sums at the divided scales. -/
theorem abs_sum_Icc_mul_log_le (hf : ∀ m n : ℕ, f (m * n) = f m * f n) (hbdd : ∀ n : ℕ, |f n| ≤ 1)
    (N : ℕ) :
    |∑ n ∈ Finset.Icc 1 N, f n| * Real.log (N : ℝ)
      ≤ (N : ℝ) + ∑ d ∈ Finset.Icc 1 N, Λ d * |∑ m ∈ Finset.Icc 1 (N / d), f m| := by
  have hrec : |∑ n ∈ Finset.Icc 1 N, f n * Real.log (n : ℝ)|
      ≤ ∑ d ∈ Finset.Icc 1 N, Λ d * |∑ m ∈ Finset.Icc 1 (N / d), f m| := by
    rw [sum_Icc_mul_log_eq hf N]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun d _ => ?_)
    rw [abs_mul, abs_mul]
    have h0 : (0 : ℝ) ≤ Λ d := vonMangoldt_nonneg
    have h1 : |f d| * |Λ d| ≤ Λ d := by
      rw [abs_of_nonneg h0]
      nlinarith [hbdd d, abs_nonneg (f d)]
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hshift := abs_sum_Icc_mul_log_sub_le hbdd N
  have hsplit : |(∑ n ∈ Finset.Icc 1 N, f n) * Real.log (N : ℝ)|
      ≤ |(∑ n ∈ Finset.Icc 1 N, f n) * Real.log (N : ℝ)
            - ∑ n ∈ Finset.Icc 1 N, f n * Real.log (n : ℝ)|
        + |∑ n ∈ Finset.Icc 1 N, f n * Real.log (n : ℝ)| := by
    have := abs_add_le ((∑ n ∈ Finset.Icc 1 N, f n) * Real.log (N : ℝ)
        - ∑ n ∈ Finset.Icc 1 N, f n * Real.log (n : ℝ))
      (∑ n ∈ Finset.Icc 1 N, f n * Real.log (n : ℝ))
    rwa [sub_add_cancel] at this
  have hprod : |∑ n ∈ Finset.Icc 1 N, f n| * |Real.log (N : ℝ)|
      = |(∑ n ∈ Finset.Icc 1 N, f n) * Real.log (N : ℝ)| := (abs_mul _ _).symm
  rcases Nat.lt_or_ge N 1 with hN | hN
  · interval_cases N
    · simp
  · have hlog0 : (0 : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    have habs : |Real.log (N : ℝ)| = Real.log (N : ℝ) := abs_of_nonneg hlog0
    rw [← habs, hprod]
    linarith

/-- **The prime-power excess is `O(N)` against any weight of the trivial divided size.**  This is the
Abel bound `∑_{d ≤ N, d not prime} Λ(d)/d ≤ 8 + mertensTail` applied termwise. -/
theorem abs_sum_notPrimeVonMangoldt_weight_le {N : ℕ} (w : ℕ → ℝ)
    (hw : ∀ d ∈ Finset.Icc 1 N, |w d| ≤ ((N / d : ℕ) : ℝ)) :
    |∑ d ∈ Finset.Icc 1 N, RHTower.Mertens.notPrimeVonMangoldt d * w d|
      ≤ (8 + RHTower.Mertens.mertensTail) * (N : ℝ) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hstep : ∀ d ∈ Finset.Icc 1 N,
      |RHTower.Mertens.notPrimeVonMangoldt d * w d|
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
    rw [abs_mul, abs_of_nonneg hnn]
    linarith [h3, hid.le, hid.ge]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  calc (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, RHTower.Mertens.notPrimeVonMangoldt d / (d : ℝ)
      ≤ (N : ℝ) * (8 + RHTower.Mertens.mertensTail) :=
        mul_le_mul_of_nonneg_left (RHTower.Mertens.tail_bounded N) hN0
    _ = (8 + RHTower.Mertens.mertensTail) * (N : ℝ) := by ring

/-- **The prime-only recursion.**  The prime-power excess of the von Mangoldt weight contributes `O(N)`
in total, so the log-weighted partial sum is governed by the primes alone. -/
theorem abs_sum_Icc_mul_log_le_primes (hf : ∀ m n : ℕ, f (m * n) = f m * f n)
    (hbdd : ∀ n : ℕ, |f n| ≤ 1) (N : ℕ) :
    |∑ n ∈ Finset.Icc 1 N, f n| * Real.log (N : ℝ)
      ≤ (9 + RHTower.Mertens.mertensTail) * (N : ℝ)
        + ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
            Real.log (p : ℝ) * |∑ m ∈ Finset.Icc 1 (N / p), f m| := by
  classical
  have hbase := abs_sum_Icc_mul_log_le hf hbdd N
  have hsplit : ∑ d ∈ Finset.Icc 1 N, Λ d * |∑ m ∈ Finset.Icc 1 (N / d), f m|
      = (∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
            Real.log (p : ℝ) * |∑ m ∈ Finset.Icc 1 (N / p), f m|)
        + ∑ d ∈ Finset.Icc 1 N,
            RHTower.Mertens.notPrimeVonMangoldt d * |∑ m ∈ Finset.Icc 1 (N / d), f m| := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [RHTower.Mertens.notPrimeVonMangoldt]
    by_cases hp : d.Prime
    · simp [hp, vonMangoldt_apply_prime hp]
    · simp [hp]
  have htail : ∑ d ∈ Finset.Icc 1 N,
        RHTower.Mertens.notPrimeVonMangoldt d * |∑ m ∈ Finset.Icc 1 (N / d), f m|
      ≤ (8 + RHTower.Mertens.mertensTail) * (N : ℝ) := by
    have hnonneg : |(∑ d ∈ Finset.Icc 1 N,
        RHTower.Mertens.notPrimeVonMangoldt d * |∑ m ∈ Finset.Icc 1 (N / d), f m|)|
        = ∑ d ∈ Finset.Icc 1 N,
            RHTower.Mertens.notPrimeVonMangoldt d * |∑ m ∈ Finset.Icc 1 (N / d), f m| := by
      refine abs_of_nonneg (Finset.sum_nonneg fun d _ => ?_)
      have hnn : 0 ≤ RHTower.Mertens.notPrimeVonMangoldt d := by
        rw [RHTower.Mertens.notPrimeVonMangoldt]
        by_cases hp : d.Prime
        · simp [hp]
        · simp only [hp, if_false]
          exact vonMangoldt_nonneg
      exact mul_nonneg hnn (abs_nonneg _)
    rw [← hnonneg]
    refine abs_sum_notPrimeVonMangoldt_weight_le _ fun d _ => ?_
    rw [abs_abs]
    exact abs_sum_Icc_le hbdd _
  have hid : (9 + RHTower.Mertens.mertensTail) * (N : ℝ)
      = (N : ℝ) + (8 + RHTower.Mertens.mertensTail) * (N : ℝ) := by ring
  rw [hsplit] at hbase
  linarith

/-- **The signed prime-only identity.**  The log-weighted partial sum of a bounded completely
multiplicative function is its prime-weighted average of divided partial sums, up to `O(N)`:

`∑_{n ≤ N} f(n) log n = ∑_{p ≤ N} f(p) log p · S_f(⌊N/p⌋) + O(N)`.

Unlike the absolute-value form this keeps all cancellation among the values `f(p)`, which is where any
decay of `S_f` must come from. -/
theorem abs_sum_Icc_mul_log_sub_sum_primes_le (hf : ∀ m n : ℕ, f (m * n) = f m * f n)
    (hbdd : ∀ n : ℕ, |f n| ≤ 1) (N : ℕ) :
    |(∑ n ∈ Finset.Icc 1 N, f n * Real.log (n : ℝ))
        - ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
            f p * Real.log (p : ℝ) * ∑ m ∈ Finset.Icc 1 (N / p), f m|
      ≤ (8 + RHTower.Mertens.mertensTail) * (N : ℝ) := by
  classical
  have hrec := sum_Icc_mul_log_eq hf N
  have hsplit : ∑ d ∈ Finset.Icc 1 N, f d * Λ d * ∑ m ∈ Finset.Icc 1 (N / d), f m
      = (∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
            f p * Real.log (p : ℝ) * ∑ m ∈ Finset.Icc 1 (N / p), f m)
        + ∑ d ∈ Finset.Icc 1 N, RHTower.Mertens.notPrimeVonMangoldt d *
            (f d * ∑ m ∈ Finset.Icc 1 (N / d), f m) := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [RHTower.Mertens.notPrimeVonMangoldt]
    by_cases hp : d.Prime
    · rw [if_pos hp, if_pos hp, vonMangoldt_apply_prime hp]
      ring
    · rw [if_neg hp, if_neg hp]
      ring
  have htail : |∑ d ∈ Finset.Icc 1 N, RHTower.Mertens.notPrimeVonMangoldt d *
      (f d * ∑ m ∈ Finset.Icc 1 (N / d), f m)|
      ≤ (8 + RHTower.Mertens.mertensTail) * (N : ℝ) := by
    refine abs_sum_notPrimeVonMangoldt_weight_le _ fun d _ => ?_
    rw [abs_mul]
    calc |f d| * |∑ m ∈ Finset.Icc 1 (N / d), f m|
        ≤ 1 * ((N / d : ℕ) : ℝ) :=
          mul_le_mul (hbdd d) (abs_sum_Icc_le hbdd _) (abs_nonneg _) zero_le_one
      _ = ((N / d : ℕ) : ℝ) := one_mul _
  rw [hrec, hsplit, add_sub_cancel_left]
  exact htail

/-- **The entry point of the Halász method.**  For a bounded completely multiplicative `f`,

`S_f(N) log N = ∑_{p ≤ N} f(p) log p · S_f(⌊N/p⌋) + O(N)`,

with the explicit constant `9 + mertensTail`.  Every ingredient is unconditional and elementary: the
convolution identity `f·log = f * (f·Λ)`, the hyperbola swap, Stirling's lower bound for `log N!`, and
the Abel bound for the prime-power excess.  Decay of `S_f` is therefore equivalent to cancellation in the
prime sum on the right. -/
theorem abs_sum_Icc_mul_log_sub_sum_primes_le' (hf : ∀ m n : ℕ, f (m * n) = f m * f n)
    (hbdd : ∀ n : ℕ, |f n| ≤ 1) (N : ℕ) :
    |(∑ n ∈ Finset.Icc 1 N, f n) * Real.log (N : ℝ)
        - ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
            f p * Real.log (p : ℝ) * ∑ m ∈ Finset.Icc 1 (N / p), f m|
      ≤ (9 + RHTower.Mertens.mertensTail) * (N : ℝ) := by
  classical
  have h1 := abs_sum_Icc_mul_log_sub_le hbdd N
  have h2 := abs_sum_Icc_mul_log_sub_sum_primes_le hf hbdd N
  have hid : (∑ n ∈ Finset.Icc 1 N, f n) * Real.log (N : ℝ)
        - ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
            f p * Real.log (p : ℝ) * ∑ m ∈ Finset.Icc 1 (N / p), f m
      = ((∑ n ∈ Finset.Icc 1 N, f n) * Real.log (N : ℝ)
            - ∑ n ∈ Finset.Icc 1 N, f n * Real.log (n : ℝ))
        + ((∑ n ∈ Finset.Icc 1 N, f n * Real.log (n : ℝ))
            - ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
                f p * Real.log (p : ℝ) * ∑ m ∈ Finset.Icc 1 (N / p), f m) := by
    ring
  rw [hid]
  refine le_trans (abs_add_le _ _) ?_
  have hexp : (9 + RHTower.Mertens.mertensTail) * (N : ℝ)
      = (N : ℝ) + (8 + RHTower.Mertens.mertensTail) * (N : ℝ) := by ring
  rw [hexp]
  linarith

/-- **The Möbius instance of the recursion.**  The same hyperbola swap, applied to the weight of the
Möbius function `Λ_μ = −Λ`, is the classical identity

`∑_{n ≤ N} μ(n) log n = −∑_{d ≤ N} Λ(d)·M(⌊N/d⌋)`,   `M(K) = ∑_{m ≤ K} μ(m)`.

No hypotheses: the Möbius function is not completely multiplicative, so this is an instance of the
general weight `Λ_f = f⁻¹ * (f·log)`, not of the completely multiplicative specialisation. -/
theorem sum_Icc_moebius_mul_log_eq (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (n : ℝ)
      = -∑ d ∈ Finset.Icc 1 N,
          Λ d * ∑ m ∈ Finset.Icc 1 (N / d), ((ArithmeticFunction.moebius m : ℤ) : ℝ) := by
  have hstep : ∑ n ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (n : ℝ)
      = ∑ n ∈ Finset.Icc 1 N,
          ((-Λ) * ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
            ArithmeticFunction ℝ)) n := by
    refine Finset.sum_congr rfl fun n _ => ?_
    have h : (pmul ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
          ArithmeticFunction.log) n
        = ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (n : ℝ) := by
      rw [pmul_apply, intCoe_apply, ArithmeticFunction.log_apply]
    rw [← h, pmul_moebius_log, mul_comm]
  rw [hstep, RHTower.sum_Icc_mul_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [ArithmeticFunction.neg_apply, intCoe_apply]
  ring

end RHTower.Sieve

end
