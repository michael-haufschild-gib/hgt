import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import GaloisForLFunctions.RHTower.Sieve.MertensFirst
import GaloisForLFunctions.RHTower.MertensFirst
import GaloisForLFunctions.HTGeometry.GeneralisedVonMangoldt

/-!
# The log-weighted recursion for a multiplicative partial sum

The identity `f·log = f * Λ_f` and the finite hyperbola swap turn the log-weighted partial sum of a
multiplicative function into a `Λ_f`-average of its own partial sums:

`∑_{n ≤ N} f(n) log n = ∑_{d ≤ N} Λ_f(d) · S_f(⌊N/d⌋)`,   `S_f(M) = ∑_{m ≤ M} f(m)`.

Replacing `log n` by `log N` costs `N log N − log N!  ≤ N`, so for a bounded completely multiplicative
`f`, where `|Λ_f| ≤ Λ`, one gets the self-referential inequality

`|S_f(N)| · log N ≤ N + ∑_{d ≤ N} Λ(d) · |S_f(⌊N/d⌋)|`.

No Dirichlet polynomial and no mean-value theorem at a short height occur: the estimate is a statement
about partial sums at the *divided* scales `N/d` only, which is why it is not subject to the length
obstruction of the contour route.
-/

noncomputable section

namespace RHTower.Sieve

open ArithmeticFunction Finset GaloisForLFunctions.HTGeometry

/-- **The log-weighted recursion.**  The defining identity of the generalised von Mangoldt function
fed through the finite hyperbola swap. -/
theorem sum_Icc_mul_log_eq (f : ArithmeticFunction ℝ) (hf : Invertible (f 1)) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n * Real.log (n : ℝ)
      = ∑ d ∈ Finset.Icc 1 N, vonMangoldtOf f hf d * ∑ m ∈ Finset.Icc 1 (N / d), f m := by
  have hpm : ∀ n : ℕ, (pmul f ArithmeticFunction.log) n = f n * Real.log (n : ℝ) := by
    intro n
    rw [pmul_apply, ArithmeticFunction.log_apply]
  have hstep : ∑ n ∈ Finset.Icc 1 N, f n * Real.log (n : ℝ)
      = ∑ n ∈ Finset.Icc 1 N, (vonMangoldtOf f hf * f) n := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← hpm n, pmul_log_eq_mul_vonMangoldtOf f hf, mul_comm f (vonMangoldtOf f hf)]
  rw [hstep, RHTower.sum_Icc_mul_apply]

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
theorem abs_sum_Icc_mul_log_sub_le (f : ArithmeticFunction ℝ) (hbdd : ∀ n : ℕ, |f n| ≤ 1) (N : ℕ) :
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

/-- **The self-referential estimate.**  For a bounded completely multiplicative `f` the partial sum at
`N` is controlled by the von Mangoldt average of the partial sums at the divided scales. -/
theorem abs_sum_Icc_mul_log_le (f : ArithmeticFunction ℝ) (hf1 : Invertible (f 1))
    (hf : ∀ m n : ℕ, f (m * n) = f m * f n) (hbdd : ∀ n : ℕ, |f n| ≤ 1) (N : ℕ) :
    |∑ n ∈ Finset.Icc 1 N, f n| * Real.log (N : ℝ)
      ≤ (N : ℝ) + ∑ d ∈ Finset.Icc 1 N, Λ d * |∑ m ∈ Finset.Icc 1 (N / d), f m| := by
  have hrec : |∑ n ∈ Finset.Icc 1 N, f n * Real.log (n : ℝ)|
      ≤ ∑ d ∈ Finset.Icc 1 N, Λ d * |∑ m ∈ Finset.Icc 1 (N / d), f m| := by
    rw [sum_Icc_mul_log_eq f hf1 N]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun d _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right
      (abs_vonMangoldtOf_le_vonMangoldt f hf1 hf hbdd d) (abs_nonneg _)
  have hshift := abs_sum_Icc_mul_log_sub_le f hbdd N
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

/-- The trivial size of a partial sum of a bounded function. -/
theorem abs_sum_Icc_le (f : ArithmeticFunction ℝ) (hbdd : ∀ n : ℕ, |f n| ≤ 1) (M : ℕ) :
    |∑ m ∈ Finset.Icc 1 M, f m| ≤ (M : ℝ) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun m _ => hbdd m) ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  simp

/-- **The prime-only recursion.**  The prime-power excess of the von Mangoldt weight contributes
`O(N)` in total, because `∑_{d ≤ N, d not prime} Λ(d)/d` is bounded.  So the log-weighted partial sum
of a bounded completely multiplicative function is governed by the primes alone. -/
theorem abs_sum_Icc_mul_log_le_primes (f : ArithmeticFunction ℝ) (hf1 : Invertible (f 1))
    (hf : ∀ m n : ℕ, f (m * n) = f m * f n) (hbdd : ∀ n : ℕ, |f n| ≤ 1) (N : ℕ) :
    |∑ n ∈ Finset.Icc 1 N, f n| * Real.log (N : ℝ)
      ≤ (9 + RHTower.Mertens.mertensTail) * (N : ℝ)
        + ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
            Real.log (p : ℝ) * |∑ m ∈ Finset.Icc 1 (N / p), f m| := by
  classical
  have hbase := abs_sum_Icc_mul_log_le f hf1 hf hbdd N
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
    have hstep : ∀ d ∈ Finset.Icc 1 N,
        RHTower.Mertens.notPrimeVonMangoldt d * |∑ m ∈ Finset.Icc 1 (N / d), f m|
          ≤ (N : ℝ) * (RHTower.Mertens.notPrimeVonMangoldt d / (d : ℝ)) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hd0 : (0 : ℝ) < (d : ℝ) := by
        have : 0 < d := hd.1
        exact_mod_cast this
      have hnn : 0 ≤ RHTower.Mertens.notPrimeVonMangoldt d := by
        rw [RHTower.Mertens.notPrimeVonMangoldt]
        by_cases hp : d.Prime
        · simp [hp]
        · simp only [hp, if_false]
          exact vonMangoldt_nonneg
      have h1 : |∑ m ∈ Finset.Icc 1 (N / d), f m| ≤ ((N / d : ℕ) : ℝ) :=
        abs_sum_Icc_le f hbdd _
      have h2 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
      have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hnn
      have hid : RHTower.Mertens.notPrimeVonMangoldt d * ((N : ℝ) / (d : ℝ))
          = (N : ℝ) * (RHTower.Mertens.notPrimeVonMangoldt d / (d : ℝ)) := by
        field_simp
      linarith [h3, hid.le, hid.ge]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hbnd := RHTower.Mertens.tail_bounded N
    calc (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, RHTower.Mertens.notPrimeVonMangoldt d / (d : ℝ)
        ≤ (N : ℝ) * (8 + RHTower.Mertens.mertensTail) :=
          mul_le_mul_of_nonneg_left hbnd hN0
      _ = (8 + RHTower.Mertens.mertensTail) * (N : ℝ) := by ring
  have hid : (9 + RHTower.Mertens.mertensTail) * (N : ℝ)
      = (N : ℝ) + (8 + RHTower.Mertens.mertensTail) * (N : ℝ) := by ring
  rw [hsplit] at hbase
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

/-- **The signed prime-only identity.**  The log-weighted partial sum of a bounded completely
multiplicative function is its prime-weighted average of divided partial sums, up to `O(N)`:

`∑_{n ≤ N} f(n) log n = ∑_{p ≤ N} f(p) log p · S_f(⌊N/p⌋) + O(N)`.

Unlike the absolute-value form this keeps all cancellation among the values `f(p)`, which is where any
decay of `S_f` must come from. -/
theorem abs_sum_Icc_mul_log_sub_sum_primes_le (f : ArithmeticFunction ℝ) (hf1 : Invertible (f 1))
    (hf : ∀ m n : ℕ, f (m * n) = f m * f n) (hbdd : ∀ n : ℕ, |f n| ≤ 1) (N : ℕ) :
    |(∑ n ∈ Finset.Icc 1 N, f n * Real.log (n : ℝ))
        - ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
            f p * Real.log (p : ℝ) * ∑ m ∈ Finset.Icc 1 (N / p), f m|
      ≤ (8 + RHTower.Mertens.mertensTail) * (N : ℝ) := by
  classical
  have hrec := sum_Icc_mul_log_eq f hf1 N
  rw [vonMangoldtOf_eq_pmul_vonMangoldt f hf1 hf] at hrec
  have hsplit : ∑ d ∈ Finset.Icc 1 N, (pmul f Λ) d * ∑ m ∈ Finset.Icc 1 (N / d), f m
      = (∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
            f p * Real.log (p : ℝ) * ∑ m ∈ Finset.Icc 1 (N / p), f m)
        + ∑ d ∈ Finset.Icc 1 N, RHTower.Mertens.notPrimeVonMangoldt d *
            (f d * ∑ m ∈ Finset.Icc 1 (N / d), f m) := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [pmul_apply, RHTower.Mertens.notPrimeVonMangoldt]
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
          mul_le_mul (hbdd d) (abs_sum_Icc_le f hbdd _) (abs_nonneg _) zero_le_one
      _ = ((N / d : ℕ) : ℝ) := one_mul _
  rw [hrec, hsplit, add_sub_cancel_left]
  exact htail

/-- **The entry point of the Halász method.**  For a bounded completely multiplicative `f`,

`S_f(N) log N = ∑_{p ≤ N} f(p) log p · S_f(⌊N/p⌋) + O(N)`,

with the explicit constant `9 + mertensTail`.  Every hypothesis is unconditional and elementary: the
identity `f·log = f * (f·Λ)`, the hyperbola swap, Stirling's lower bound for `log N!`, and the Abel
bound for the prime-power excess.  Decay of `S_f` is therefore equivalent to cancellation in the prime
sum on the right, which is what a distance hypothesis on the values `f(p)` controls. -/
theorem abs_sum_Icc_mul_log_sub_sum_primes_le' (f : ArithmeticFunction ℝ) (hf1 : Invertible (f 1))
    (hf : ∀ m n : ℕ, f (m * n) = f m * f n) (hbdd : ∀ n : ℕ, |f n| ≤ 1) (N : ℕ) :
    |(∑ n ∈ Finset.Icc 1 N, f n) * Real.log (N : ℝ)
        - ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
            f p * Real.log (p : ℝ) * ∑ m ∈ Finset.Icc 1 (N / p), f m|
      ≤ (9 + RHTower.Mertens.mertensTail) * (N : ℝ) := by
  classical
  have h1 := abs_sum_Icc_mul_log_sub_le f hbdd N
  have h2 := abs_sum_Icc_mul_log_sub_sum_primes_le f hf1 hf hbdd N
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

/-- **Propagation across scales.**  If `S_f` is `ε`-small at every scale below `N`, then it is `ε`-small
at `N` up to a loss of order `1/log N`.  The recursion cannot manufacture growth: `S_f(N) log N` is the
prime-weighted average of the divided partial sums, and `∑_{p ≤ N} (log p)/p = log N + O(1)` by Mertens'
first theorem, so the weights carry exactly the factor `log N` that is divided out. -/
theorem abs_sum_Icc_le_of_smaller_scales (f : ArithmeticFunction ℝ) (hf1 : Invertible (f 1))
    (hf : ∀ m n : ℕ, f (m * n) = f m * f n) (hbdd : ∀ n : ℕ, |f n| ≤ 1) {N : ℕ} (hN : 1 ≤ N)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ∀ M : ℕ, 1 ≤ M → M < N → |∑ m ∈ Finset.Icc 1 M, f m| ≤ ε * (M : ℝ)) :
    |∑ n ∈ Finset.Icc 1 N, f n| * Real.log (N : ℝ)
      ≤ (9 + RHTower.Mertens.mertensTail) * (N : ℝ)
        + ε * (N : ℝ) * (Real.log (N : ℝ)
            + ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail))) := by
  classical
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hmain := abs_sum_Icc_mul_log_sub_sum_primes_le' f hf1 hf hbdd N
  have hterm : ∀ p ∈ Finset.Icc 1 N with Nat.Prime p,
      |f p * Real.log (p : ℝ) * ∑ m ∈ Finset.Icc 1 (N / p), f m|
        ≤ ε * (N : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hpN⟩, hpp⟩ := hp
    have hp2 : 2 ≤ p := hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      have : 0 < p := by omega
      exact_mod_cast this
    have hlog0 : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp1)
    have hMlow : 1 ≤ N / p := (Nat.one_le_div_iff (by omega)).2 hpN
    have hMhigh : N / p < N := Nat.div_lt_self (by omega) (by omega)
    have hS := hsmall (N / p) hMlow hMhigh
    have hcast : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) := Nat.cast_div_le
    rw [abs_mul, abs_mul, abs_of_nonneg hlog0]
    have h1 : |f p| * Real.log (p : ℝ) ≤ Real.log (p : ℝ) := by
      nlinarith [hbdd p, hlog0, abs_nonneg (f p)]
    have h2 : |∑ m ∈ Finset.Icc 1 (N / p), f m| ≤ ε * ((N : ℝ) / (p : ℝ)) := by
      refine hS.trans ?_
      exact mul_le_mul_of_nonneg_left hcast hε
    have hchain : |f p| * Real.log (p : ℝ) * |∑ m ∈ Finset.Icc 1 (N / p), f m|
        ≤ Real.log (p : ℝ) * (ε * ((N : ℝ) / (p : ℝ))) :=
      mul_le_mul h1 h2 (abs_nonneg _) hlog0
    have hval : Real.log (p : ℝ) * (ε * ((N : ℝ) / (p : ℝ)))
        = ε * (N : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) := by
      field_simp
      ring
    linarith [hchain, hval.le, hval.ge]
  have hP : |∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
        f p * Real.log (p : ℝ) * ∑ m ∈ Finset.Icc 1 (N / p), f m|
      ≤ ε * (N : ℝ) * (Real.log (N : ℝ)
          + ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail))) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hmert := RHTower.Mertens.mertens_first_prime N hN
    rw [abs_le] at hmert
    have hsum : ∑ p ∈ Finset.Icc 1 N with Nat.Prime p, Real.log (p : ℝ) / (p : ℝ)
        ≤ Real.log (N : ℝ) + ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)) := by
      linarith [hmert.2]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have hsplit : |(∑ n ∈ Finset.Icc 1 N, f n) * Real.log (N : ℝ)|
      ≤ |(∑ n ∈ Finset.Icc 1 N, f n) * Real.log (N : ℝ)
            - ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
                f p * Real.log (p : ℝ) * ∑ m ∈ Finset.Icc 1 (N / p), f m|
        + |∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
            f p * Real.log (p : ℝ) * ∑ m ∈ Finset.Icc 1 (N / p), f m| := by
    have := abs_add_le ((∑ n ∈ Finset.Icc 1 N, f n) * Real.log (N : ℝ)
        - ∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
            f p * Real.log (p : ℝ) * ∑ m ∈ Finset.Icc 1 (N / p), f m)
      (∑ p ∈ Finset.Icc 1 N with Nat.Prime p,
        f p * Real.log (p : ℝ) * ∑ m ∈ Finset.Icc 1 (N / p), f m)
    rwa [sub_add_cancel] at this
  have hprod : |∑ n ∈ Finset.Icc 1 N, f n| * Real.log (N : ℝ)
      = |(∑ n ∈ Finset.Icc 1 N, f n) * Real.log (N : ℝ)| := by
    rw [abs_mul, abs_of_nonneg hlogN]
  rw [hprod]
  linarith

end RHTower.Sieve

end
