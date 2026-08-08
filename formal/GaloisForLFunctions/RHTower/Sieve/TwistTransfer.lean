import GaloisForLFunctions.RHTower.Sieve.DirichletLipschitz

/-!
# Transferring a partial-sum bound across a twist

Halász's exceptional frequency is handled by twisting: if `f` is close to `n^{iτ}` then `g(n) = f(n)n^{−iτ}`
is far from every character near the origin, and a bound for the partial sums of `g` must be carried back
to those of `f`.  Summation by parts does it at the cost of a single factor:

`‖∑_{n ≤ N} g(n)n^{iτ}‖ ≤ (1 + |τ| log N)·max_{m ≤ N} ‖∑_{n ≤ m} g(n)‖`.

The cost is the total variation of the twist along the integers, `∑_{n < N} ‖(n+1)^{iτ} − n^{iτ}‖`, which
telescopes to `|τ| log N` because the phase exponential is `1`-Lipschitz: the chord never exceeds the arc.
Nothing about `g` is used beyond the hypothesis, so this is the general transfer, valid for any sequence
and any real frequency.
-/

noncomputable section
namespace RHTower.Sieve
open Complex

/-- The twist `n^{iτ}` is the phase of `τ log n`. -/
theorem natCast_cpow_mul_I (τ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℂ) ^ ((τ : ℂ) * I) = Complex.exp (((τ * Real.log n : ℝ) : ℂ) * I) := by
  have hn0 : ((n : ℂ)) ≠ 0 := by
    have : (0 : ℕ) < n := hn
    exact_mod_cast Nat.cast_ne_zero.2 (by omega)
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := hn
    exact_mod_cast this
  rw [Complex.cpow_def_of_ne_zero hn0]
  congr 1
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hnR.le]
  push_cast
  ring

/-- **Summation by parts for a twisted sum.**  The twisted partial sum is the untwisted one at the top,
minus the untwisted partial sums against the increments of the twist. -/
theorem sum_Icc_mul_phase_eq (g : ℕ → ℂ) (τ : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, g n * Complex.exp (((τ * Real.log n : ℝ) : ℂ) * I))
      = (∑ n ∈ Finset.Icc 1 N, g n) * Complex.exp (((τ * Real.log N : ℝ) : ℂ) * I)
        - ∑ n ∈ Finset.range N, (∑ m ∈ Finset.Icc 1 n, g m)
            * (Complex.exp (((τ * Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * I)
                - Complex.exp (((τ * Real.log n : ℝ) : ℂ) * I)) := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Finset.sum_range_succ]
      push_cast
      ring

/-- The increment of the twist along the integers is at most `|τ|` times the increment of the
logarithm. -/
theorem norm_phase_succ_sub_le (τ : ℝ) (n : ℕ) :
    ‖Complex.exp (((τ * Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * I)
        - Complex.exp (((τ * Real.log n : ℝ) : ℂ) * I)‖
      ≤ |τ| * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  refine le_trans (norm_exp_phase_sub_le _ _) ?_
  have hmono : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact Real.log_le_log hnR (by linarith)
  rw [show τ * Real.log ((n : ℝ) + 1) - τ * Real.log n
      = τ * (Real.log ((n : ℝ) + 1) - Real.log n) by ring, abs_mul,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.log ((n : ℝ) + 1) - Real.log n)]

/-- **The twist transfer.**  A bound on every partial sum of `g` bounds the twisted sum at the cost of
`1 + |τ| log N`. -/
theorem norm_sum_Icc_mul_phase_le {g : ℕ → ℂ} {τ S : ℝ} {N : ℕ}
    (hS : ∀ m : ℕ, m ≤ N → ‖∑ n ∈ Finset.Icc 1 m, g n‖ ≤ S) :
    ‖∑ n ∈ Finset.Icc 1 N, g n * Complex.exp (((τ * Real.log n : ℝ) : ℂ) * I)‖
      ≤ (1 + |τ| * Real.log N) * S := by
  have hS0 : 0 ≤ S := le_trans (norm_nonneg _) (hS 0 (Nat.zero_le N))
  have htel : ∑ n ∈ Finset.range N, (Real.log ((n : ℝ) + 1) - Real.log n) = Real.log N := by
    have h := Finset.sum_range_sub (f := fun n : ℕ => Real.log (n : ℝ)) N
    simp only [Nat.cast_add, Nat.cast_one] at h
    rw [h]
    simp
  rw [sum_Icc_mul_phase_eq g τ N]
  refine le_trans (norm_sub_le _ _) ?_
  have htop : ‖(∑ n ∈ Finset.Icc 1 N, g n) * Complex.exp (((τ * Real.log N : ℝ) : ℂ) * I)‖ ≤ S := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hS N le_rfl
  have hrest : ‖∑ n ∈ Finset.range N, (∑ m ∈ Finset.Icc 1 n, g m)
      * (Complex.exp (((τ * Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * I)
          - Complex.exp (((τ * Real.log n : ℝ) : ℂ) * I))‖
      ≤ (|τ| * Real.log N) * S := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Finset.range N,
        ‖(∑ m ∈ Finset.Icc 1 n, g m)
            * (Complex.exp (((τ * Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * I)
                - Complex.exp (((τ * Real.log n : ℝ) : ℂ) * I))‖
          ≤ S * (|τ| * (Real.log ((n : ℝ) + 1) - Real.log n)) := by
      intro n hn
      have hnN : n ≤ N := le_of_lt (Finset.mem_range.1 hn)
      rw [norm_mul]
      exact mul_le_mul (hS n hnN) (norm_phase_succ_sub_le τ n) (norm_nonneg _) hS0
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [← Finset.mul_sum, ← Finset.mul_sum, htel]
    ring
  linarith

/-- The twist transfer with the twist displayed as a complex power. -/
theorem norm_sum_Icc_mul_cpow_mul_I_le {g : ℕ → ℂ} {τ S : ℝ} {N : ℕ}
    (hS : ∀ m : ℕ, m ≤ N → ‖∑ n ∈ Finset.Icc 1 m, g n‖ ≤ S) :
    ‖∑ n ∈ Finset.Icc 1 N, g n * (n : ℂ) ^ ((τ : ℂ) * I)‖ ≤ (1 + |τ| * Real.log N) * S := by
  have hcongr : (∑ n ∈ Finset.Icc 1 N, g n * (n : ℂ) ^ ((τ : ℂ) * I))
      = ∑ n ∈ Finset.Icc 1 N, g n * Complex.exp (((τ * Real.log n : ℝ) : ℂ) * I) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [natCast_cpow_mul_I τ (Finset.mem_Icc.1 hn).1]
  rw [hcongr]
  exact norm_sum_Icc_mul_phase_le hS

end RHTower.Sieve
end
