import GaloisForLFunctions.RHTower.Sieve.GallagherReverse

/-!
# The almost-diagonal mean value theorem

The exact quadratic form of a logarithmic short-interval mean square,

`∫_ℝ ‖∑_{u < log n ≤ u+δ} a_n‖² du = ∑_{n,m} Re(a_n conj a_m) (δ - |log n - log m|)₊`,

is supported on pairs whose logarithms are within `δ`.  Bounding `Re(a_n conj a_m)` by
`(‖a_n‖² + ‖a_m‖²)/2` and the kernel by `δ` on that support gives

`∫_ℝ ‖∑_{u < log n ≤ u+δ} a_n‖² du ≤ δ ∑_n ‖a_n‖² · #{m : |log n - log m| < δ}`,

and Gallagher's lemma turns this into a mean value theorem for the Dirichlet polynomial:

`∫_{-W}^{W} ‖∑_n a_n n^{2πiw}‖² dw ≤ (5/(4δ)) ∑_n ‖a_n‖² · #{m : |log n - log m| < δ}`,   `2πδW ≤ 1`.

The arithmetic content is now a single count: how many indices of the support lie in a multiplicative
window of ratio `e^δ`.  For a sparse support — the primes, say — that count is far smaller than the
number of indices, and the resulting bound is correspondingly sharper than the classical mean value
theorem, whose error term `O(N ∑‖a_n‖²)` knows nothing about the support.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Set Finset

/-- The number of indices of `s` whose logarithm is within `δ` of `log n`. -/
noncomputable def logNeighbourCount (s : Finset ℕ) (δ : ℝ) (n : ℕ) : ℕ :=
  #{m ∈ s | |Real.log n - Real.log m| < δ}

/-- The kernel of the quadratic form is dominated by `δ` on the near-diagonal and vanishes off it. -/
theorem max_sub_abs_le_indicator {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    max (δ - |x|) 0 ≤ δ * (if |x| < δ then (1 : ℝ) else 0) := by
  by_cases h : |x| < δ
  · rw [if_pos h, mul_one]
    rcases le_total (δ - |x|) 0 with hle | hle
    · rw [max_eq_right hle]
      linarith
    · rw [max_eq_left hle]
      have : 0 ≤ |x| := abs_nonneg x
      linarith
  · rw [if_neg h, mul_zero]
    have hge : δ ≤ |x| := not_lt.mp h
    exact max_eq_right (by linarith)

/-- **The almost-diagonal bound for a logarithmic short-interval mean square.** -/
theorem integral_normSq_logWindowSum_le_count (a : ℕ → ℂ) (s : Finset ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ u : ℝ, ‖logWindowSum a s δ u‖ ^ 2)
      ≤ δ * ∑ n ∈ s, (logNeighbourCount s δ n : ℝ) * ‖a n‖ ^ 2 := by
  classical
  rw [integral_normSq_logWindowSum]
  have hterm : ∀ n ∈ s, ∀ m ∈ s,
      (a n * (starRingEnd ℂ) (a m)).re * max (δ - |Real.log n - Real.log m|) 0
        ≤ δ * ((‖a n‖ ^ 2 + ‖a m‖ ^ 2) / 2)
            * (if |Real.log n - Real.log m| < δ then (1 : ℝ) else 0) := by
    intro n _ m _
    have hre : (a n * (starRingEnd ℂ) (a m)).re ≤ (‖a n‖ ^ 2 + ‖a m‖ ^ 2) / 2 := by
      have h1 : (a n * (starRingEnd ℂ) (a m)).re ≤ ‖a n * (starRingEnd ℂ) (a m)‖ :=
        Complex.re_le_norm _
      have h2 : ‖a n * (starRingEnd ℂ) (a m)‖ = ‖a n‖ * ‖a m‖ := by
        rw [norm_mul, RCLike.norm_conj]
      have h3 : ‖a n‖ * ‖a m‖ ≤ (‖a n‖ ^ 2 + ‖a m‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖a n‖ - ‖a m‖)]
      linarith [h1, h2.le, h2.ge, h3]
    have hker := max_sub_abs_le_indicator hδ (Real.log n - Real.log m)
    have hkernonneg : (0 : ℝ) ≤ max (δ - |Real.log n - Real.log m|) 0 := le_max_right _ _
    have hsum : (0 : ℝ) ≤ (‖a n‖ ^ 2 + ‖a m‖ ^ 2) / 2 := by positivity
    calc (a n * (starRingEnd ℂ) (a m)).re * max (δ - |Real.log n - Real.log m|) 0
        ≤ ((‖a n‖ ^ 2 + ‖a m‖ ^ 2) / 2) * max (δ - |Real.log n - Real.log m|) 0 :=
          mul_le_mul_of_nonneg_right hre hkernonneg
      _ ≤ ((‖a n‖ ^ 2 + ‖a m‖ ^ 2) / 2)
            * (δ * (if |Real.log n - Real.log m| < δ then (1 : ℝ) else 0)) :=
          mul_le_mul_of_nonneg_left hker hsum
      _ = δ * ((‖a n‖ ^ 2 + ‖a m‖ ^ 2) / 2)
            * (if |Real.log n - Real.log m| < δ then (1 : ℝ) else 0) := by ring
  refine le_trans (Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm =>
    hterm n hn m hm) ?_
  -- split the symmetric bound into its two halves
  have hsplit : ∀ n ∈ s, ∑ m ∈ s, δ * ((‖a n‖ ^ 2 + ‖a m‖ ^ 2) / 2)
        * (if |Real.log n - Real.log m| < δ then (1 : ℝ) else 0)
      = (δ / 2) * (‖a n‖ ^ 2 * (logNeighbourCount s δ n : ℝ))
        + (δ / 2) * ∑ m ∈ s, ‖a m‖ ^ 2
            * (if |Real.log n - Real.log m| < δ then (1 : ℝ) else 0) := by
    intro n _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    · refine Finset.sum_congr rfl fun m _ => ?_
      ring
    all_goals skip
  sorry

end RHTower.Sieve

end
