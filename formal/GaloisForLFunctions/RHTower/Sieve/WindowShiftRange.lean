import GaloisForLFunctions.RHTower.Sieve.WindowExactAutocorrelation

/-!
# Only the shifts below `L` matter

The overlap kernel vanishes at `|n - m| ≥ L`, so every shift `h ≥ L` contributes nothing and the
correlation sum runs over `1 ≤ h < L` only:

`∑_{x < X} ‖∑_{x < n ≤ x+L} a_n‖²
   = ∑_n K(n,n) ‖a_n‖² + 2 ∑_{h=1}^{L-1} ∑_n K(n,n+h) Re(a_n conj a_{n+h})`.

The number of correlations involved is therefore `L - 1`, independent of the length `X` of the
average.  This is what makes the reduction useful: a bound for the shifted correlations at the
finitely many shifts `h < L` is enough.
-/

namespace RHTower.Sieve

open Finset

/-- Shifts of at least `L` contribute nothing. -/
theorem windowOverlap_shift_eq_zero {X L n h : ℕ} (hh : L ≤ h) :
    windowOverlap X L n (n + h) = 0 :=
  windowOverlap_eq_zero (Or.inl (by omega))

/-- **The correlation sum runs over `h < L`.** -/
theorem sum_normSq_window_eq_autocorrelation_lt (a : ℕ → ℂ) (X L : ℕ) :
    ∑ x ∈ Finset.range X, ‖∑ n ∈ Finset.Ioc x (x + L), a n‖ ^ 2
      = ∑ n ∈ Finset.range (X + L + 1), ((windowOverlap X L n n : ℕ) : ℝ) * ‖a n‖ ^ 2
        + 2 * ∑ h ∈ Finset.Ico 1 L, ∑ n ∈ Finset.range (X + L + 1 - h),
            ((windowOverlap X L n (n + h) : ℕ) : ℝ)
              * (a n * (starRingEnd ℂ) (a (n + h))).re := by
  classical
  have hsub : Finset.Ico 1 L ⊆ Finset.Ico 1 (X + L + 1) := by
    intro h hh
    rw [Finset.mem_Ico] at hh ⊢
    omega
  have hvanish : ∀ h ∈ Finset.Ico 1 (X + L + 1), h ∉ Finset.Ico 1 L →
      ∑ n ∈ Finset.range (X + L + 1 - h), ((windowOverlap X L n (n + h) : ℕ) : ℝ)
        * (a n * (starRingEnd ℂ) (a (n + h))).re = 0 := by
    intro h hh hnot
    rw [Finset.mem_Ico] at hh hnot
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [windowOverlap_shift_eq_zero (by omega)]
    simp
  rw [sum_normSq_window_eq_autocorrelation a X L, Finset.sum_subset hsub hvanish]

end RHTower.Sieve
