import GaloisForLFunctions.RHTower.Sieve.WindowShiftRange

/-!
# A correlation bound gives the mean-square bound

The exact identity turns any bound on the `L-1` weighted shifted correlations into a bound on the
short-interval variance:

if `|∑_n K(n,n+h) Re(a_n conj a_{n+h})| ≤ δ` for every `1 ≤ h < L`, then

`∑_{x < X} ‖∑_{x < n ≤ x+L} a_n‖² ≤ L ∑_n ‖a_n‖² + 2Lδ`.

The diagonal is bounded by `K(n,n) ≤ L`, and the off-diagonal by the hypothesis at each of the fewer
than `L` shifts.  This is the shape into which the cited correlation estimate plugs: everything on
the left of the implication is proved here, and only the hypothesis is open.
-/

namespace RHTower.Sieve

open Finset

/-- **A correlation bound gives the mean-square bound.** -/
theorem sum_normSq_window_le_of_correlation {a : ℕ → ℂ} {X L : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hcorr : ∀ h ∈ Finset.Ico 1 L,
      |∑ n ∈ Finset.range (X + L + 1 - h), ((windowOverlap X L n (n + h) : ℕ) : ℝ)
        * (a n * (starRingEnd ℂ) (a (n + h))).re| ≤ δ) :
    ∑ x ∈ Finset.range X, ‖∑ n ∈ Finset.Ioc x (x + L), a n‖ ^ 2
      ≤ (L : ℝ) * ∑ n ∈ Finset.range (X + L + 1), ‖a n‖ ^ 2 + 2 * (L : ℝ) * δ := by
  classical
  rw [sum_normSq_window_eq_autocorrelation_lt a X L]
  have hdiag : ∑ n ∈ Finset.range (X + L + 1), ((windowOverlap X L n n : ℕ) : ℝ) * ‖a n‖ ^ 2
      ≤ (L : ℝ) * ∑ n ∈ Finset.range (X + L + 1), ‖a n‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    have hK : ((windowOverlap X L n n : ℕ) : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast windowOverlap_le X L n n
    exact mul_le_mul_of_nonneg_right hK (sq_nonneg _)
  have hoff : ∑ h ∈ Finset.Ico 1 L, ∑ n ∈ Finset.range (X + L + 1 - h),
      ((windowOverlap X L n (n + h) : ℕ) : ℝ) * (a n * (starRingEnd ℂ) (a (n + h))).re
        ≤ (L : ℝ) * δ := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _ |>.trans' (le_abs_self _)) ?_
    refine le_trans (Finset.sum_le_sum hcorr) ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hcard : ((L - 1 : ℕ) : ℝ) ≤ (L : ℝ) := by
      have : (L - 1 : ℕ) ≤ L := Nat.sub_le L 1
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hcard hδ
  linarith

end RHTower.Sieve
