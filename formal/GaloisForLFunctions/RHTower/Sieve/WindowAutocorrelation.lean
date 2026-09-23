import GaloisForLFunctions.RHTower.Sieve.ShiftReindex
import GaloisForLFunctions.RHTower.Sieve.WindowTriangularWeight

/-!
# The short-interval variance in autocorrelation form

Splitting the triangular pair sum into its diagonal and its upper triangle, and reindexing the latter
by the shift, gives

`∑_{n,m < R} (L - |n-m|) ‖a_n‖‖a_m‖ = L ∑_{n < R} ‖a_n‖² + 2 ∑_{h=1}^{R-1} (L-h) ∑_{n < R-h} ‖a_n‖‖a_{n+h}‖`,

so the short-interval variance is bounded by a diagonal term plus a weighted sum of shifted
correlations.  For a coefficient sequence bounded by one the diagonal is `O(LR)`; everything beyond
that is governed by the correlations at shift `h`, weighted by the same triangular factor `L - h` and
so supported on `h < L`.
-/

namespace RHTower.Sieve

open Finset

/-- **The triangular pair sum in autocorrelation form.** -/
theorem sum_pair_triangular_eq_autocorrelation (a : ℕ → ℂ) (R L : ℕ) :
    ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R,
        ((L - Nat.dist n m : ℕ) : ℝ) * (‖a n‖ * ‖a m‖)
      = (L : ℝ) * ∑ n ∈ Finset.range R, ‖a n‖ ^ (2 : ℕ)
        + 2 * ∑ h ∈ Finset.Ico 1 R, ((L - h : ℕ) : ℝ)
            * ∑ n ∈ Finset.range (R - h), ‖a n‖ * ‖a (n + h)‖ := by
  classical
  set W : ℕ → ℕ → ℝ := fun n m => ((L - Nat.dist n m : ℕ) : ℝ) * (‖a n‖ * ‖a m‖) with hW
  have hsymm : ∀ n m, W n m = W m n := by
    intro n m
    rw [hW]
    simp only
    rw [Nat.dist_comm, mul_comm (‖a n‖)]
  have hsplit := sum_pair_eq_diag_add_two_upper R W hsymm
  have hdiag : ∑ n ∈ Finset.range R, W n n = (L : ℝ) * ∑ n ∈ Finset.range R, ‖a n‖ ^ (2 : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hW]
    simp only [Nat.dist_self, Nat.sub_zero]
    ring
  have hupper : ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, (if n < m then W n m else 0)
      = ∑ h ∈ Finset.Ico 1 R, ((L - h : ℕ) : ℝ)
          * ∑ n ∈ Finset.range (R - h), ‖a n‖ * ‖a (n + h)‖ := by
    rw [sum_upper_triangle_eq_sum_shift R W]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hW]
    simp only
    have hd : Nat.dist n (n + h) = h := by
      rw [Nat.dist_eq_sub_of_le (Nat.le_add_right n h)]
      omega
    rw [hd]
  rw [hsplit, hdiag, hupper]

/-- **The short-interval variance, bounded in autocorrelation form.** -/
theorem sum_normSq_window_le_autocorrelation (a : ℕ → ℂ) (X L : ℕ) :
    ∑ x ∈ Finset.range X, ‖∑ n ∈ Finset.Ioc x (x + L), a n‖ ^ (2 : ℕ)
      ≤ (L : ℝ) * ∑ n ∈ Finset.range (X + L + 1), ‖a n‖ ^ (2 : ℕ)
        + 2 * ∑ h ∈ Finset.Ico 1 (X + L + 1), ((L - h : ℕ) : ℝ)
            * ∑ n ∈ Finset.range (X + L + 1 - h), ‖a n‖ * ‖a (n + h)‖ := by
  refine le_trans (sum_normSq_window_le_triangular a X L) ?_
  exact le_of_eq (sum_pair_triangular_eq_autocorrelation a (X + L + 1) L)

end RHTower.Sieve
