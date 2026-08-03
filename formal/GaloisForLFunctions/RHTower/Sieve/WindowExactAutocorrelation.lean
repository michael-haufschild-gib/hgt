import GaloisForLFunctions.RHTower.Sieve.ShiftReindex
import GaloisForLFunctions.RHTower.Sieve.WindowTriangularWeight

/-!
# The variance equals the correlations

Splitting the exact pair-sum identity into diagonal and upper triangle and reindexing by the shift
gives an **equality**, not a bound:

`∑_{x < X} ‖∑_{x < n ≤ x+L} a_n‖²
   = ∑_n K(n,n) ‖a_n‖² + 2 ∑_{h ≥ 1} ∑_n K(n,n+h) Re(a_n conj a_{n+h})`.

Since the kernel is `L` on the diagonal and `L - h` at shift `h` in the bulk, the short-interval
variance is *determined* by the shifted correlations: it is small exactly when they cancel.  The
earlier bound replaced `Re(a_n conj a_{n+h})` by `‖a_n‖‖a_{n+h}‖` and so discarded all cancellation;
here nothing is discarded.
-/

namespace RHTower.Sieve

open Finset

/-- The Hermitian pair weight is symmetric. -/
theorem re_mul_conj_comm (u v : ℂ) :
    (u * (starRingEnd ℂ) v).re = (v * (starRingEnd ℂ) u).re := by
  have h : (v * (starRingEnd ℂ) u) = (starRingEnd ℂ) (u * (starRingEnd ℂ) v) := by
    simp [map_mul, mul_comm]
  rw [h, Complex.conj_re]

/-- The diagonal weight is the squared norm. -/
theorem re_mul_conj_self (u : ℂ) : (u * (starRingEnd ℂ) u).re = ‖u‖ ^ 2 := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- **The variance equals the weighted correlations.** -/
theorem sum_normSq_window_eq_autocorrelation (a : ℕ → ℂ) (X L : ℕ) :
    ∑ x ∈ Finset.range X, ‖∑ n ∈ Finset.Ioc x (x + L), a n‖ ^ 2
      = ∑ n ∈ Finset.range (X + L + 1), ((windowOverlap X L n n : ℕ) : ℝ) * ‖a n‖ ^ 2
        + 2 * ∑ h ∈ Finset.Ico 1 (X + L + 1), ∑ n ∈ Finset.range (X + L + 1 - h),
            ((windowOverlap X L n (n + h) : ℕ) : ℝ)
              * (a n * (starRingEnd ℂ) (a (n + h))).re := by
  classical
  set R := X + L + 1 with hR
  set W : ℕ → ℕ → ℝ :=
    fun n m => ((windowOverlap X L n m : ℕ) : ℝ) * (a n * (starRingEnd ℂ) (a m)).re with hW
  have hsymm : ∀ n m, W n m = W m n := by
    intro n m
    rw [hW]
    simp only
    rw [windowOverlap_comm, re_mul_conj_comm]
  have hsplit := sum_pair_eq_diag_add_two_upper R W hsymm
  have hdiag : ∑ n ∈ Finset.range R, W n n
      = ∑ n ∈ Finset.range R, ((windowOverlap X L n n : ℕ) : ℝ) * ‖a n‖ ^ 2 := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hW]
    simp only
    rw [re_mul_conj_self]
  have hupper : ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, (if n < m then W n m else 0)
      = ∑ h ∈ Finset.Ico 1 R, ∑ n ∈ Finset.range (R - h),
          ((windowOverlap X L n (n + h) : ℕ) : ℝ)
            * (a n * (starRingEnd ℂ) (a (n + h))).re := by
    rw [sum_upper_triangle_eq_sum_shift R W]
  rw [sum_normSq_window_eq a X L, hsplit, hdiag, hupper]

end RHTower.Sieve
