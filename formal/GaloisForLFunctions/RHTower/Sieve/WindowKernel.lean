import GaloisForLFunctions.RHTower.Sieve.WindowMultiplicity

/-!
# The exact short-interval variance kernel

Expanding the square and exchanging the order of summation turns the variance of a short-interval sum
into a pair sum against the overlap count

`K(n,m) = #{x < X : n, m ∈ (x, x+L]}`:

`∑_{x < X} ‖∑_{x < n ≤ x+L} a_n‖² = ∑_{n,m} K(n,m) Re(a_n conj a_m)`.

The kernel vanishes off the diagonal band: both `n` and `m` lie in `(x, x+L]` only if
`|n - m| ≤ L - 1`, so `K(n,m) = 0` as soon as `|n - m| ≥ L`.  Short-interval variance is therefore a
local problem — only pairs closer than `L` interact — and this is the discrete counterpart of the
Fejér kernel's support.
-/

namespace RHTower.Sieve

open Finset

/-- The number of window starts seeing both `n` and `m`. -/
noncomputable def windowOverlap (X L n m : ℕ) : ℕ :=
  ((Finset.range X).filter
    (fun x => n ∈ Finset.Ioc x (x + L) ∧ m ∈ Finset.Ioc x (x + L))).card

/-- **The kernel is supported on the diagonal band `|n - m| < L`.** -/
theorem windowOverlap_eq_zero {X L n m : ℕ} (h : n + L ≤ m ∨ m + L ≤ n) :
    windowOverlap X L n m = 0 := by
  classical
  rw [windowOverlap, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _
  rw [not_and_or]
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨hn, hm⟩ := hcon
  rw [Finset.mem_Ioc] at hn hm
  omega

/-- The kernel never exceeds the window length. -/
theorem windowOverlap_le (X L n m : ℕ) : windowOverlap X L n m ≤ L := by
  classical
  refine le_trans (Finset.card_le_card ?_) (card_window_starts_le X L n)
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.1⟩

/-- Exchanging a double window sum for the overlap kernel. -/
theorem sum_window_pair_swap (X L : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ x ∈ Finset.range X, ∑ n ∈ Finset.Ioc x (x + L), ∑ m ∈ Finset.Ioc x (x + L), F n m
      = ∑ n ∈ Finset.range (X + L + 1), ∑ m ∈ Finset.range (X + L + 1),
          (windowOverlap X L n m : ℝ) * F n m := by
  classical
  have hinner : ∀ x ∈ Finset.range X,
      ∑ n ∈ Finset.Ioc x (x + L), ∑ m ∈ Finset.Ioc x (x + L), F n m
        = ∑ n ∈ Finset.range (X + L + 1), ∑ m ∈ Finset.range (X + L + 1),
            (if n ∈ Finset.Ioc x (x + L) ∧ m ∈ Finset.Ioc x (x + L) then F n m else 0) := by
    intro x hx
    rw [Finset.mem_range] at hx
    have hsub : Finset.Ioc x (x + L) ⊆ Finset.range (X + L + 1) := window_subset_range hx
    rw [← Finset.sum_subset hsub (fun n _ hn => ?_)]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [← Finset.sum_subset hsub (fun m _ hm => ?_)]
      · refine Finset.sum_congr rfl fun m hm => ?_
        rw [if_pos ⟨hn, hm⟩]
      · rw [if_neg (by tauto)]
    · refine Finset.sum_eq_zero fun m _ => ?_
      rw [if_neg (by tauto)]
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, windowOverlap]

/-- **The exact short-interval variance identity.** -/
theorem sum_normSq_window_eq (a : ℕ → ℂ) (X L : ℕ) :
    ∑ x ∈ Finset.range X, ‖∑ n ∈ Finset.Ioc x (x + L), a n‖ ^ 2
      = ∑ n ∈ Finset.range (X + L + 1), ∑ m ∈ Finset.range (X + L + 1),
          (windowOverlap X L n m : ℝ) * (a n * (starRingEnd ℂ) (a m)).re := by
  classical
  rw [← sum_window_pair_swap X L (fun n m => (a n * (starRingEnd ℂ) (a m)).re)]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hnormSq : ‖∑ n ∈ Finset.Ioc x (x + L), a n‖ ^ 2
      = ((∑ n ∈ Finset.Ioc x (x + L), a n)
          * (starRingEnd ℂ) (∑ n ∈ Finset.Ioc x (x + L), a n)).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hnormSq, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.re_sum]

end RHTower.Sieve
