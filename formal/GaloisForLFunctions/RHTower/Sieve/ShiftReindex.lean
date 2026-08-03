import Mathlib

/-!
# Reindexing a pair sum by the shift

The strictly upper triangular pairs `n < m < R` are parametrised by the shift `h = m - n`:

`∑_{n < m < R} F(n,m) = ∑_{1 ≤ h < R} ∑_{n < R - h} F(n, n+h)`,

the bijection being `(n,m) ↦ (m-n, n)` with inverse `(h,n) ↦ (n, n+h)`.  Combined with the
trichotomy split of a symmetric pair sum into its diagonal and two triangles, this turns any
pair sum into a diagonal term plus a sum of *shifted correlations* — the form in which a
short-interval variance is actually estimated.
-/

namespace RHTower.Sieve

open Finset

/-- **Reindexing the upper triangle by the shift.** -/
theorem sum_upper_triangle_eq_sum_shift (R : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, (if n < m then F n m else 0)
      = ∑ h ∈ Finset.Ico 1 R, ∑ n ∈ Finset.range (R - h), F n (n + h) := by
  classical
  have hfilter : ∀ n, ∑ m ∈ Finset.range R, (if n < m then F n m else 0)
      = ∑ m ∈ (Finset.range R).filter (fun m => n < m), F n m := by
    intro n
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl fun n _ => hfilter n, Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.2 - x.1, x.1⟩) (fun y => ⟨y.2, y.2 + y.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, m⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Finset.mem_Ico] at hx ⊢
    omega
  · rintro ⟨h, n⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Finset.mem_Ico] at hy ⊢
    omega
  · rintro ⟨n, m⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hx
    have : n + (m - n) = m := by omega
    simp [this]
  · rintro ⟨h, n⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hy
    simp
  · rintro ⟨n, m⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hx
    have : n + (m - n) = m := by omega
    simp [this]

/-- **Trichotomy split of a symmetric pair sum.** -/
theorem sum_pair_eq_diag_add_two_upper (R : ℕ) (W : ℕ → ℕ → ℝ)
    (hsymm : ∀ n m, W n m = W m n) :
    ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, W n m
      = ∑ n ∈ Finset.range R, W n n
        + 2 * ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, (if n < m then W n m else 0) := by
  classical
  have hsplit : ∀ n m : ℕ, W n m = (if n = m then W n m else 0) + (if n < m then W n m else 0)
      + (if m < n then W n m else 0) := by
    intro n m
    rcases lt_trichotomy n m with h | h | h
    · rw [if_neg (by omega), if_pos h, if_neg (by omega)]; ring
    · rw [if_pos h, if_neg (by omega), if_neg (by omega)]; ring
    · rw [if_neg (by omega), if_neg (by omega), if_pos h]; ring
  have hdiag : ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, (if n = m then W n m else 0)
      = ∑ n ∈ Finset.range R, W n n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.sum_ite_eq (Finset.range R) n (fun m => W n m), if_pos hn]
  have hlower : ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, (if m < n then W n m else 0)
      = ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, (if n < m then W n m else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    by_cases h : n < m
    · rw [if_pos h, if_pos h, hsymm]
    · rw [if_neg h, if_neg h]
  calc ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, W n m
      = ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R,
          ((if n = m then W n m else 0) + (if n < m then W n m else 0)
            + (if m < n then W n m else 0)) :=
        Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => hsplit n m
    _ = ∑ n ∈ Finset.range R, W n n
        + 2 * ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, (if n < m then W n m else 0) := by
        simp only [Finset.sum_add_distrib]
        rw [hdiag, hlower]
        ring

end RHTower.Sieve
