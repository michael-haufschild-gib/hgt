import GaloisForLFunctions.RHTower.Sieve.WindowKernel

/-!
# The overlap kernel is bounded by the triangular weight

Both `n` and `m` lie in `(x, x+L]` only for `max(n,m) - L ≤ x < min(n,m)`, so

`K(n,m) ≤ L - |n - m|`,

the discrete triangular (Fejér) weight.  It vanishes at `|n - m| = L`, recovering the support
statement, and equals `L` on the diagonal.  Feeding it into the exact variance identity,

`∑_{x < X} ‖∑_{x < n ≤ x+L} a_n‖² ≤ ∑_{n,m} (L - |n-m|) ‖a_n‖ ‖a_m‖`,

with the weight decaying linearly away from the diagonal rather than being the constant `L` of the
trivial bound.
-/

namespace RHTower.Sieve

open Finset

/-- The overlap kernel is symmetric. -/
theorem windowOverlap_comm (X L n m : ℕ) : windowOverlap X L n m = windowOverlap X L m n := by
  classical
  rw [windowOverlap, windowOverlap]
  congr 1
  exact Finset.filter_congr fun x _ => by tauto

/-- The triangular bound, in the ordered case. -/
theorem windowOverlap_le_sub_of_le {X L n m : ℕ} (hnm : n ≤ m) :
    windowOverlap X L n m ≤ L - (m - n) := by
  classical
  have hsub : (Finset.range X).filter
      (fun x => n ∈ Finset.Ioc x (x + L) ∧ m ∈ Finset.Ioc x (x + L))
      ⊆ Finset.Ico (m - L) n := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioc] at hx
    obtain ⟨_, ⟨hn1, hn2⟩, ⟨hm1, hm2⟩⟩ := hx
    rw [Finset.mem_Ico]
    omega
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Nat.card_Ico]
  omega

/-- **The overlap kernel is at most the triangular weight `L - |n - m|`.** -/
theorem windowOverlap_le_sub_dist (X L n m : ℕ) :
    windowOverlap X L n m ≤ L - Nat.dist n m := by
  rcases le_total n m with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    exact windowOverlap_le_sub_of_le h
  · rw [windowOverlap_comm, Nat.dist_comm, Nat.dist_eq_sub_of_le h]
    exact windowOverlap_le_sub_of_le h

/-- **The short-interval variance against the triangular weight.** -/
theorem sum_normSq_window_le_triangular (a : ℕ → ℂ) (X L : ℕ) :
    ∑ x ∈ Finset.range X, ‖∑ n ∈ Finset.Ioc x (x + L), a n‖ ^ (2 : ℕ)
      ≤ ∑ n ∈ Finset.range (X + L + 1), ∑ m ∈ Finset.range (X + L + 1),
          ((L - Nat.dist n m : ℕ) : ℝ) * (‖a n‖ * ‖a m‖) := by
  classical
  rw [sum_normSq_window_eq]
  refine Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => ?_
  have hK : ((windowOverlap X L n m : ℕ) : ℝ) ≤ ((L - Nat.dist n m : ℕ) : ℝ) := by
    exact_mod_cast windowOverlap_le_sub_dist X L n m
  have hK0 : (0 : ℝ) ≤ ((windowOverlap X L n m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hre : (a n * (starRingEnd ℂ) (a m)).re ≤ ‖a n‖ * ‖a m‖ := by
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_mul, RCLike.norm_conj]
  have hnn : (0 : ℝ) ≤ ‖a n‖ * ‖a m‖ := by positivity
  calc ((windowOverlap X L n m : ℕ) : ℝ) * (a n * (starRingEnd ℂ) (a m)).re
      ≤ ((windowOverlap X L n m : ℕ) : ℝ) * (‖a n‖ * ‖a m‖) :=
        mul_le_mul_of_nonneg_left hre hK0
    _ ≤ ((L - Nat.dist n m : ℕ) : ℝ) * (‖a n‖ * ‖a m‖) :=
        mul_le_mul_of_nonneg_right hK hnn

end RHTower.Sieve
