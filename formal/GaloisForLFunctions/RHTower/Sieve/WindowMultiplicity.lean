import Mathlib

/-!
# Windows through a point, and the trivial short-interval variance bound

An integer `n` lies in the window `(x, x+L]` exactly when `n - L ≤ x < n`, so at most `L` of the
starts `x` see it:

`#{x < X : n ∈ (x, x+L]} ≤ L`.

Summing Cauchy–Schwarz over the windows and then exchanging the order of summation gives the trivial
variance bound

`∑_{x < X} ‖∑_{x < n ≤ x+L} a_n‖² ≤ L² ∑_n ‖a_n‖²`.

This is the bound every short-interval variance argument improves on; the point of recording it is
that the multiplicity count, not the Cauchy–Schwarz, is what fixes the shape.
-/

namespace RHTower.Sieve

open Finset

/-- **At most `L` window starts see a given point.** -/
theorem card_window_starts_le (X L n : ℕ) :
    (((Finset.range X).filter (fun x => n ∈ Finset.Ioc x (x + L))).card : ℕ) ≤ L := by
  classical
  have hsub : (Finset.range X).filter (fun x => n ∈ Finset.Ioc x (x + L))
      ⊆ Finset.Ico (n - L) n := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Ioc] at hx
    obtain ⟨_, hx1, hx2⟩ := hx
    rw [Finset.mem_Ico]
    omega
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Nat.card_Ico]
  omega

/-- The window lies inside the ambient range. -/
theorem window_subset_range {x X L : ℕ} (hx : x < X) :
    Finset.Ioc x (x + L) ⊆ Finset.range (X + L + 1) := by
  intro n hn
  rw [Finset.mem_Ioc] at hn
  rw [Finset.mem_range]
  omega

/-- Exchanging window sums for a multiplicity count. -/
theorem sum_window_sum_le (X L : ℕ) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    ∑ x ∈ Finset.range X, ∑ n ∈ Finset.Ioc x (x + L), w n
      ≤ (L : ℝ) * ∑ n ∈ Finset.range (X + L + 1), w n := by
  classical
  have hinner : ∀ x ∈ Finset.range X, ∑ n ∈ Finset.Ioc x (x + L), w n
      = ∑ n ∈ Finset.range (X + L + 1), (if n ∈ Finset.Ioc x (x + L) then w n else 0) := by
    intro x hx
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun n _ => rfl
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    rw [Finset.mem_range] at hx
    constructor
    · intro h; exact ⟨by omega, by omega⟩
    · rintro ⟨_, h⟩; exact h
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard : (((Finset.range X).filter (fun x => n ∈ Finset.Ioc x (x + L))).card : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast card_window_starts_le X L n
  exact mul_le_mul_of_nonneg_right hcard (hw n)

/-- **The trivial short-interval variance bound.** -/
theorem sum_normSq_window_le (a : ℕ → ℂ) (X L : ℕ) :
    ∑ x ∈ Finset.range X, ‖∑ n ∈ Finset.Ioc x (x + L), a n‖ ^ (2 : ℕ)
      ≤ (L : ℝ) ^ (2 : ℕ) * ∑ n ∈ Finset.range (X + L + 1), ‖a n‖ ^ (2 : ℕ) := by
  classical
  have hcs : ∀ x ∈ Finset.range X, ‖∑ n ∈ Finset.Ioc x (x + L), a n‖ ^ (2 : ℕ)
      ≤ (L : ℝ) * ∑ n ∈ Finset.Ioc x (x + L), ‖a n‖ ^ (2 : ℕ) := by
    intro x _
    have htri : ‖∑ n ∈ Finset.Ioc x (x + L), a n‖ ≤ ∑ n ∈ Finset.Ioc x (x + L), ‖a n‖ :=
      norm_sum_le _ _
    have hcard : ((Finset.Ioc x (x + L)).card : ℝ) = (L : ℝ) := by
      rw [Nat.card_Ioc]
      simp
    have hcauchy : (∑ n ∈ Finset.Ioc x (x + L), ‖a n‖) ^ (2 : ℕ)
        ≤ ((Finset.Ioc x (x + L)).card : ℝ) * ∑ n ∈ Finset.Ioc x (x + L), ‖a n‖ ^ (2 : ℕ) :=
      sq_sum_le_card_mul_sum_sq
    rw [hcard] at hcauchy
    have hnn : (0 : ℝ) ≤ ∑ n ∈ Finset.Ioc x (x + L), ‖a n‖ :=
      Finset.sum_nonneg fun n _ => norm_nonneg _
    calc ‖∑ n ∈ Finset.Ioc x (x + L), a n‖ ^ (2 : ℕ)
        ≤ (∑ n ∈ Finset.Ioc x (x + L), ‖a n‖) ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ (L : ℝ) * ∑ n ∈ Finset.Ioc x (x + L), ‖a n‖ ^ (2 : ℕ) := hcauchy
  refine le_trans (Finset.sum_le_sum hcs) ?_
  rw [← Finset.mul_sum, sq, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg L)
  exact sum_window_sum_le X L (fun n => ‖a n‖ ^ (2 : ℕ)) fun n => sq_nonneg _

end RHTower.Sieve
