import Mathlib

/-!
# Bounded counting difference forces interleaving

If two monotone sequences have counting functions differing by at most `K`, then the sequences
interleave with shift `K`: the `n`-th term of one is bounded by the `(n+K)`-th term of the other.
Consequently, if the terms have mean spacing `s`, corresponding terms are within `K·s`.

For two Dirichlet series with the same gamma factor, the difference of the zero-counting functions is
an integer-valued step function, and the archimedean main terms cancel; a bound on that difference
therefore pins each zero of one to a zero of the other within `K` times the mean zero spacing.
-/

open Finset

namespace HTGeometry

/-- **Interleaving from a counting bound.**  If, on every threshold `t`, the number of terms of `x`
below `t` exceeds the number of terms of `y` below `t` by at most `K`, then `y n ≤ x (n + K)`. -/
theorem le_shift_of_count_le {x y : ℕ → ℝ} (hx : Monotone x) (hy : Monotone y) {K n N : ℕ}
    (hN : n + K < N)
    (hcount : ∀ t : ℝ, ((Finset.range N).filter (fun i => x i ≤ t)).card
                ≤ ((Finset.range N).filter (fun i => y i ≤ t)).card + K) :
    y n ≤ x (n + K) := by
  by_contra hcon
  push Not at hcon
  set t := x (n + K) with ht
  have hsub : Finset.range (n + K + 1) ⊆ (Finset.range N).filter (fun i => x i ≤ t) := by
    intro i hi
    rw [Finset.mem_range] at hi
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩
    exact hx (by omega)
  have hlow : n + K + 1 ≤ ((Finset.range N).filter (fun i => x i ≤ t)).card := by
    calc n + K + 1 = (Finset.range (n + K + 1)).card := by simp
      _ ≤ _ := Finset.card_le_card hsub
  have hsub2 : (Finset.range N).filter (fun i => y i ≤ t) ⊆ Finset.range n := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_range]
    by_contra hcon2
    push Not at hcon2
    have : y n ≤ y i := hy hcon2
    linarith [hi.2]
  have hhigh : ((Finset.range N).filter (fun i => y i ≤ t)).card ≤ n := by
    calc ((Finset.range N).filter (fun i => y i ≤ t)).card
        ≤ (Finset.range n).card := Finset.card_le_card hsub2
      _ = n := by simp
  have := hcount t
  omega

/-- Symmetric form: a two-sided counting bound interleaves the sequences in both directions. -/
theorem abs_shift_of_count_le {x y : ℕ → ℝ} (hx : Monotone x) (hy : Monotone y) {K n N : ℕ}
    (hN : n + K < N)
    (h1 : ∀ t : ℝ, ((Finset.range N).filter (fun i => x i ≤ t)).card
                ≤ ((Finset.range N).filter (fun i => y i ≤ t)).card + K)
    (h2 : ∀ t : ℝ, ((Finset.range N).filter (fun i => y i ≤ t)).card
                ≤ ((Finset.range N).filter (fun i => x i ≤ t)).card + K) :
    y n ≤ x (n + K) ∧ x n ≤ y (n + K) :=
  ⟨le_shift_of_count_le hx hy hN h1, le_shift_of_count_le hy hx hN h2⟩

end HTGeometry
