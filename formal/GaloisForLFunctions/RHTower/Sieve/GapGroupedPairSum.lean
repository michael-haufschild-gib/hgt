import GaloisForLFunctions.RHTower.Sieve.PairGapScale

/-!
# Grouping an off-diagonal pair sum by the gap

For a fixed first member, each gap `h` is realised by at most two second members, so a pair sum of
a gap-only weight is at most `2·|S|` times the sum of the weight over the gaps.  This is the step
that turns the type-II off-diagonal total into a one-dimensional `h`-sum.
-/

namespace RHTower.Sieve

open Finset

/-- At most two elements realise a given gap. -/
theorem card_filter_dist_le_two (S : Finset ℕ) (m₁ h : ℕ) :
    (S.filter (fun m₂ => Nat.dist m₁ m₂ = h)).card ≤ 2 := by
  classical
  have hsub : S.filter (fun m₂ => Nat.dist m₁ m₂ = h) ⊆ {m₁ + h, m₁ - h} := by
    intro m₂ hm₂
    rw [Finset.mem_filter] at hm₂
    have hd := hm₂.2
    rw [Nat.dist] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  refine le_trans (Finset.card_le_card hsub) ?_
  exact le_trans (Finset.card_insert_le _ _) (by simp)

/-- **The gap-grouped bound for one row.** -/
theorem sum_row_gap_le (S : Finset ℕ) (H : ℕ) (G : ℕ → ℝ) (hG : ∀ h, 0 ≤ G h)
    {m₁ : ℕ} (hmap : ∀ m₂ ∈ S.erase m₁, Nat.dist m₁ m₂ ∈ Finset.Icc 1 H) :
    (∑ m₂ ∈ S.erase m₁, G (Nat.dist m₁ m₂)) ≤ 2 * ∑ h ∈ Finset.Icc 1 H, G h := by
  classical
  · have hfib := Finset.sum_fiberwise_of_maps_to (s := S.erase m₁)
      (t := Finset.Icc 1 H) (g := fun m₂ => Nat.dist m₁ m₂)
      (fun m₂ hm₂ => hmap m₂ hm₂) (fun m₂ => G (Nat.dist m₁ m₂))
    rw [← hfib]
    have hstep : ∀ h ∈ Finset.Icc 1 H,
        (∑ m₂ ∈ (S.erase m₁).filter (fun m₂ => Nat.dist m₁ m₂ = h), G (Nat.dist m₁ m₂))
          ≤ 2 * G h := by
      intro h _
      have hconst : (∑ m₂ ∈ (S.erase m₁).filter (fun m₂ => Nat.dist m₁ m₂ = h),
          G (Nat.dist m₁ m₂))
          = (((S.erase m₁).filter (fun m₂ => Nat.dist m₁ m₂ = h)).card : ℝ) * G h := by
        rw [Finset.sum_congr rfl (fun m₂ hm₂ => by
          rw [(Finset.mem_filter.1 hm₂).2]), Finset.sum_const, nsmul_eq_mul]
      rw [hconst]
      have hcard : (((S.erase m₁).filter (fun m₂ => Nat.dist m₁ m₂ = h)).card : ℝ) ≤ 2 := by
        have h2 := card_filter_dist_le_two (S.erase m₁) m₁ h
        exact_mod_cast h2
      exact mul_le_mul_of_nonneg_right hcard (hG h)
    refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
    rw [← Finset.mul_sum]

/-- **The gap-grouped bound for an off-diagonal pair sum.** -/
theorem sum_offdiag_gap_le (S : Finset ℕ) (H : ℕ) (G : ℕ → ℝ) (hG : ∀ h, 0 ≤ G h)
    (hmap : ∀ m₁ ∈ S, ∀ m₂ ∈ S.erase m₁, Nat.dist m₁ m₂ ∈ Finset.Icc 1 H) :
    (∑ m₁ ∈ S, ∑ m₂ ∈ S.erase m₁, G (Nat.dist m₁ m₂))
      ≤ 2 * (S.card : ℝ) * ∑ h ∈ Finset.Icc 1 H, G h := by
  classical
  refine le_trans (Finset.sum_le_sum fun m₁ hm₁ =>
    sum_row_gap_le S H G hG (fun m₂ hm₂ => hmap m₁ hm₁ m₂ hm₂)) (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

end RHTower.Sieve
