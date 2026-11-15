import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovBoxSeparation

/-!
# A short vertical-center range misses a moment-manifold corner

In physical dimension three, the shear with both horizontal coefficients
equal to one sends the corner `(1,1,0)` to vertical coordinate `-2` in
inverse shear coordinates. At every positive scale below one half, no
radius-two frame box with vertical center at least `-1` contains this point,
in any positive degree.
-/

open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

private theorem corner_not_mem_center_ge_neg_one (k : ℕ) (ε t : ℝ)
    (hε : 0 < ε) (hsmall : ε < 1 / 2) (ht : -1 ≤ t) :
    horizontalMoment 1 (k + 1) (fun _ => 1) 0 ∉
      momentCoveringBox 1 (k + 1) ε (fun _ => 1 / ε) t := by
  intro h
  have hv := (mem_momentCoveringBox_projection 1 k ε (fun _ => 1 / ε) t
    (horizontalMoment 1 (k + 1) (fun _ => 1) 0) h).2
  rw [degreeOneProjection_moment] at hv
  simp only [Fin.cons_zero, Fin.cons_succ] at hv
  have hs : ε * (∑ _ : Fin 2, (1 / ε) * (1 : ℝ)) = 2 := by
    calc
      _ = (2 / ε) * ε := by norm_num [Fin.sum_univ_succ]; ring
      _ = 2 := div_mul_cancel₀ 2 (ne_of_gt hε)
  rw [hs, abs_of_pos hε] at hv
  have hlo := (abs_le.mp hv).1
  linarith only [ht, hlo, hsmall]

/-- The short-center obstruction persists at every positive scale below one half. -/
theorem corner_not_mem_short_center_union_small_scale (k : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hsmall : ε < 1 / 2) :
    horizontalMoment 1 (k + 1) (fun _ => 1) 0 ∉
      ⋃ t ∈ Set.Icc (-1 : ℝ) 1, momentCoveringBox 1 (k + 1) ε (fun _ => 1 / ε) t := by
  intro h
  simp only [Set.mem_iUnion] at h
  obtain ⟨t, ht, hm⟩ := h
  exact corner_not_mem_center_ge_neg_one k ε t hε hsmall ht.1 hm

/-- The entire vertical-center interval `[-1,1]` misses a corner of the unit moment manifold. -/
theorem corner_not_mem_short_center_union (k : ℕ) :
    horizontalMoment 1 (k + 1) (fun _ => 1) 0 ∉
      ⋃ t ∈ Set.Icc (-1 : ℝ) 1, momentCoveringBox 1 (k + 1) (1 / 4) (fun _ => 4) t := by
  simpa only [show (1 : ℝ) / (1 / 4) = 4 by norm_num] using
    corner_not_mem_short_center_union_small_scale k (1 / 4) (by norm_num) (by norm_num)

/-- Positive-degree moment images of the full physical unit cube are not covered by these short-center boxes. -/
theorem short_center_union_not_cover_unit_moments (k : ℕ) :
    ¬ (∀ (u : Fin 2 → ℝ) (z : ℝ), (∀ i, 0 ≤ u i ∧ u i ≤ 1) → 0 ≤ z → z ≤ 1 →
      horizontalMoment 1 (k + 1) u z ∈
        ⋃ t ∈ Set.Icc (-1 : ℝ) 1, momentCoveringBox 1 (k + 1) (1 / 4) (fun _ => 4) t) := by
  intro h
  exact corner_not_mem_short_center_union k
    (h (fun _ => 1) 0 (by intro i; norm_num) (by norm_num) (by norm_num))

#print axioms corner_not_mem_short_center_union_small_scale
#print axioms corner_not_mem_short_center_union
#print axioms short_center_union_not_cover_unit_moments

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
