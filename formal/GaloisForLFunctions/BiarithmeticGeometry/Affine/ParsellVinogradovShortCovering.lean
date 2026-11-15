import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovBoxSeparation

/-!
# A short vertical-center range misses a moment-manifold corner

In physical dimension three, the shear with both horizontal coefficients
equal to one sends the corner `(1,1,0)` to vertical coordinate `-2` in
inverse shear coordinates. At scale one quarter, no radius-two frame box
with vertical center at least `-1` contains this point, in any positive degree.
-/

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

private theorem corner_not_mem_center_ge_neg_one (k : ℕ) (t : ℝ) (ht : -1 ≤ t) :
    horizontalMoment 1 (k + 1) (fun _ => 1) 0 ∉
      momentCoveringBox 1 (k + 1) (1 / 4) (fun _ => 4) t := by
  intro h
  have hv := (mem_momentCoveringBox_projection 1 k (1 / 4) (fun _ => 4) t
    (horizontalMoment 1 (k + 1) (fun _ => 1) 0) h).2
  rw [degreeOneProjection_moment] at hv
  norm_num [Fin.sum_univ_succ] at hv
  have hlo := (abs_le.mp hv).1
  have hhi := (abs_le.mp hv).2
  linarith only [ht, hlo, hhi]

/-- The entire vertical-center interval `[-1,1]` misses a corner of the unit moment manifold. -/
theorem corner_not_mem_short_center_union (k : ℕ) :
    horizontalMoment 1 (k + 1) (fun _ => 1) 0 ∉
      ⋃ t ∈ Set.Icc (-1 : ℝ) 1, momentCoveringBox 1 (k + 1) (1 / 4) (fun _ => 4) t := by
  intro h
  simp only [Set.mem_iUnion] at h
  obtain ⟨t, ht, hm⟩ := h
  exact corner_not_mem_center_ge_neg_one k t ht.1 hm

/-- Positive-degree moment images of the full physical unit cube are not covered by these short-center boxes. -/
theorem short_center_union_not_cover_unit_moments (k : ℕ) :
    ¬ (∀ (u : Fin 2 → ℝ) (z : ℝ), (∀ i, 0 ≤ u i ∧ u i ≤ 1) → 0 ≤ z → z ≤ 1 →
      horizontalMoment 1 (k + 1) u z ∈
        ⋃ t ∈ Set.Icc (-1 : ℝ) 1, momentCoveringBox 1 (k + 1) (1 / 4) (fun _ => 4) t) := by
  intro h
  exact corner_not_mem_short_center_union k
    (h (fun _ => 1) 0 (by intro i; norm_num) (by norm_num) (by norm_num))

#print axioms corner_not_mem_short_center_union
#print axioms short_center_union_not_cover_unit_moments

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
