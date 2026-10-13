import GaloisForLFunctions.HTGeometry.PaperCoordinateCompression

/-! # Contractive coordinate tails and exact single-coordinate prefixes

Both a coordinate prefix and its complementary tail are contractions.
These bounds apply to every vector history and every bounded operator.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem paperCoordinateProjection_single (N j : ℕ) (z : E) :
    paperCoordinateProjection N (lp.single 2 j z) =
      if j < N then lp.single 2 j z else 0 := by
  by_cases hj : j < N
  · rw [if_pos hj]
    apply lp.ext
    funext n
    rw [paperCoordinateProjection_coordinate]
    by_cases hn : n < N
    · rw [if_pos hn]
    · rw [if_neg hn, lp.single_apply_ne _ _ _ (by omega : n ≠ j)]
  · rw [if_neg hj]
    apply lp.ext
    funext n
    rw [paperCoordinateProjection_coordinate]
    by_cases hn : n < N
    · rw [if_pos hn, lp.single_apply_ne _ _ _ (by omega : n ≠ j)]
      rfl
    · rw [if_neg hn]
      rfl

theorem norm_sub_paperCoordinateProjection_le (N : ℕ) (x : VecSeq E) :
    ‖x - paperCoordinateProjection N x‖ ≤ ‖x‖ := by
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro n
  simp only [lp.coeFn_sub, Pi.sub_apply, paperCoordinateProjection_coordinate]
  split_ifs <;> simp

theorem norm_paperCoordinateTail_le (N : ℕ) :
    ‖ContinuousLinearMap.id ℂ (VecSeq E) - paperCoordinateProjection N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [sub_apply, ContinuousLinearMap.id_apply, one_mul] using
    norm_sub_paperCoordinateProjection_le N x

theorem norm_sub_comp_paperCoordinateProjection_le (T : VecSeq E →L[ℂ] F) (N : ℕ) :
    ‖T - T ∘L paperCoordinateProjection N‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  rw [sub_apply, ContinuousLinearMap.comp_apply, ← map_sub]
  exact (T.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_sub_paperCoordinateProjection_le N x) (norm_nonneg T))

end
end GaloisForLFunctions.HTGeometry
