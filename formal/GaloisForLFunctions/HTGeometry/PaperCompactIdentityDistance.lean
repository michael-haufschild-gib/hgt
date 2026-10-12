import GaloisForLFunctions.HTGeometry.CompactCofinalEssentialMargin
import GaloisForLFunctions.HTGeometry.CompactOperatorBoundedBelow

/-! # Exact quotient distance of identity plus any compact correction

On every infinite-dimensional complex Banach space the distance of identity to
compact operators is one. The statement permits arbitrary compact corrections.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem compactIdealDistance_add_compact (T K : E →L[ℂ] F) (hK : IsCompactOperator K) :
    compactIdealDistance (T + K) = compactIdealDistance T := by
  apply le_antisymm
  · apply le_compactIdealDistance
    intro L hL
    have h := compactIdealDistance_le (T + K) (L + K) (hL.add hK)
    simpa only [add_sub_add_right_eq_sub] using h
  · apply le_compactIdealDistance
    intro L hL
    have h := compactIdealDistance_le T (L - K) (hL.sub hK)
    convert h using 1
    congr 1
    abel

theorem compactIdealDistance_sub_compact (T K : E →L[ℂ] F) (hK : IsCompactOperator K) :
    compactIdealDistance (T - K) = compactIdealDistance T := by
  simpa only [sub_eq_add_neg] using compactIdealDistance_add_compact T (-K) hK.neg

variable [CompleteSpace E]

theorem one_le_norm_identity_sub_compact
    (hinfinite : ¬ FiniteDimensional ℂ E) (K : E →L[ℂ] E) (hK : IsCompactOperator K) :
    1 ≤ ‖1 - K‖ := by
  by_contra h
  have hc : 0 < 1 - ‖1 - K‖ := sub_pos.2 (lt_of_not_ge h)
  have hbdd : ∀ x ∈ (⊤ : Submodule ℂ E), (1 - ‖1 - K‖) * ‖x‖ ≤ ‖K x‖ := by
    intro x _
    have hnorm := (1 - K).le_opNorm x
    change ‖x - K x‖ ≤ ‖1 - K‖ * ‖x‖ at hnorm
    have htri := norm_add_le (x - K x) (K x)
    rw [sub_add_cancel] at htri
    nlinarith
  letI := finiteDimensional_of_isCompactOperator_of_bounded_below hK ⊤
    (by simp) hc hbdd
  exact hinfinite (FiniteDimensional.of_surjective
    (Submodule.topEquiv : (⊤ : Submodule ℂ E) ≃ₗ[ℂ] E).toLinearMap
    (Submodule.topEquiv : (⊤ : Submodule ℂ E) ≃ₗ[ℂ] E).surjective)

theorem compactIdealDistance_identity (hinfinite : ¬ FiniteDimensional ℂ E) :
    compactIdealDistance (1 : E →L[ℂ] E) = 1 := by
  apply le_antisymm
  · have h := compactIdealDistance_le (1 : E →L[ℂ] E) 0 isCompactOperator_zero
    have h' : compactIdealDistance (1 : E →L[ℂ] E) ≤ ‖(1 : E →L[ℂ] E)‖ := by
      simpa only [sub_zero] using h
    exact h'.trans ContinuousLinearMap.norm_id_le
  · exact le_compactIdealDistance 1 1 (one_le_norm_identity_sub_compact hinfinite)

theorem compactIdealDistance_identity_sub (hinfinite : ¬ FiniteDimensional ℂ E)
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) : compactIdealDistance (1 - K) = 1 := by
  rw [compactIdealDistance_sub_compact _ _ hK, compactIdealDistance_identity hinfinite]

end GaloisForLFunctions.HTGeometry
