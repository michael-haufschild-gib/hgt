import GaloisForLFunctions.HTGeometry.HilbertFiniteProjectionCompact
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

/-! # Operator bounds for arbitrary Hilbert-basis truncations

No Hilbert--Schmidt hypothesis is required: a finite basis cutoff and its
complement are contractions on the domain of every bounded operator.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped InnerProductSpace
variable {E F I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem norm_sub_hilbertFiniteProjection_le (b : HilbertBasis I ℂ E)
    (s : Finset I) (x : E) : ‖x - hilbertFiniteProjection b s x‖ ≤ ‖x‖ := by
  have he : inner ℂ (hilbertFiniteProjection b s x) (hilbertFiniteProjection b s x) =
      inner ℂ (hilbertFiniteProjection b s x) x := by
    simp only [hilbertFiniteProjection_apply, sum_inner, inner_smul_left]
    apply Finset.sum_congr rfl
    intro i hi
    rw [b.orthonormal.inner_right_sum _ hi]
  have hn := norm_sub_sq (𝕜 := ℂ) (hilbertFiniteProjection b s x) x
  rw [← he, inner_self_eq_norm_sq, norm_sub_rev] at hn
  nlinarith [norm_nonneg x, norm_nonneg (x - hilbertFiniteProjection b s x),
    sq_nonneg ‖hilbertFiniteProjection b s x‖]

theorem hsTruncation_eq_comp_hilbertFiniteProjection (b : HilbertBasis I ℂ E)
    (T : E →L[ℂ] F) (s : Finset I) :
    T.hsTruncation b s = T ∘L hilbertFiniteProjection b s := by
  ext x
  simp only [ContinuousLinearMap.hsTruncation_apply, ContinuousLinearMap.comp_apply,
    hilbertFiniteProjection_apply, map_sum, map_smul]

theorem norm_hsTruncation_le_norm (b : HilbertBasis I ℂ E)
    (T : E →L[ℂ] F) (s : Finset I) : ‖T.hsTruncation b s‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  rw [hsTruncation_eq_comp_hilbertFiniteProjection, ContinuousLinearMap.comp_apply]
  exact (T.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (hilbertFiniteProjection_norm_le b s x) (norm_nonneg T))

theorem norm_sub_hsTruncation_le_norm (b : HilbertBasis I ℂ E)
    (T : E →L[ℂ] F) (s : Finset I) : ‖T - T.hsTruncation b s‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  rw [sub_apply, hsTruncation_eq_comp_hilbertFiniteProjection,
    ContinuousLinearMap.comp_apply, ← map_sub]
  exact (T.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_sub_hilbertFiniteProjection_le b s x) (norm_nonneg T))

end
end GaloisForLFunctions.HTGeometry
