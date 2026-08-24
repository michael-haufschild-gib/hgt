import GaloisForLFunctions.HTGeometry.FiniteBlaschkeLeakagePythagoras

open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Orthogonal projections are self-adjoint as continuous linear maps. -/
theorem adjoint_starProjection_eq_self (S : Submodule ℂ E)
    [S.HasOrthogonalProjection] : S.starProjection.adjoint = S.starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  refine ext_inner_right ℂ fun y => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (S.starProjection_isSymmetric x y).symm

/-- Orthogonal projections are idempotent as continuous linear maps. -/
theorem starProjection_comp_self_eq_self (S : Submodule ℂ E)
    [S.HasOrthogonalProjection] :
    S.starProjection.comp S.starProjection = S.starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  change S.starProjection (S.starProjection x) = S.starProjection x
  exact S.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem x)

/-- Complement of an orthogonal projection is contractive. -/
theorem norm_id_sub_starProjection_le_one (S : Submodule ℂ E)
    [S.HasOrthogonalProjection] :
    ‖ContinuousLinearMap.id ℂ E - S.starProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x - S.starProjection x‖ ≤ 1 * ‖x‖
  have hsplit := S.starProjection_add_starProjection_orthogonal x
  have hres : x - S.starProjection x =
      (Submodule.orthogonal S).starProjection x := by
    calc
      x - S.starProjection x =
          (S.starProjection x + (Submodule.orthogonal S).starProjection x) -
            S.starProjection x :=
        congrArg (fun z => z - S.starProjection x) hsplit.symm
      _ = (Submodule.orthogonal S).starProjection x := by abel
  rw [hres, one_mul]
  calc
    ‖(Submodule.orthogonal S).starProjection x‖ ≤
        ‖(Submodule.orthogonal S).starProjection‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right
      (Submodule.orthogonal S).starProjection_norm_le (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-- Compression of a Gram operator to an orthogonal channel, minus its projection. -/
def channelGramDefect (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (L : E →L[ℂ] F) : E →L[ℂ] E :=
  (S.starProjection.comp (L.adjoint.comp L)).comp S.starProjection - S.starProjection

/-- Block from one orthogonal channel into its complement. -/
def channelOffDiagonalGram (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (L : E →L[ℂ] F) : E →L[ℂ] E :=
  ((ContinuousLinearMap.id ℂ E - S.starProjection).comp
    (L.adjoint.comp L)).comp S.starProjection

/-- Exact channel defect: under `L†L + T†T = I`, lost `L`-Gram is the negative causal Gram. -/
theorem channelGramDefect_eq_neg_adjoint_comp
    (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (L : E →L[ℂ] F) (T : E →L[ℂ] G)
    (hgram : L.adjoint.comp L + T.adjoint.comp T = ContinuousLinearMap.id ℂ E) :
    channelGramDefect S L = -((T.comp S.starProjection).adjoint.comp
      (T.comp S.starProjection)) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [channelGramDefect, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_comp, adjoint_starProjection_eq_self,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  have hx := congrArg (fun R : E →L[ℂ] E => R (S.starProjection x)) hgram
  change L.adjoint (L (S.starProjection x)) +
      T.adjoint (T (S.starProjection x)) = S.starProjection x at hx
  have hqsum :
      S.starProjection (L.adjoint (L (S.starProjection x))) +
          S.starProjection (T.adjoint (T (S.starProjection x))) =
        S.starProjection x := by
    rw [← map_add, hx]
    exact S.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem x)
  calc
    S.starProjection (L.adjoint (L (S.starProjection x))) - S.starProjection x =
        S.starProjection (L.adjoint (L (S.starProjection x))) -
          (S.starProjection (L.adjoint (L (S.starProjection x))) +
            S.starProjection (T.adjoint (T (S.starProjection x)))) :=
      congrArg (fun z =>
        S.starProjection (L.adjoint (L (S.starProjection x))) - z) hqsum.symm
    _ = -S.starProjection (T.adjoint (T (S.starProjection x))) := by abel

/-- Exact off-diagonal defect: the complementary `L` block is the negative causal cross block. -/
theorem channelOffDiagonalGram_eq_neg_causal
    (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (L : E →L[ℂ] F) (T : E →L[ℂ] G)
    (hgram : L.adjoint.comp L + T.adjoint.comp T = ContinuousLinearMap.id ℂ E) :
    channelOffDiagonalGram S L =
      -((ContinuousLinearMap.id ℂ E - S.starProjection).comp
        (T.adjoint.comp (T.comp S.starProjection))) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [channelOffDiagonalGram, neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  let R : E →L[ℂ] E := ContinuousLinearMap.id ℂ E - S.starProjection
  have hx := congrArg (fun U : E →L[ℂ] E => U (S.starProjection x)) hgram
  change L.adjoint (L (S.starProjection x)) +
      T.adjoint (T (S.starProjection x)) = S.starProjection x at hx
  have hRzero : R (S.starProjection x) = 0 := by
    change S.starProjection x - S.starProjection (S.starProjection x) = 0
    rw [S.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem x), sub_self]
  have hRsum :
      R (L.adjoint (L (S.starProjection x))) +
          R (T.adjoint (T (S.starProjection x))) = 0 := by
    rw [← map_add, hx, hRzero]
  change R (L.adjoint (L (S.starProjection x))) =
    -R (T.adjoint (T (S.starProjection x)))
  exact eq_neg_of_add_eq_zero_left hRsum

/-- Channel Gram defect norm is exactly the square of causal compression norm on that channel. -/
theorem norm_channelGramDefect_eq_sq
    (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (L : E →L[ℂ] F) (T : E →L[ℂ] G)
    (hgram : L.adjoint.comp L + T.adjoint.comp T = ContinuousLinearMap.id ℂ E) :
    ‖channelGramDefect S L‖ =
      ‖T.comp S.starProjection‖ * ‖T.comp S.starProjection‖ := by
  rw [channelGramDefect_eq_neg_adjoint_comp S L T hgram, norm_neg,
    ContinuousLinearMap.norm_adjoint_comp_self]

/-- Off-diagonal leakage block is bounded by causal channel norm when the causal map contracts. -/
theorem norm_channelOffDiagonalGram_le
    (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (L : E →L[ℂ] F) (T : E →L[ℂ] G)
    (hgram : L.adjoint.comp L + T.adjoint.comp T = ContinuousLinearMap.id ℂ E)
    (hT : ‖T‖ ≤ 1) :
    ‖channelOffDiagonalGram S L‖ ≤ ‖T.comp S.starProjection‖ := by
  rw [channelOffDiagonalGram_eq_neg_causal S L T hgram, norm_neg]
  let R : E →L[ℂ] E := ContinuousLinearMap.id ℂ E - S.starProjection
  let C : E →L[ℂ] G := T.comp S.starProjection
  calc
    ‖R.comp (T.adjoint.comp C)‖ ≤ ‖R‖ * ‖T.adjoint.comp C‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖T.adjoint‖ * ‖C‖) := by
      gcongr
      · exact norm_id_sub_starProjection_le_one S
      · exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖T‖ * ‖C‖ := by rw [one_mul, LinearIsometryEquiv.norm_map]
    _ ≤ 1 * ‖C‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg C)
    _ = ‖T.comp S.starProjection‖ := by simp [C]

end GaloisForLFunctions.HTGeometry
