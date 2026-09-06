import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicCuspMultiplier
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The bounded recovery shift on the physical defect Hilbert completion

The unique bounded extension of actual multiplication by u has norm at most
one quarter. Its positive basis weights are exactly successive optimal recovery
gap ratios. It obeys the physical covariance T_q U = q U T_q on the completion.
-/


namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial
attribute [local instance] cubicGradedLineNormedGroup cubicGradedLineInnerProductSpace
  cubicGradedLine_complete

def cubicHilbertRecoveryShift : cubicDefectHilbert →L[ℝ] cubicDefectHilbert :=
  (cubicDefectHilbertEmbedding.comp cubicCuspDefectMultiplyFirst).extendOfNorm
    cubicDefectHilbertEmbedding

theorem cubicHilbertRecoveryShift_extension
    (x : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :
    cubicHilbertRecoveryShift (cubicDefectHilbertEmbedding x)=
      cubicDefectHilbertEmbedding (cubicCuspDefectMultiplyFirst x) :=
  LinearMap.extendOfNorm_eq cubicDefectHilbertEmbedding_denseRange
    ⟨1/4,cubicCuspDefectMultiplyFirst_bound⟩ x

theorem cubicHilbertRecoveryShift_polynomial (P : Polynomial (Polynomial ℝ)) :
    cubicHilbertRecoveryShift (cubicDefectHilbertEmbedding (Submodule.Quotient.mk P))=
      cubicDefectHilbertEmbedding (Submodule.Quotient.mk (Polynomial.C Polynomial.X*P)) := by
  rw [cubicHilbertRecoveryShift_extension,cubicCuspDefectMultiplyFirst_mk]

theorem cubicHilbertRecoveryShift_bound (x : cubicDefectHilbert) :
    ‖cubicHilbertRecoveryShift x‖ ≤ (1/4:ℝ)*‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le cubicDefectHilbertEmbedding_denseRange (1/4)
    cubicCuspDefectMultiplyFirst_bound x

theorem cubicHilbertRecoveryShift_opNorm : ‖cubicHilbertRecoveryShift‖ ≤ (1/4:ℝ) :=
  LinearMap.opNorm_extendOfNorm_le cubicDefectHilbertEmbedding_denseRange (by positivity)
    cubicCuspDefectMultiplyFirst_bound

theorem cubicHilbertRecoveryShift_unique (F : cubicDefectHilbert →L[ℝ] cubicDefectHilbert) :
    (∀ x, F (cubicDefectHilbertEmbedding x)=
      cubicDefectHilbertEmbedding (cubicCuspDefectMultiplyFirst x)) ↔ F=cubicHilbertRecoveryShift := by
  constructor
  · intro h
    have he := cubicDefectHilbertEmbedding_denseRange.equalizer F.continuous
      cubicHilbertRecoveryShift.continuous (by
        funext x
        change F (cubicDefectHilbertEmbedding x)=cubicHilbertRecoveryShift (cubicDefectHilbertEmbedding x)
        rw [h x,cubicHilbertRecoveryShift_extension])
    exact DFunLike.coe_injective he
  · intro h
    subst F
    exact cubicHilbertRecoveryShift_extension

theorem cubicDefectHilbertEmbedding_scaled_basis (k : ℕ) :
    cubicDefectHilbertEmbedding (cubicCuspDefectBasis k)=
      cubicGradedRecoveryGap k • cubicHilbertBasis k := by
  rw [cubicDefectHilbertEmbedding_basis,cubicHilbertBasis_apply]
  have hscale : cubicGradedScaledEquiv k (cubicGradedDefectMk k (cubicHomogeneousMissing k))=
      cubicGradedRecoveryGap k := by
    change cubicGradedRecoveryGap k*cubicGradedCoefficient k (cubicHomogeneousMissing k)=_
    rw [cubicGradedCoefficient_missing,mul_one]
  have hs := cubicHilbertUnitGrade_spans k (cubicGradedDefectMk k (cubicHomogeneousMissing k))
  rw [hscale] at hs
  change lp.single 2 k (cubicGradedDefectMk k (cubicHomogeneousMissing k))=
    cubicGradedRecoveryGap k • lp.single 2 k (cubicHilbertUnitGrade k)
  rw [← lp.single_smul,hs]

def cubicRecoveryShiftWeight (k : ℕ) : ℝ :=
  cubicGradedRecoveryGap (k+1)/cubicGradedRecoveryGap k

theorem cubicRecoveryShiftWeight_bounds (k : ℕ) :
    0<cubicRecoveryShiftWeight k ∧ cubicRecoveryShiftWeight k ≤ 1/4 := by
  unfold cubicRecoveryShiftWeight
  refine ⟨div_pos (cubicGradedRecoveryGap_positive _) (cubicGradedRecoveryGap_positive _),?_⟩
  apply (div_le_iff₀ (cubicGradedRecoveryGap_positive k)).mpr
  linarith [(cubicGradedRecoveryGap_successor_bound k).2]

theorem cubicHilbertRecoveryShift_basis (k : ℕ) :
    cubicHilbertRecoveryShift (cubicHilbertBasis k)=
      cubicRecoveryShiftWeight k • cubicHilbertBasis (k+1) := by
  have h := cubicHilbertRecoveryShift_extension (cubicCuspDefectBasis k)
  rw [cubicCuspDefectMultiplyFirst_basis,cubicDefectHilbertEmbedding_scaled_basis,
    cubicDefectHilbertEmbedding_scaled_basis,map_smul] at h
  have he := congrArg (fun x : cubicDefectHilbert => (cubicGradedRecoveryGap k)⁻¹ • x) h
  rw [smul_smul,inv_mul_cancel₀ (ne_of_gt (cubicGradedRecoveryGap_positive k)),one_smul,
    smul_smul] at he
  rw [he,cubicRecoveryShiftWeight,div_eq_mul_inv,mul_comm]

theorem cubicHilbertRecoveryShift_flow (q : Icc (0:ℝ) 1) (x : cubicDefectHilbert) :
    cubicHilbertFlow q (cubicHilbertRecoveryShift x)=
      q.val • cubicHilbertRecoveryShift (cubicHilbertFlow q x) := by
  let F := (cubicHilbertFlow q).comp cubicHilbertRecoveryShift
  let G := q.val • cubicHilbertRecoveryShift.comp (cubicHilbertFlow q)
  have he := cubicDefectHilbertEmbedding_denseRange.equalizer F.continuous G.continuous (by
    funext y
    change cubicHilbertFlow q (cubicHilbertRecoveryShift (cubicDefectHilbertEmbedding y))=
      q.val • cubicHilbertRecoveryShift (cubicHilbertFlow q (cubicDefectHilbertEmbedding y))
    rw [cubicHilbertRecoveryShift_extension,cubicHilbertFlow_extension,
      cubicHilbertFlow_extension,cubicHilbertRecoveryShift_extension,
      cubicCuspDefectMultiplyFirst_flow,map_smul])
  exact congrFun he x

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
