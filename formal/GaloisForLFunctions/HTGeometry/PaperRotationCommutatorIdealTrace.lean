import GaloisForLFunctions.HTGeometry.PaperRotationWeylOperators
import GaloisForLFunctions.HTGeometry.PaperCompactIdealTrace

/-!
# Exact ideal-trace cost of rotation commutators

The paper's extended trace of a closed ideal measures the literal commutator of bilateral Weyl
words. Its cost is zero exactly when the signed-area phase is one, and infinity otherwise. The
operator norm is the ordinary distance of that phase from one. This separates exact compactness
from small commutation error without discarding the phase or replacing the operators by `K₀` data.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open LpDiagonal
open scoped ENNReal Classical

/-- The native bilateral Hilbert identity is not compact. -/
theorem paperRotation_identity_not_compact :
    ¬ IsCompactOperator (ContinuousLinearMap.id ℂ PaperRotationHilbert) := by
  have hinf : {n : ℤ | (Equiv.addRight (1 : ℤ)) n ≠ n}.Infinite := by
    have hs : {n : ℤ | (Equiv.addRight (1 : ℤ)) n ≠ n} = Set.univ := by
      ext n
      simp
    rw [hs]
    exact Set.infinite_univ
  intro h
  have hc := h.clm_comp (lpReindexDefect (Equiv.addRight (1 : ℤ)))
  apply not_isCompactOperator_lpReindexDefect_of_infinite _ hinf
  simpa using hc

/-- No nonzero scalar multiple of an invertible Weyl word can be compact. -/
theorem paperRotationWord_smul_compact_iff (a : ℤ) (b : ℝ) (z : ℂ) :
    IsCompactOperator (z • paperRotationWord a b) ↔ z = 0 := by
  constructor
  · intro h
    by_contra hz
    have hc := (h.clm_comp (paperRotationWordUndo a b)).smul z⁻¹
    have heq : z⁻¹ • (paperRotationWordUndo a b ∘L (z • paperRotationWord a b)) =
        ContinuousLinearMap.id ℂ PaperRotationHilbert := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [smul_apply, ContinuousLinearMap.comp_apply, map_smul,
        smul_smul, inv_mul_cancel₀ hz, one_smul]
      change (paperRotationWordUndo a b ∘L paperRotationWord a b) v = v
      rw [paperRotationWordUndo_left]
      rfl
    change IsCompactOperator
      (z⁻¹ • (paperRotationWordUndo a b ∘L (z • paperRotationWord a b))) at hc
    rw [heq] at hc
    exact paperRotation_identity_not_compact hc
  · rintro rfl
    rw [zero_smul]
    exact isCompactOperator_zero

/-- Literal difference between the two orders of a pair of Weyl words. -/
def paperRotationCommutator (a c : ℤ) (b d : ℝ) :
    PaperRotationHilbert →L[ℂ] PaperRotationHilbert :=
  paperRotationWord a b ∘L paperRotationWord c d -
    paperRotationWord c d ∘L paperRotationWord a b

/-- Exact scalar defect times the reversed unitary word. -/
theorem paperRotationCommutator_eq (a c : ℤ) (b d : ℝ) :
    paperRotationCommutator a c b d =
      (paperRotationPhase (c * b - a * d) - 1) •
        (paperRotationWord c d ∘L paperRotationWord a b) := by
  rw [paperRotationCommutator, paperRotationWord_commutation, sub_smul, one_smul]

theorem paperRotationCommutator_norm_apply (a c : ℤ) (b d : ℝ)
    (v : PaperRotationHilbert) :
    ‖paperRotationCommutator a c b d v‖ =
      ‖paperRotationPhase (c * b - a * d) - 1‖ * ‖v‖ := by
  rw [paperRotationCommutator_eq, smul_apply, norm_smul, ContinuousLinearMap.comp_apply,
    paperRotationWord_norm, paperRotationWord_norm]

/-- The exact operator norm retains the size of the commutation defect. -/
theorem paperRotationCommutator_norm (a c : ℤ) (b d : ℝ) :
    ‖paperRotationCommutator a c b d‖ = ‖paperRotationPhase (c * b - a * d) - 1‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      (fun v => (paperRotationCommutator_norm_apply a c b d v).le)
  · let v : PaperRotationHilbert := lp.single 2 (0 : ℤ) (1 : ℂ)
    have hv : ‖v‖ = 1 := by simp [v, lp.norm_single]
    simpa only [paperRotationCommutator_norm_apply, hv, mul_one] using
      ContinuousLinearMap.le_opNorm (paperRotationCommutator a c b d) v

/-- Compactness is equivalent to exact vanishing of the signed-area phase defect. -/
theorem paperRotationCommutator_compact_iff (a c : ℤ) (b d : ℝ) :
    IsCompactOperator (paperRotationCommutator a c b d) ↔
      paperRotationPhase (c * b - a * d) = 1 := by
  have hp : paperRotationPhase (-(c : ℝ) * b) ≠ 0 := by
    intro h
    have hn := paperRotationPhase_norm (-(c : ℝ) * b)
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  rw [paperRotationCommutator_eq, paperRotationWord_comp, smul_smul,
    paperRotationWord_smul_compact_iff, mul_eq_zero]
  simp only [hp, or_false, sub_eq_zero]

/-- The positive sharp boundary: every compact commutator in this family is already zero. -/
theorem paperRotationCommutator_compact_iff_zero (a c : ℤ) (b d : ℝ) :
    IsCompactOperator (paperRotationCommutator a c b d) ↔
      paperRotationCommutator a c b d = 0 := by
  constructor
  · intro h
    have hp := (paperRotationCommutator_compact_iff a c b d).mp h
    simp [paperRotationCommutator_eq, hp]
  · intro h
    rw [h]
    exact isCompactOperator_zero

/-- Direct application of the proven paper ideal-weight theorem to the actual commutator Gram. -/
theorem paperRotationCommutator_traceCost (a c : ℤ) (b d : ℝ) :
    compactOperatorTraceCost PaperRotationHilbert (paperRotationCommutator a c b d) =
      if paperRotationPhase (c * b - a * d) = 1 then 0 else ∞ := by
  rw [compactOperatorTraceCost_eq, paperRotationCommutator_compact_iff]

/-- Every compact correction has exactly the same extended trace cost. -/
theorem paperRotationCommutator_traceCost_add_compact (a c : ℤ) (b d : ℝ)
    (K : compactOperatorStarAlgebra PaperRotationHilbert) :
    compactOperatorTraceCost PaperRotationHilbert (paperRotationCommutator a c b d + K.1) =
      if paperRotationPhase (c * b - a * d) = 1 then 0 else ∞ := by
  rw [compactOperatorTraceCost_add_compact, paperRotationCommutator_traceCost]

end

end GaloisForLFunctions.HTGeometry
