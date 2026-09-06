import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicHilbertShift
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The nonzero self-commutator of physical multiplication

The actual Hilbert recovery shift has a backward weighted adjoint. Its
self-commutator is diagonal with the initial squared weight and subsequent
differences of squared weights. The positive initial weight proves that the
commutator is nonzero and physical multiplication is not normal.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial
attribute [local instance] cubicGradedLineNormedGroup cubicGradedLineInnerProductSpace
  cubicGradedLine_complete


theorem cubicHilbertBasis_inner (i j : ℕ) :
    inner ℝ (cubicHilbertBasis i) (cubicHilbertBasis j)=if i=j then 1 else 0 :=
  (orthonormal_iff_ite.mp cubicHilbertBasis.orthonormal) i j

theorem cubicHilbertRecoveryShift_adjoint_zero :
    cubicHilbertRecoveryShift.adjoint (cubicHilbertBasis 0)=0 := by
  apply cubicHilbertBasis.repr.injective
  apply lp.ext
  funext j
  rw [map_zero cubicHilbertBasis.repr,HilbertBasis.repr_apply_apply]
  change inner ℝ (cubicHilbertBasis j)
    (cubicHilbertRecoveryShift.adjoint (cubicHilbertBasis 0))=0
  rw [ContinuousLinearMap.adjoint_inner_right,cubicHilbertRecoveryShift_basis,
    real_inner_smul_left,cubicHilbertBasis_inner]
  simp

theorem cubicHilbertRecoveryShift_adjoint_successor (k : ℕ) :
    cubicHilbertRecoveryShift.adjoint (cubicHilbertBasis (k+1))=
      cubicRecoveryShiftWeight k • cubicHilbertBasis k := by
  apply cubicHilbertBasis.repr.injective
  apply lp.ext
  funext j
  rw [HilbertBasis.repr_apply_apply,HilbertBasis.repr_apply_apply,
    ContinuousLinearMap.adjoint_inner_right,cubicHilbertRecoveryShift_basis,
    real_inner_smul_left,real_inner_smul_right,cubicHilbertBasis_inner,cubicHilbertBasis_inner]
  by_cases hj : j=k
  · subst j; simp
  · simp [hj]

def cubicRecoveryCommutator : cubicDefectHilbert →L[ℝ] cubicDefectHilbert :=
  cubicHilbertRecoveryShift.adjoint.comp cubicHilbertRecoveryShift-
    cubicHilbertRecoveryShift.comp cubicHilbertRecoveryShift.adjoint

theorem cubicRecoveryCommutator_zero_basis :
    cubicRecoveryCommutator (cubicHilbertBasis 0)=
      (cubicRecoveryShiftWeight 0)^2 • cubicHilbertBasis 0 := by
  simp only [cubicRecoveryCommutator,sub_apply,ContinuousLinearMap.comp_apply,
    cubicHilbertRecoveryShift_basis,map_smul,cubicHilbertRecoveryShift_adjoint_successor,
    cubicHilbertRecoveryShift_adjoint_zero,map_zero,sub_zero,smul_smul,pow_two]

theorem cubicRecoveryCommutator_successor_basis (k : ℕ) :
    cubicRecoveryCommutator (cubicHilbertBasis (k+1))=
      ((cubicRecoveryShiftWeight (k+1))^2-(cubicRecoveryShiftWeight k)^2) •
        cubicHilbertBasis (k+1) := by
  simp only [cubicRecoveryCommutator,sub_apply,ContinuousLinearMap.comp_apply,
    cubicHilbertRecoveryShift_basis,map_smul,cubicHilbertRecoveryShift_adjoint_successor,
    smul_smul,pow_two,sub_smul]

theorem cubicRecoveryCommutator_nonzero : cubicRecoveryCommutator≠0 := by
  intro hz
  have h := congrArg (fun T : cubicDefectHilbert →L[ℝ] cubicDefectHilbert =>
    ‖T (cubicHilbertBasis 0)‖) hz
  rw [cubicRecoveryCommutator_zero_basis,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _),cubicHilbertBasis.orthonormal.1, mul_one] at h
  simp only [zero_apply,norm_zero] at h
  nlinarith [(cubicRecoveryShiftWeight_bounds 0).1]

theorem cubicHilbertRecoveryShift_nonnormal :
    cubicHilbertRecoveryShift.adjoint.comp cubicHilbertRecoveryShift≠
      cubicHilbertRecoveryShift.comp cubicHilbertRecoveryShift.adjoint := by
  intro h
  apply cubicRecoveryCommutator_nonzero
  exact sub_eq_zero.mpr h

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
