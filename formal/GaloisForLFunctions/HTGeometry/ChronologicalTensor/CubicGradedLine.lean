import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicGradedDefect
import Mathlib.Analysis.Normed.Module.TransferInstance
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Hilbert lines from physical graded recovery costs

The quotient is given the transported real vector-space structure, and the
projection is proved to preserve the original addition and scalar action.
Its norm is exactly the attained infimum of physical representative norms.
The induced inner product makes each positive-weight defect a complete real
line; no topology on the ungraded quotient is asserted here.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial


def cubicGradedScaledEquiv (k : ℕ) : cubicGradedDefect k ≃ ℝ where
  toFun x := cubicGradedRecoveryGap k*cubicGradedDefectCoordinate k x
  invFun r := (cubicGradedDefectEquiv k).symm (r/cubicGradedRecoveryGap k)
  left_inv x := by
    apply (cubicGradedDefectEquiv k).injective
    change (cubicGradedDefectEquiv k) ((cubicGradedDefectEquiv k).symm
      (cubicGradedRecoveryGap k*cubicGradedDefectCoordinate k x/cubicGradedRecoveryGap k))=_
    rw [Equiv.apply_symm_apply]
    have hn := (cubicGradedRecoveryGap_positive k).ne'
    field_simp
    rfl
  right_inv r := by
    change cubicGradedRecoveryGap k*((cubicGradedDefectEquiv k)
      ((cubicGradedDefectEquiv k).symm (r/cubicGradedRecoveryGap k)))=r
    rw [Equiv.apply_symm_apply]
    have hn := (cubicGradedRecoveryGap_positive k).ne'
    field_simp

@[implicit_reducible]
def cubicGradedLineNormedGroup (k : ℕ) : NormedAddCommGroup (cubicGradedDefect k) :=
  (cubicGradedScaledEquiv k).normedAddCommGroup

@[implicit_reducible]
def cubicGradedLineNormedSpace (k : ℕ) :
    letI := cubicGradedLineNormedGroup k
    NormedSpace ℝ (cubicGradedDefect k) := by
  letI := cubicGradedLineNormedGroup k
  exact (cubicGradedScaledEquiv k).normedSpace ℝ

def cubicGradedLineLinearEquiv (k : ℕ) :
    letI := cubicGradedLineNormedGroup k
    letI := cubicGradedLineNormedSpace k
    cubicGradedDefect k ≃ₗ[ℝ] ℝ := by
  letI := cubicGradedLineNormedGroup k
  letI := cubicGradedLineNormedSpace k
  exact (cubicGradedScaledEquiv k).linearEquiv ℝ

theorem cubicGradedLine_norm (k : ℕ) (x : cubicGradedDefect k) :
    letI := cubicGradedLineNormedGroup k
    ‖x‖=cubicGradedDefectNorm k x := by
  letI := cubicGradedLineNormedGroup k
  change |cubicGradedRecoveryGap k*cubicGradedDefectCoordinate k x|=_
  rw [cubicGradedDefectNorm_eq,abs_mul,abs_of_pos (cubicGradedRecoveryGap_positive k)]
  ring

theorem cubicGradedLine_mk_add (k : ℕ) (P Q : cubicHomogeneousSpace (k+1)) :
    letI := cubicGradedLineNormedGroup k
    cubicGradedDefectMk k (P+Q)=cubicGradedDefectMk k P+cubicGradedDefectMk k Q := by
  letI := cubicGradedLineNormedGroup k
  letI := cubicGradedLineNormedSpace k
  apply (cubicGradedLineLinearEquiv k).injective
  rw [map_add]
  change cubicGradedRecoveryGap k*cubicGradedCoefficient k (P+Q)=
    cubicGradedRecoveryGap k*cubicGradedCoefficient k P+cubicGradedRecoveryGap k*cubicGradedCoefficient k Q
  rw [map_add,mul_add]

theorem cubicGradedLine_mk_smul (k : ℕ) (r : ℝ) (P : cubicHomogeneousSpace (k+1)) :
    letI := cubicGradedLineNormedGroup k
    letI := cubicGradedLineNormedSpace k
    cubicGradedDefectMk k (r • P)=r • cubicGradedDefectMk k P := by
  letI := cubicGradedLineNormedGroup k
  letI := cubicGradedLineNormedSpace k
  apply (cubicGradedLineLinearEquiv k).injective
  rw [map_smul]
  change cubicGradedRecoveryGap k*cubicGradedCoefficient k (r • P)=
    r*(cubicGradedRecoveryGap k*cubicGradedCoefficient k P)
  rw [map_smul,smul_eq_mul]
  ring


theorem cubicGradedLine_finrank (k : ℕ) :
    letI := cubicGradedLineNormedGroup k
    letI := cubicGradedLineNormedSpace k
    Module.finrank ℝ (cubicGradedDefect k)=1 := by
  letI := cubicGradedLineNormedGroup k
  letI := cubicGradedLineNormedSpace k
  rw [(cubicGradedLineLinearEquiv k).finrank_eq,CommSemiring.finrank_self]

theorem cubicGradedLine_complete (k : ℕ) :
    letI := cubicGradedLineNormedGroup k
    CompleteSpace (cubicGradedDefect k) := by
  letI := cubicGradedLineNormedGroup k
  letI := cubicGradedLineNormedSpace k
  letI := FiniteDimensional.of_injective (cubicGradedLineLinearEquiv k).toLinearMap
    (cubicGradedLineLinearEquiv k).injective
  exact FiniteDimensional.complete ℝ (cubicGradedDefect k)

@[implicit_reducible]
def cubicGradedLineInnerProductSpace (k : ℕ) :
    letI := cubicGradedLineNormedGroup k
    InnerProductSpace ℝ (cubicGradedDefect k) := by
  letI := cubicGradedLineNormedGroup k
  letI := cubicGradedLineNormedSpace k
  let e := cubicGradedLineLinearEquiv k
  exact {
    toNormedSpace := cubicGradedLineNormedSpace k
    inner := fun x y => e x * e y
    norm_sq_eq_re_inner := fun x => by
      change |e x| ^ 2 = e x * e x
      rw [sq_abs]
      ring
    conj_inner_symm := fun x y => by
      change e y * e x = e x * e y
      ring
    add_left := fun x y z => by
      rw [map_add,add_mul]
    smul_left := fun x y r => by
      change e (r • x)*e y=r*(e x*e y)
      rw [map_smul,smul_eq_mul]
      ring }

theorem cubicGradedLine_inner (k : ℕ) (x y : cubicGradedDefect k) :
    letI := cubicGradedLineNormedGroup k
    letI := cubicGradedLineInnerProductSpace k
    inner ℝ x y = (cubicGradedRecoveryGap k)^2 *
      cubicGradedDefectCoordinate k x * cubicGradedDefectCoordinate k y := by
  letI := cubicGradedLineNormedGroup k
  letI := cubicGradedLineInnerProductSpace k
  change (cubicGradedRecoveryGap k*cubicGradedDefectCoordinate k x)*
    (cubicGradedRecoveryGap k*cubicGradedDefectCoordinate k y)=_
  ring

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
