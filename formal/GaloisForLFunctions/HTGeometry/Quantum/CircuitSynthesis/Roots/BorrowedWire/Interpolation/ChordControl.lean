import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-! # Unitary interpolation from a nearly self-adjoint chord -/

open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.BorrowedWire.Interpolation
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- In the frame of a candidate unitary, the skew part of a chord X
measures its angular error. The larger self-adjoint sag enters only
as a factor on the unknown distance. -/
theorem chord_control (U : unitary (Mat I)) (X : Mat I) :
    (2-‖X-1‖)*‖(U:Mat I)-1‖ ≤ 2*‖(U:Mat I)-X‖+‖star X-X‖ := by
  let V : Mat I := U
  have hU : star V*V=1 := (Unitary.mem_iff.mp U.property).1
  have hnorm : ‖V‖=1 := CStarRing.norm_coe_unitary U
  have hid : (2:ℝ) • (V-1) = ((V-X)+(star X-star V)*V)-(star X-X)-(star X-1)*(V-1) := by
    rw [two_smul]
    calc
      _ = ((V-X)+(star X-star V)*V)-(star X-X)-(star X-1)*(V-1)+(star V*V-1) := by noncomm_ring
      _ = _ := by rw [hU,sub_self,add_zero]
  have hd : ‖(star X-star V)*V‖≤‖V-X‖ := by
    apply (norm_mul_le ..).trans_eq
    rw [hnorm,mul_one,←star_sub,norm_star,norm_sub_rev]
  have hlast : ‖(star X-1)*(V-1)‖≤‖X-1‖*‖V-1‖ := by
    apply (norm_mul_le ..).trans_eq
    rw [show star X-1=star (X-1) by rw [star_sub,star_one],norm_star]
  have h :=
    (norm_sub_le (((V-X)+(star X-star V)*V)-(star X-X)) ((star X-1)*(V-1))).trans
      (add_le_add ((norm_sub_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl hd)) le_rfl)) hlast)
  rw [←hid,norm_smul,Real.norm_of_nonneg zero_le_two] at h
  change (2-‖X-1‖)*‖V-1‖≤2*‖V-X‖+‖star X-X‖
  linarith only [h]

/-- The bounds needed for the physical 9/80 crossing leave a
fixed positive allowance for synthesizing the interpolating circuit. -/
theorem physical_chord_margin (U : unitary (Mat I)) (X : Mat I)
    (hd : ‖(U:Mat I)-X‖≤53/500) (hs : ‖X-1‖≤24/1000)
    (hi : ‖star X-X‖≤1/300) : ‖(U:Mat I)-1‖+1/400<9/80 := by
  have h := chord_control U X
  have hl := mul_le_mul_of_nonneg_right hs (norm_nonneg ((U:Mat I)-1))
  linarith only [h,hl,hd,hi]

#print axioms chord_control
#print axioms physical_chord_margin
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.BorrowedWire.Interpolation
