import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.PositiveDiagonal

/-! # Real expectations of the Gram error in an arbitrary orthonormal basis -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections.Rounding
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ
local instance : CStarAlgebra (Mat I) where

/-- Real part of the expectation in column i. -/
def reading (V : unitaryGroup I ℂ) (i : I) : Mat I →ₗ[ℝ] ℝ where
  toFun X := ((star V.val*X*V.val) i i).re
  map_add' X Y := by simp only [Matrix.mul_add,Matrix.add_mul,Matrix.add_apply,Complex.add_re]
  map_smul' r X := by simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_apply,Complex.real_smul,
    Complex.re_ofReal_mul,RingHom.id_apply,smul_eq_mul]

theorem reading_one (V : unitaryGroup I ℂ) (i : I) : reading V i 1=1 := by
  change ((star V.val*1*V.val) i i).re=1
  rw [mul_one,(Unitary.mem_iff.mp V.property).1,Matrix.one_apply_eq,Complex.one_re]

theorem reading_star (V : unitaryGroup I ℂ) (i : I) (X : Mat I) : reading V i (star X)=reading V i X := by
  have h : star V.val*star X*V.val=star (star V.val*X*V.val) := by
    simp only [star_mul,star_star,mul_assoc]
  change ((star V.val*star X*V.val) i i).re=_
  rw [h]
  exact Complex.conj_re _

theorem reading_le_norm (V : unitaryGroup I ℂ) (i : I) (X : Mat I) : reading V i X≤‖X‖ := by
  apply (Complex.re_le_norm _).trans ((norm_entry_le_l2_opNorm _ i i).trans_eq ?_)
  simpa only [star_star] using l2_opNorm_unitary_conj_eq (Unitary.star_mem V.property) X

/-- A squared unitary error bounds the real overlap in every test column. -/
theorem column_error (V : unitaryGroup I ℂ) (i : I) (W D : Mat I)
    (hW : W∈unitary (Mat I)) (hD : D∈unitary (Mat I)) :
    2-2*reading V i (star W*D) ≤ ‖D-W‖^2 := by
  let X := D-W
  have hG : star X*X = 1+1-star (star W*D)-star W*D := by
    dsimp only [X]
    rw [star_mul,star_star,star_sub,sub_mul,mul_sub,mul_sub,(Unitary.mem_iff.mp hW).1,(Unitary.mem_iff.mp hD).1]
    abel
  have h := reading_le_norm V i (star X*X)
  rw [CStarRing.norm_star_mul_self,←sq,hG,map_sub,map_sub,map_add,reading_one,reading_star] at h
  linarith only [h]

/-- Testing after conjugation by a self-adjoint unitary changes the basis
of the test and leaves the error estimate available in that basis. -/
theorem reading_conjugate (S V : unitaryGroup I ℂ) (i : I) (X : Mat I) :
    reading V i (star S.val*X*S.val)=reading (S*V) i X := by
  change ((star V.val*(star S.val*X*S.val)*V.val) i i).re =
    ((star (S.val*V.val)*X*(S.val*V.val)) i i).re
  simp only [star_mul,mul_assoc]

#print axioms column_error
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections.Rounding
