import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic

/-! # Quadratic longitudinal response of a split doublet -/
open Matrix Polynomial Finset
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section
variable {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]

/-- Determinant along the field perturbation, retaining the field strength as a formal variable. -/
def fieldDet (A B : Matrix I I R) : R[X] :=
  (A.map C + (X : R[X]) • B.map C).det

theorem eval_fieldDet (A B : Matrix I I R) (r : R) :
    (fieldDet A B).eval r = (A+r • B).det := by
  change (evalRingHom r) _ = _
  rw [fieldDet,RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  simp [RingHom.mapMatrix_apply,Matrix.map_apply,Matrix.smul_apply,smul_eq_mul]
  exact mul_comm _ _

private theorem quadratic_split (p : R[X]) (r : R) :
    p.eval r = p.coeff 0 + r*p.coeff 1 + r^2*p.divX.divX.eval r := by
  have h := congrArg (eval r) p.divX_mul_X_add
  have h' := congrArg (eval r) p.divX.divX_mul_X_add
  simp only [eval_add,eval_mul,eval_X,eval_C,coeff_divX,zero_add] at h h'
  rw [←h,←h']
  ring

/-- Averaging opposite fields removes the full linear term. The residual
has an everywhere-defined quotient by r², including at the unsplit point. -/
theorem symmetrized_quadratic (p : R[X]) (r : R) :
    p.eval r + p.eval (-r) = 2*p.coeff 0 +
      r^2*(p.divX.divX.eval r+p.divX.divX.eval (-r)) := by
  rw [quadratic_split p r,quadratic_split p (-r)]
  ring

theorem quadratic_at_zero (p : R[X]) : p.divX.divX.eval 0 = p.coeff 2 := by
  rw [←coeff_zero_eq_eval_zero,coeff_divX,coeff_divX]

private theorem diagonal_fieldDet (a b : I → R) :
    fieldDet (diagonal a) (diagonal b) = ∏ i, (C (a i)+X*C (b i)) := by
  unfold fieldDet
  have he : (diagonal a).map C + (X : R[X]) • (diagonal b).map C =
      diagonal (fun i => C (a i)+X*C (b i)) := by
    ext i j
    by_cases h : i=j
    · subst j
      simp [Matrix.smul_apply,smul_eq_mul]
    · simp [Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply_ne _ h]
  rw [he,Matrix.det_diagonal]

/-- At a complementary classical doublet the quadratic coefficient is
minus the squared longitudinal splitting times all spectator gaps. -/
theorem doublet_quadratic_coeff (a b : I → R) (s t : I) (hst : s≠t)
    (hs : a s=0) (ht : a t=0) (hb : b t= -b s) :
    (fieldDet (diagonal a) (diagonal b)).coeff 2 =
      -(b s)^2 * ∏ j ∈ (univ.erase s).erase t, a j := by
  rw [diagonal_fieldDet,←Finset.mul_prod_erase _ _ (mem_univ s),
    ←Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨hst.symm,mem_univ t⟩)]
  let P := ∏ j ∈ (univ.erase s).erase t, (C (a j)+X*C (b j))
  have he : (C (a s)+X*C (b s))*((C (a t)+X*C (b t))*P) =
      (C (-(b s)^2)*P)*X^2 := by
    rw [hs,ht,hb,map_zero,map_neg,map_neg,map_pow]
    ring
  change _ = -(b s)^2 * _
  rw [he]
  rw [show 2=0+2 by rfl,coeff_mul_X_pow,coeff_zero_eq_eval_zero,eval_mul,eval_C]
  simp only [P,Polynomial.eval_prod,eval_add,eval_mul,eval_X,eval_C,zero_mul,add_zero]

#print axioms symmetrized_quadratic
#print axioms doublet_quadratic_coeff
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
