import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-! # An invertible matrix of anchored differences gives a full energy matrix -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- If subtracting the anchor column gives a nonsingular square matrix,
adjoining a row of ones to the original matrix gives a nonsingular matrix. -/
theorem det_cons_one_ne_zero {d : ℕ} (R : Matrix (Fin d) (Fin (d+1)) ℂ)
    (hr : (Matrix.of fun i j => R i j.succ - R i 0).det ≠ 0) :
    (Matrix.of (Fin.cons (fun _ => (1:ℂ)) R)).det ≠ 0 := by
  intro hdet
  obtain ⟨v,hv,he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hsum : v 0 + ∑ j : Fin d, v j.succ = 0 := by
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using congrFun he 0
  have hrow (i : Fin d) : R i 0*v 0 + ∑ j : Fin d, R i j.succ*v j.succ = 0 := by
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using congrFun he i.succ
  have htail : (fun j : Fin d => v j.succ) = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero hr
    funext i
    change ∑ j : Fin d, (R i j.succ - R i 0)*v j.succ = 0
    simp_rw [sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum]
    linear_combination hrow i - R i 0 * hsum
  have hzero : v 0 = 0 := by
    simpa only [show ∀ j : Fin d, v j.succ = 0 from congrFun htail,Finset.sum_const_zero,add_zero]
      using hsum
  exact hv (funext fun j => Fin.cases hzero (congrFun htail) j)

end
end GaloisForLFunctions.HTGeometry.SpectralJets
