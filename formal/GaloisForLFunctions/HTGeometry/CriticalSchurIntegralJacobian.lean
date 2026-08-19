import GaloisForLFunctions.HTGeometry.CriticalSchurSourceIntegralModels
import GaloisForLFunctions.HTGeometry.CriticalSchurUniformizer

/-!
# The integral model of the reciprocal Jacobian determinant

The reciprocal Jacobian of the integral reciprocal truncation maps entrywise to the reciprocal
Jacobian over the source field, so its determinant is the lifted Jacobian determinant element —
which is a uniformizer of the source Schur valuation ring, hence not a unit.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial Matrix

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

variable (K : Type*) [Field K] [CharZero K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)

theorem map_criticalReciprocalJacobianIntegral :
    (criticalReciprocalJacobian (criticalSourceRecipPolynomialIntegral K hm hn) n m).map
        (criticalSchurSourceValuationSubring K hm hn).subtype
      = criticalReciprocalJacobian (criticalSourceReciprocalPolynomial K m n) n m := by
  ext r i
  rw [Matrix.map_apply, criticalReciprocalJacobian_apply, criticalReciprocalJacobian_apply,
    ← map_criticalSourceRecipPolynomialIntegral K hm hn]
  simp only [rectangularSchurToeplitz, map_neg, apply_ite
    (f := (criticalSchurSourceValuationSubring K hm hn).subtype)]
  congr 1
  by_cases hle : (i : ℕ) ≤ n + (r : ℕ)
  · rw [if_pos hle, if_pos hle, ← Polynomial.map_mul, Polynomial.coeff_map]
  · rw [if_neg hle, if_neg hle, map_zero]

theorem det_criticalReciprocalJacobianIntegral :
    (criticalReciprocalJacobian (criticalSourceRecipPolynomialIntegral K hm hn) n m).det
      = criticalSchurJacobianDetElement K hm hn := by
  apply Subtype.val_injective
  rw [coe_criticalSchurJacobianDetElement K hm hn,
    ← map_criticalReciprocalJacobianIntegral K hm hn]
  exact RingHom.map_det (criticalSchurSourceValuationSubring K hm hn).subtype _

end

end GaloisForLFunctions.HTGeometry
