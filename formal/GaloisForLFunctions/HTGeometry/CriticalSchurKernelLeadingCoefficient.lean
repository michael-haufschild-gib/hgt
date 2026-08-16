import GaloisForLFunctions.HTGeometry.CorankOneKernelSupport
import GaloisForLFunctions.HTGeometry.CriticalSchurGenericCorank

/-!
# The generic Schur kernel has a nonvanishing leading coordinate

Generic corank one says the kernel of the normalized critical Jacobian is a line; the corner
cofactor says one adjugate entry survives at the generic point of the Schur divisor.  Together, by
`ker_coord_ne_zero_of_adjugate_ne_zero`, every nonzero kernel vector has a nonzero entry in the
coordinate matched to that cofactor.

The corpus states the cofactor as the determinant of the submatrix obtained by deleting the last row
and the first column; mathlib's `adjugate_fin_succ_eq_det_submatrix` identifies that, up to a sign,
with the adjugate entry at `(0, last)`.  The sign is a unit, so it does not affect vanishing.
-/

noncomputable section

open Matrix

namespace GaloisForLFunctions.HTGeometry

/-- **The leading coordinate of a generic Schur kernel vector does not vanish.**  Every nonzero
kernel vector of the normalized critical Jacobian at the generic point of the Schur divisor has a
nonzero zeroth coordinate. -/
theorem criticalSchurGeneric_ker_coord_zero_ne_zero
    (K : Type*) [Field K] {n' m' : ℕ} (hn : 0 < n') (hm : 0 < m') : by
    letI : IsDomain (criticalSchurTailDivisorRing K n' m') :=
      (Ideal.Quotient.isDomain_iff_prime _).mpr
        (criticalSchurTailIdeal_isPrime K hn hm)
    exact ∀ v : Fin (m' + 1) → criticalSchurTailDivisorField K n' m',
      (criticalSchurGenericMatrix K hn hm).mulVec v = 0 → v ≠ 0 → v 0 ≠ 0 := by
  classical
  letI : IsDomain (criticalSchurTailDivisorRing K n' m') :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr
      (criticalSchurTailIdeal_isPrime K hn hm)
  intro v hv hvne
  refine ker_coord_ne_zero_of_adjugate_ne_zero (j := Fin.last m')
    (finrank_ker_criticalSchurGenericMatrix_eq_one K hn hm) hv hvne ?_
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hc := criticalSchurGenericMatrix_cornerCofactor_ne_zero K hn hm
  simp only [Fin.succAbove_zero]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hc

end GaloisForLFunctions.HTGeometry

end
