import GaloisForLFunctions.HTGeometry.Critical.Schur.JacobianDivisor
import GaloisForLFunctions.HTGeometry.SchurCofactorLocus
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Generic corank one on the actual Schur ramification divisor

For positive `n'` and `m'`, the actual horizon dimensions are `n'+1` and `m'+1`.  We pass the
universal normalized reciprocal-square Toeplitz matrix to the function field of its irreducible
determinant divisor.  Its determinant vanishes there, while its corner cofactor survives.  Hence
the generic Jacobian has corank exactly one.

`CriticalSchurJacobianDivisor` identifies this normalized matrix with the concrete reciprocal
Jacobian up to a nonzero scalar, so this is the generic-corank statement for the actual cover.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial Matrix


/-- Coordinate ring for the positive rectangular-Schur tail matrix of shape
`(n'+1) × (m'+1)`. -/
abbrev criticalSchurTailRing (K : Type*) [Field K] (n' m' : ℕ) :=
  MvPolynomial (Fin (n' + m' - 1 + 2)) K

/-- Universal normalized reciprocal-square Jacobian matrix in positive two-sided rank. -/
noncomputable def criticalSchurTailMatrix
    (K : Type*) [Field K] (n' m' : ℕ) :
    Matrix (Fin (m' + 1)) (Fin (m' + 1)) (criticalSchurTailRing K n' m') :=
  rectangularSchurToeplitz (schurVar K (n' + m' - 1 + 2)) (n' + 1) (m' + 1)

/-- Prime determinant ideal of the normalized critical Jacobian. -/
noncomputable def criticalSchurTailIdeal
    (K : Type*) [Field K] (n' m' : ℕ) : Ideal (criticalSchurTailRing K n' m') :=
  Ideal.span ({(criticalSchurTailMatrix K n' m').det} :
    Set (criticalSchurTailRing K n' m'))

theorem criticalSchurTailIdeal_isPrime
    (K : Type*) [Field K] {n' m' : ℕ} (hn : 0 < n') (hm : 0 < m') :
    (criticalSchurTailIdeal K n' m').IsPrime := by
  classical
  simpa [criticalSchurTailIdeal, criticalSchurTailMatrix] using
    rectangularSchurDivisorIdeal_isPrime (K := K) hn hm

/-- Integral coordinate ring of the generic Schur divisor. -/
abbrev criticalSchurTailDivisorRing
    (K : Type*) [Field K] (n' m' : ℕ) :=
  (criticalSchurTailRing K n' m') ⧸ criticalSchurTailIdeal K n' m'

/-- Function field of the generic Schur divisor. -/
abbrev criticalSchurTailDivisorField
    (K : Type*) [Field K] (n' m' : ℕ) :=
  FractionRing (criticalSchurTailDivisorRing K n' m')

/-- Map from Schur tail coordinates to the divisor function field. -/
noncomputable def criticalSchurTailGenericMap
    (K : Type*) [Field K] {n' m' : ℕ} (hn : 0 < n') (hm : 0 < m') :
    criticalSchurTailRing K n' m' →+*
      criticalSchurTailDivisorField K n' m' := by
  letI : IsDomain (criticalSchurTailDivisorRing K n' m') :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr
      (criticalSchurTailIdeal_isPrime K hn hm)
  exact (algebraMap (criticalSchurTailDivisorRing K n' m')
    (criticalSchurTailDivisorField K n' m')).comp
      (Ideal.Quotient.mk (criticalSchurTailIdeal K n' m'))

/-- Normalized actual Jacobian at the generic point of its Schur divisor. -/
noncomputable def criticalSchurGenericMatrix
    (K : Type*) [Field K] {n' m' : ℕ} (hn : 0 < n') (hm : 0 < m') :
    Matrix (Fin (m' + 1)) (Fin (m' + 1))
      (criticalSchurTailDivisorField K n' m') := by
  letI : IsDomain (criticalSchurTailDivisorRing K n' m') :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr
      (criticalSchurTailIdeal_isPrime K hn hm)
  exact (criticalSchurTailMatrix K n' m').map
    (criticalSchurTailGenericMap K hn hm)

theorem criticalSchurGenericMatrix_det_eq_zero
    (K : Type*) [Field K] {n' m' : ℕ} (hn : 0 < n') (hm : 0 < m') :
    (criticalSchurGenericMatrix K hn hm).det = 0 := by
  letI : IsDomain (criticalSchurTailDivisorRing K n' m') :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr
      (criticalSchurTailIdeal_isPrime K hn hm)
  rw [criticalSchurGenericMatrix, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det]
  change algebraMap (criticalSchurTailDivisorRing K n' m')
      (criticalSchurTailDivisorField K n' m')
        (Ideal.Quotient.mk (criticalSchurTailIdeal K n' m')
          (criticalSchurTailMatrix K n' m').det) = 0
  rw [show Ideal.Quotient.mk (criticalSchurTailIdeal K n' m')
      (criticalSchurTailMatrix K n' m').det = 0 by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _]
  exact map_zero _

/-- The corner cofactor stays nonzero at the generic point of the actual Schur divisor. -/
theorem criticalSchurGenericMatrix_cornerCofactor_ne_zero
    (K : Type*) [Field K] {n' m' : ℕ} (hn : 0 < n') (hm : 0 < m') :
    ((criticalSchurGenericMatrix K hn hm).submatrix
      (Fin.last m').succAbove Fin.succ).det ≠ 0 := by
  classical
  letI : IsDomain (criticalSchurTailDivisorRing K n' m') :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr
      (criticalSchurTailIdeal_isPrime K hn hm)
  let A := criticalSchurTailMatrix K n' m'
  let c := (A.submatrix (Fin.last m').succAbove Fin.succ).det
  have hcQ : Ideal.Quotient.mk (criticalSchurTailIdeal K n' m') c ≠ 0 := by
    change Ideal.Quotient.mk
      (Ideal.span ({(rectangularSchurToeplitz
        (schurVar K (n' + m' - 1 + 2)) (n' + 1) (m' + 1)).det} :
          Set (MvPolynomial (Fin (n' + m' - 1 + 2)) K)))
      ((rectangularSchurToeplitz
        (schurVar K (n' + m' - 1 + 2)) (n' + 1) (m' + 1)).submatrix
          (Fin.last m').succAbove Fin.succ).det ≠ 0
    exact rectangularSchurCofactor_ne_zero_in_divisorRing (K := K) hn hm
  have hcF : algebraMap (criticalSchurTailDivisorRing K n' m')
      (criticalSchurTailDivisorField K n' m')
        (Ideal.Quotient.mk (criticalSchurTailIdeal K n' m') c) ≠ 0 :=
    by
      intro hzero
      apply hcQ
      apply IsFractionRing.injective (criticalSchurTailDivisorRing K n' m')
        (criticalSchurTailDivisorField K n' m')
      simpa using hzero
  rw [criticalSchurGenericMatrix, Matrix.submatrix_map,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact hcF

/-- **Generic corank one.**  On the function field of the irreducible Schur divisor, the kernel of
the normalized actual critical Jacobian is exactly one-dimensional. -/
theorem finrank_ker_criticalSchurGenericMatrix_eq_one
    (K : Type*) [Field K] {n' m' : ℕ} (hn : 0 < n') (hm : 0 < m') : by
    letI : IsDomain (criticalSchurTailDivisorRing K n' m') :=
      (Ideal.Quotient.isDomain_iff_prime _).mpr
        (criticalSchurTailIdeal_isPrime K hn hm)
    exact Module.finrank (criticalSchurTailDivisorField K n' m')
      (LinearMap.ker (criticalSchurGenericMatrix K hn hm).mulVecLin) = 1 := by
  classical
  letI : IsDomain (criticalSchurTailDivisorRing K n' m') :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr
      (criticalSchurTailIdeal_isPrime K hn hm)
  let M := criticalSchurGenericMatrix K hn hm
  have hdet : M.det = 0 := criticalSchurGenericMatrix_det_eq_zero K hn hm
  obtain ⟨v, hvne, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  have hkerne : LinearMap.ker M.mulVecLin ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨v, by simpa [Matrix.mulVecLin_apply] using hv, hvne⟩
  have hkerge : 1 ≤ Module.finrank (criticalSchurTailDivisorField K n' m')
      (LinearMap.ker M.mulVecLin) :=
    Submodule.one_le_finrank_iff.mpr hkerne
  let B := M.submatrix (Fin.last m').succAbove Fin.succ
  have hBdet : B.det ≠ 0 :=
    criticalSchurGenericMatrix_cornerCofactor_ne_zero K hn hm
  have hBunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hrankB : B.rank = m' := by
    have h := Matrix.rank_mul_eq_right_of_isUnit_det B
      (1 : Matrix (Fin m') (Fin m')
        (criticalSchurTailDivisorField K n' m')) hBunit
    simpa [B] using h
  have hrankge : m' ≤ M.rank := by
    exact hrankB.symm.trans_le
      (Matrix.rank_submatrix_le M (Fin.last m').succAbove Fin.succ)
  change m' ≤
      Module.finrank (criticalSchurTailDivisorField K n' m')
        (LinearMap.range M.mulVecLin) at hrankge
  have hsum := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hsum
  change Module.finrank (criticalSchurTailDivisorField K n' m')
    (LinearMap.ker M.mulVecLin) = 1
  omega

end

end GaloisForLFunctions.HTGeometry
