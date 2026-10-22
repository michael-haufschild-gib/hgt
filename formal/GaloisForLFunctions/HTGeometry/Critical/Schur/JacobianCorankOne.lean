import GaloisForLFunctions.HTGeometry.Critical.Schur.CornerCofactor
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower

/-!
# Corank one of the observation Jacobian at the source Schur place

The reciprocal Jacobian is the negative normalized Schur Toeplitz matrix scaled by the inverse
square of the source scale, so each of its minors is a unit multiple of the corresponding minor of
the universal Schur section evaluated at the Schur coordinates.  The corner cofactor is not in the
ramification ideal, hence has nonzero residue, while the determinant itself does vanish there:

```text
coe_det_submatrix_criticalReciprocalJacobianIntegral      the minor in closed form
residue_det_submatrix_criticalReciprocalJacobianIntegral_ne_zero
criticalSchur_finrank_ker_reduced_jacobian_eq_one
    ** the kernel of the reduced observation Jacobian is a LINE **
```

That line is the conormal line of the branch, and `CriticalObservationConormalBase` exhibits a
nonzero vector in it coming from the observation side.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Matrix IsLocalRing MvPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable (K : Type*) [Field K] [CharZero K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)

/-- The Schur coordinates after the scale are the reversed reciprocal squares. -/
theorem criticalSourceSchurCoordinates_comp_succ :
    criticalSourceSchurCoordinates K hm hn ∘ Fin.succ
      = criticalSourceReciprocalSquareReversed K hm hn := by
  funext i
  simp [criticalSourceSchurCoordinates]

/-- Evaluating a shifted polynomial at the Schur coordinates discards the scale. -/
theorem aeval_criticalSourceSchurCoordinates_rename_succ
    (p : MvPolynomial (Fin (m + n - 1)) K) :
    MvPolynomial.aeval (criticalSourceSchurCoordinates K hm hn)
        (MvPolynomial.rename Fin.succ p)
      = MvPolynomial.aeval (criticalSourceReciprocalSquareReversed K hm hn) p := by
  rw [MvPolynomial.aeval_rename, criticalSourceSchurCoordinates_comp_succ K hm hn]

/-- **A minor of the integral reciprocal Jacobian, in closed form.** -/
theorem coe_det_submatrix_criticalReciprocalJacobianIntegral
    {k : ℕ} (ρ γ : Fin k → Fin m) :
    ((((criticalReciprocalJacobian (criticalSourceRecipPolynomialIntegral K hm hn) n m).submatrix
        ρ γ).det : criticalSchurSourceValuationSubring K hm hn) : criticalSourceField K m n)
      = (-1 : criticalSourceField K m n) ^ k *
          (((criticalSourceScale K hm hn) ^ 2)⁻¹) ^ k *
          MvPolynomial.aeval (criticalSourceSchurCoordinates K hm hn)
            (MvPolynomial.rename Fin.succ
              (((rectangularSchurToeplitz (schurVar K (m + n - 1)) n m).submatrix ρ γ).det)) := by
  classical
  rw [aeval_criticalSourceSchurCoordinates_rename_succ K hm hn]
  have hmat : criticalReciprocalJacobian (criticalSourceReciprocalPolynomial K m n) n m
      = -((((criticalSourceScale K hm hn) ^ 2)⁻¹) •
          ((rectangularSchurToeplitz (schurVar K (m + n - 1)) n m).map
            (MvPolynomial.aeval (criticalSourceReciprocalSquareReversed K hm hn)))) := by
    rw [criticalReciprocalJacobian_eq_neg_rectangularSchurToeplitz,
      show (fun kk => (criticalSourceReciprocalPolynomial K m n *
          criticalSourceReciprocalPolynomial K m n).coeff kk)
        = (fun kk => ((criticalSourceReciprocalPolynomial K m n) ^ 2).coeff kk) by
        simp [pow_two],
      rectangularSchurToeplitz_actual_eq_invScale_smul_normalized K hm hn,
      map_aeval_rectangularSchurToeplitz K hm hn]
  show (criticalSchurSourceValuationSubring K hm hn).subtype
      (((criticalReciprocalJacobian (criticalSourceRecipPolynomialIntegral K hm hn) n m).submatrix
        ρ γ).det) = _
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map,
    map_criticalReciprocalJacobianIntegral K hm hn, hmat,
    show ((-((((criticalSourceScale K hm hn) ^ 2)⁻¹) •
        ((rectangularSchurToeplitz (schurVar K (m + n - 1)) n m).map
          (MvPolynomial.aeval (criticalSourceReciprocalSquareReversed K hm hn))))).submatrix ρ γ)
      = -((((criticalSourceScale K hm hn) ^ 2)⁻¹) •
        (((rectangularSchurToeplitz (schurVar K (m + n - 1)) n m).submatrix ρ γ).map
          (MvPolynomial.aeval (criticalSourceReciprocalSquareReversed K hm hn)))) from rfl,
    Matrix.det_neg, Matrix.det_smul, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
  simp only [Fintype.card_fin]
  ring

/-- **The corner minor of the reduced reciprocal Jacobian is nonzero at the Schur place.** -/
theorem residue_det_submatrix_criticalReciprocalJacobianIntegral_ne_zero
    [DecidableEq K] {m' n' : ℕ} (hm' : 0 < m') (hn' : 0 < n')
    (hm2 : 1 < m' + 1) (hn2 : 1 < n' + 1) :
    IsLocalRing.residue
        (criticalSchurSourceValuationSubring K (by omega : 0 < m' + 1) (by omega : 0 < n' + 1))
        (((criticalReciprocalJacobian
            (criticalSourceRecipPolynomialIntegral K (by omega : 0 < m' + 1)
              (by omega : 0 < n' + 1)) (n' + 1) (m' + 1)).submatrix
          (Fin.last m').succAbove Fin.succ).det) ≠ 0 := by
  classical
  set hm0 : 0 < m' + 1 := by omega
  set hn0 : 0 < n' + 1 := by omega
  set Cof : criticalSchurSourceRing K (m' + 1) (n' + 1) :=
    MvPolynomial.rename Fin.succ
      (((rectangularSchurToeplitz (schurVar K ((m' + 1) + (n' + 1) - 1)) (n' + 1)
        (m' + 1)).submatrix (Fin.last m').succAbove Fin.succ).det) with hCof
  set w : criticalSchurSourceValuationSubring K hm0 hn0 :=
    algebraMap (criticalSchurSourceRing K (m' + 1) (n' + 1)) _ Cof with hw
  set u : criticalSchurSourceValuationSubring K hm0 hn0 :=
    (-1) ^ m' * (criticalSchurSourceScaleInvElement K hm0 hn0) ^ (2 * m') with hu
  have hcu : ((u : criticalSourceField K (m' + 1) (n' + 1)))
      = (-1 : criticalSourceField K (m' + 1) (n' + 1)) ^ m' *
        (((criticalSourceScale K hm0 hn0) ^ 2)⁻¹) ^ m' := by
    rw [hu]
    push_cast
    rw [show ((criticalSchurSourceScaleInvElement K hm0 hn0 :
        criticalSourceField K (m' + 1) (n' + 1))) = (criticalSourceScale K hm0 hn0)⁻¹ from rfl]
    congr 1
    rw [pow_mul, inv_pow]
  have hkey : (((criticalReciprocalJacobian
      (criticalSourceRecipPolynomialIntegral K hm0 hn0) (n' + 1) (m' + 1)).submatrix
        (Fin.last m').succAbove Fin.succ).det) = u * w := by
    apply Subtype.val_injective
    rw [show (((u * w : criticalSchurSourceValuationSubring K hm0 hn0) :
        criticalSourceField K (m' + 1) (n' + 1)))
        = (u : criticalSourceField K (m' + 1) (n' + 1)) *
          (w : criticalSourceField K (m' + 1) (n' + 1)) from rfl, hcu,
      hw, coe_algebraMap_criticalSchurSourceValuation K hm0 hn0]
    exact coe_det_submatrix_criticalReciprocalJacobianIntegral K hm0 hn0 _ _
  rw [hkey, map_mul]
  refine mul_ne_zero ?_ ?_
  · have hunit : IsUnit u := by
      rw [hu]
      exact ((isUnit_one.neg).pow m').mul
        ((isUnit_criticalSchurSourceScaleInvElement K hm2 hn2).pow (2 * m'))
    exact (hunit.map (IsLocalRing.residue
      (criticalSchurSourceValuationSubring K hm0 hn0))).ne_zero
  · rw [hw]
    intro hzero
    exact criticalSchur_cornerCofactor_notMem_ramificationIdeal (K := K) hm' hn'
      ((criticalSchur_residue_algebraMap_eq_zero_iff K hm0 hn0 Cof).mp hzero)

section Facts

variable [IsAlgClosed K] [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

omit [IsAlgClosed K] in
/-- **Corank one of the observation Jacobian at the source Schur place.** -/
theorem criticalSchur_finrank_ker_reduced_jacobian_eq_one [DecidableEq K] :
    Module.finrank
        (IsLocalRing.ResidueField
          (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)))
        (LinearMap.ker ((criticalObservationJacobian K (m := m) (n := n)).map
          (IsLocalRing.residue
            (criticalSchurSourceValuationSubring K (Fact.out : 0 < m)
              (Fact.out : 0 < n)))).mulVecLin) = 1 := by
  classical
  obtain ⟨m', rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := (Fact.out : 1 < m); omega⟩
  obtain ⟨n', rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := (Fact.out : 1 < n); omega⟩
  refine finrank_ker_mulVecLin_eq_one_of_det_eq_zero' _
    (det_criticalObservationJacobian_map_residue K)
    (r := Sum.map Fin.succ id) (c := Sum.map (Fin.last m').succAbove id) ?_ ?_
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · rw [det_submatrix_criticalObservationJacobian K, Matrix.submatrix_map,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact residue_det_submatrix_criticalReciprocalJacobianIntegral_ne_zero
      (K := K) (m := m' + 1) (n := n' + 1)
      (Nat.succ_lt_succ_iff.mp (Fact.out : 1 < m' + 1))
      (Nat.succ_lt_succ_iff.mp (Fact.out : 1 < n' + 1))
      Fact.out Fact.out

end Facts

end

end GaloisForLFunctions.HTGeometry
