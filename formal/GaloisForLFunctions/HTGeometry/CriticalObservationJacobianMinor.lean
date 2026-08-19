import GaloisForLFunctions.HTGeometry.CriticalObservationConormalBase
import GaloisForLFunctions.HTGeometry.SquareMatrixCorankOne

/-!
# Minors of the observation Jacobian

The corank-one criterion is index-type agnostic, and the observation Jacobian is block triangular
with an identity corner, so its minors of codimension one reduce to minors of the reciprocal
Jacobian:

```text
finrank_ker_mulVecLin_eq_one_of_det_eq_zero'      corank one over any finite index type
det_criticalObservationJacobian_map_residue       the Jacobian is singular at the Schur place
det_submatrix_criticalObservationJacobian
    ** deleting one raw row and column leaves the corresponding minor of the reciprocal
       Jacobian **
```
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Matrix IsLocalRing KaehlerDifferential

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

/-- **Corank one over an arbitrary finite index type.**  A square matrix over a field whose
determinant vanishes but which has a nonsingular submatrix of codimension one has a
one-dimensional kernel. -/
theorem finrank_ker_mulVecLin_eq_one_of_det_eq_zero'
    {F : Type*} [Field F] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι ι F) (hdet : M.det = 0) {r c : κ → ι}
    (hcard : Fintype.card κ + 1 = Fintype.card ι)
    (hB : (M.submatrix r c).det ≠ 0) :
    Module.finrank F (LinearMap.ker M.mulVecLin) = 1 := by
  classical
  obtain ⟨v, hvne, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  have hkerne : LinearMap.ker M.mulVecLin ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨v, by simpa [Matrix.mulVecLin_apply] using hv, hvne⟩
  have hkerge : 1 ≤ Module.finrank F (LinearMap.ker M.mulVecLin) :=
    Submodule.one_le_finrank_iff.mpr hkerne
  have hrankB : (M.submatrix r c).rank = Fintype.card κ := by
    have h := Matrix.rank_mul_eq_right_of_isUnit_det (M.submatrix r c)
      (1 : Matrix κ κ F) (isUnit_iff_ne_zero.mpr hB)
    simpa using h
  have hrankge : Fintype.card κ ≤ M.rank := hrankB.symm.trans_le (Matrix.rank_submatrix_le M r c)
  change Fintype.card κ ≤ Module.finrank F (LinearMap.range M.mulVecLin) at hrankge
  have hsum := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hsum
  omega

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

omit [IsAlgClosed K] in
/-- The observation Jacobian is singular at the source Schur place. -/
theorem det_criticalObservationJacobian_map_residue :
    ((criticalObservationJacobian K (m := m) (n := n)).map
      (IsLocalRing.residue
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)))).det
      = 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_criticalObservationJacobian K]
  refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
  exact (IsLocalRing.mem_maximalIdeal _).mpr
    (irreducible_criticalSchurJacobianDetElement K (Fact.out : 1 < m)
      (Fact.out : 1 < n)).not_isUnit

omit [IsAlgClosed K] [Fact (1 < m)] [Fact (1 < n)] in
/-- Deleting one row and one column from the raw block of the observation Jacobian leaves a
determinant equal to that of the corresponding minor of the reciprocal Jacobian. -/
theorem det_submatrix_criticalObservationJacobian
    {F : Type*} [CommRing F]
    (φ : criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) →+* F)
    {k : ℕ} (ρ γ : Fin k → Fin m) :
    (((criticalObservationJacobian K (m := m) (n := n)).map φ).submatrix
        (Sum.map ρ id) (Sum.map γ id)).det
      = (((criticalReciprocalJacobian
            (criticalSourceRecipPolynomialIntegral K (Fact.out : 0 < m) (Fact.out : 0 < n))
            n m).map φ).submatrix γ ρ).det := by
  classical
  have hblocks : ((criticalObservationJacobian K (m := m) (n := n)).map φ).submatrix
      (Sum.map ρ id) (Sum.map γ id)
      = Matrix.fromBlocks
          (((criticalReciprocalJacobian
            (criticalSourceRecipPolynomialIntegral K (Fact.out : 0 < m) (Fact.out : 0 < n))
            n m).map φ).transpose.submatrix ρ γ)
          0
          ((((criticalObservationJacobian K (m := m) (n := n)).map φ).submatrix
            (Sum.inr) (Sum.inl ∘ γ)))
          1 := by
    refine Matrix.ext fun x y => ?_
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        show φ (criticalObservationJacobian K (Sum.inl (ρ a)) (Sum.inl (γ b))) = _
        rw [criticalObservationJacobian_eq_fromBlocks K]
        rfl
      | inr b =>
        show φ (criticalObservationJacobian K (Sum.inl (ρ a)) (Sum.inr b)) = _
        rw [criticalObservationJacobian_eq_fromBlocks K]
        show φ 0 = _
        rw [map_zero]
        rfl
    | inr a =>
      cases y with
      | inl b => rfl
      | inr b =>
        show φ (criticalObservationJacobian K (Sum.inr a) (Sum.inr b)) = _
        rw [criticalObservationJacobian_eq_fromBlocks K]
        show φ (if a = b then 1 else 0) = _
        by_cases hab : a = b
        · rw [if_pos hab, map_one, Matrix.fromBlocks_apply₂₂, Matrix.one_apply, if_pos hab]
        · rw [if_neg hab, map_zero, Matrix.fromBlocks_apply₂₂, Matrix.one_apply, if_neg hab]
  rw [hblocks, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one,
    ← Matrix.transpose_submatrix, Matrix.det_transpose]

end

end GaloisForLFunctions.HTGeometry
