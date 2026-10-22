import GaloisForLFunctions.HTGeometry.Critical.Sheet.SchurPullback
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.Critical.Schur.JacobianCorankOne

/-!
# Corank one at every singular point of the reduced fibre

The kernel of the reduced observation Jacobian is a line not only at the Schur place but at every
singular reduced state of a geometric sheet.  The reason is `(D-1)`: a singular sheet pulls the
normal-closure Schur valuation back to the Schur place, so its lift is a local map of the source
Schur valuation ring, and the surviving corner minor keeps a nonzero residue.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing Matrix

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

variable (σ : criticalGeometricSheet K m n)

/-- The lift of a singular sheet is a local map. -/
theorem criticalSheetSourceSchurLift_mem_maximalIdeal
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)))
    {x : criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)}
    (hx : x ∈ maximalIdeal (criticalSchurSourceValuationSubring K (Fact.out : 0 < m)
      (Fact.out : 0 < n))) :
    criticalSheetSourceSchurLift K σ hsing x
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)) := by
  have hfm : 0 < m := Fact.out
  have hfn : 0 < n := Fact.out
  have hmap : (criticalSchurChartPrime K (m := m) (n := n)).map
      (algebraMap (criticalSourceChartAlgebra K (m := m) (n := n))
        (criticalSchurSourceValuationSubring K hfm hfn))
      = maximalIdeal (criticalSchurSourceValuationSubring K hfm
        hfn) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal _ _
  rw [← hmap] at hx
  have hle : (criticalSchurChartPrime K (m := m) (n := n)).map
      (algebraMap (criticalSourceChartAlgebra K (m := m) (n := n))
        (criticalSchurSourceValuationSubring K hfm hfn))
      ≤ (maximalIdeal (criticalNormalClosureSchurValuationSubring K hfm
        hfn)).comap (criticalSheetSourceSchurLift K σ hsing) := by
    rw [Ideal.map_le_iff_le_comap]
    intro t ht
    rw [Ideal.mem_comap]
    show (criticalSheetSourceSchurLift K σ hsing)
        (algebraMap (criticalSourceChartAlgebra K (m := m) (n := n))
          (criticalSchurSourceValuationSubring K hfm hfn) t)
        ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K hfm
          hfn)
    rw [criticalSheetSourceSchurLift, IsLocalization.lift_eq]
    rw [← criticalSheetChartPrime_eq_of_singular K σ hsing] at ht
    exact ht
  exact hle hx

/-- **Corank one at every singular point of the reduced fibre.** -/
theorem criticalSheet_finrank_ker_reduced_jacobian_eq_one [DecidableEq K]
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n))) :
    Module.finrank
        (IsLocalRing.ResidueField
          (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)))
        (LinearMap.ker (((criticalObservationJacobian K (m := m) (n := n)).map
          ((IsLocalRing.residue
            (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
              (Fact.out : 0 < n))).comp
            (criticalSheetSourceSchurLift K σ hsing))).mulVecLin)) = 1 := by
  classical
  obtain ⟨m', rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := (Fact.out : 1 < m); omega⟩
  obtain ⟨n', rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := (Fact.out : 1 < n); omega⟩
  have hdet0 : ((criticalObservationJacobian K (m := m' + 1) (n := n' + 1)).map
      ((IsLocalRing.residue
        (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m' + 1)
          (Fact.out : 0 < n' + 1))).comp
        (criticalSheetSourceSchurLift K σ hsing))).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    have hB : IsLocalRing.residue
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m' + 1)
          (Fact.out : 0 < n' + 1))
        (criticalObservationJacobian K (m := m' + 1) (n := n' + 1)).det = 0 := by
      have := det_criticalObservationJacobian_map_residue K (m := m' + 1) (n := n' + 1)
      rwa [← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    have hmem : (criticalObservationJacobian K (m := m' + 1) (n := n' + 1)).det
        ∈ maximalIdeal (criticalSchurSourceValuationSubring K (Fact.out : 0 < m' + 1)
          (Fact.out : 0 < n' + 1)) := (IsLocalRing.residue_eq_zero_iff _).mp hB
    exact (IsLocalRing.residue_eq_zero_iff _).mpr
      (criticalSheetSourceSchurLift_mem_maximalIdeal K σ hsing hmem)
  refine finrank_ker_mulVecLin_eq_one_of_det_eq_zero' _ hdet0
    (r := Sum.map Fin.succ id) (c := Sum.map (Fin.last m').succAbove id) ?_ ?_
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · rw [det_submatrix_criticalObservationJacobian K, Matrix.submatrix_map,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det, RingHom.comp_apply]
    refine residue_criticalSheetSourceSchurLift_ne_zero K σ hsing ?_
    exact residue_det_submatrix_criticalReciprocalJacobianIntegral_ne_zero
      (K := K) (m := m' + 1) (n := n' + 1)
      (Nat.succ_lt_succ_iff.mp (Fact.out : 1 < m' + 1))
      (Nat.succ_lt_succ_iff.mp (Fact.out : 1 < n' + 1))
      Fact.out Fact.out

end

end GaloisForLFunctions.HTGeometry
