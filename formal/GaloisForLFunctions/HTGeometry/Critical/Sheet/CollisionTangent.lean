import GaloisForLFunctions.HTGeometry.Critical.Sheet.FixedConormal
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.LowTangentJacobianKernel
import GaloisForLFunctions.HTGeometry.MatrixKernelDeletedColumn
import GaloisForLFunctions.HTGeometry.Critical.Schur.TangentConstantTerm
import GaloisForLFunctions.HTGeometry.CriticalFibreSharedTangentRigidity
import GaloisForLFunctions.HTGeometry.Critical.Schur.MarkedReduction

/-!
# Collision tangents are singular, and their constant term survives

A nonzero low tangent makes the reduced horizon Jacobian singular, hence makes the sheet singular
in the sense of `CriticalSheetSchurPullback`.  The reduced reciprocal jet has a nonzero constant
term, and the surviving corner minor forces the tangent's own constant term to be nonzero.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial IsLocalRing

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- **A nonzero low tangent forces the sheet to be singular.** -/
theorem criticalSheet_singular_of_tangent (σ : criticalGeometricSheet K m n)
    {U V : (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
      (Fact.out : 0 < m) (Fact.out : 0 < n)))[X]}
    (hU : U.degree < (m : ℕ)) (hV : V.degree < (n : ℕ)) (hUV : U ≠ 0 ∨ V ≠ 0)
    (htan : (X : (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
        (Fact.out : 0 < m) (Fact.out : 0 < n)))[X]) ^ (m + n)
      ∣ U * criticalSheetReducedRecipPolynomial K σ
        + criticalSheetReducedRawPolynomial K σ * V) :
    criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)) := by
  classical
  refine criticalSheet_singular_of_det_eq_zero K σ ?_
  rw [← det_horizonObservationJacobian]
  exact Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨horizonConormalVector U V m n, horizonConormalVector_ne_zero hU hV hUV,
      horizonObservationJacobian_mulVec_conormal (criticalSheet_reduced_inv K σ) hU hV htan⟩

/-- The reduced reciprocal jet of a sheet has a nonzero constant term. -/
theorem criticalSheetReducedRecipPolynomial_coeff_zero_ne_zero
    (σ : criticalGeometricSheet K m n) :
    (criticalSheetReducedRecipPolynomial K σ).coeff 0 ≠ 0 := by
  have hm : (0 : ℕ) < m := Fact.out
  have hn : (0 : ℕ) < n := Fact.out
  set W := criticalNormalClosureSchurValuationSubring K hm hn with hW
  set c : W := ((criticalGeometricSheetToSchurFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ).1.2
    + criticalNormalClosureSchurReciprocalTailIntegral K hm hn).coeff 0 with hc
  have hval : (c : criticalNormalClosure K m n)
      = σ (criticalSourceRecip K m n ⟨0, by omega⟩) := by
    have h := congrArg (fun p => Polynomial.coeff p 0)
      (criticalSheetFibre_recipPolynomial_map K σ)
    simp only [Polynomial.coeff_map] at h
    rw [hc]
    refine h.trans ?_
    show σ ((criticalSourceReciprocalPolynomial K m n).coeff 0) = _
    rw [criticalSourceReciprocalPolynomial_coeff K m n 0 (by omega)]
  have hraw : σ (criticalSourceRaw K m n ⟨0, by omega⟩)
      ∈ criticalNormalClosureSchurValuationSubring K hm hn :=
    criticalSourceRaw_sheet_mem_normalClosureSchur K (Fact.out : 1 < m) (Fact.out : 1 < n) σ _
  have hone : c * ⟨σ (criticalSourceRaw K m n ⟨0, by omega⟩), hraw⟩ = 1 := by
    apply Subtype.ext
    show (c : criticalNormalClosure K m n) * σ (criticalSourceRaw K m n ⟨0, by omega⟩) = 1
    rw [hval, ← map_mul]
    have hinv : criticalSourceRecip K m n ⟨0, by omega⟩ *
        criticalSourceRaw K m n ⟨0, by omega⟩ = 1 := by
      rw [criticalSourceRecip_zero_eq_inv K (by omega : 0 < m + n)]
      exact inv_mul_cancel₀ (criticalSourceScale_ne_zero K hm hn)
    rw [hinv, map_one]
  have hunit : IsUnit c := ⟨⟨c, _, hone, (mul_comm _ _).trans hone⟩, rfl⟩
  rw [criticalSheetReducedRecipPolynomial, Polynomial.coeff_map]
  exact fun hzero => (IsLocalRing.notMem_maximalIdeal.mpr hunit)
    ((IsLocalRing.residue_eq_zero_iff _).mp hzero)

/-- **The constant term of a collision tangent does not vanish.** -/
theorem criticalSheet_tangent_coeff_zero_ne_zero [DecidableEq K]
    (σ : criticalGeometricSheet K m n)
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)))
    {U V : (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
      (Fact.out : 0 < m) (Fact.out : 0 < n)))[X]}
    (hU : U.degree < (m : ℕ)) (hV : V.degree < (n : ℕ)) (hUV : U ≠ 0 ∨ V ≠ 0)
    (htan : (X : (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
        (Fact.out : 0 < m) (Fact.out : 0 < n)))[X]) ^ (m + n)
      ∣ U * criticalSheetReducedRecipPolynomial K σ
        + criticalSheetReducedRawPolynomial K σ * V) :
    U.coeff 0 ≠ 0 := by
  classical
  obtain ⟨m', hm'⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := (Fact.out : 1 < m); omega⟩
  subst hm'
  have hker := horizonObservationJacobian_mulVec_conormal
    (criticalSheet_reduced_inv K σ) hU hV htan
  have hne := horizonConormalVector_ne_zero hU hV hUV
  have hinj : Function.Injective
      (Sum.map (Fin.last m').succAbove (id : Fin n → Fin n)) := by
    rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (Fin.succAbove_right_injective (Sum.inl.inj hab))
    · exact absurd hab (by simp)
    · exact absurd hab (by simp)
    · exact congrArg Sum.inr (Sum.inr.inj hab)
  have hsurj : ∀ i : Fin (m' + 1) ⊕ Fin n, i ≠ Sum.inl (Fin.last m') →
      ∃ j, Sum.map (Fin.last m').succAbove (id : Fin n → Fin n) j = i := by
    rintro (a | a) hne'
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq
        (show a ≠ Fin.last m' from fun h => hne' (by rw [h]))
      exact ⟨Sum.inl j, by rw [Sum.map_inl, hj]⟩
    · exact ⟨Sum.inr a, rfl⟩
  have hB : ((horizonObservationJacobian (criticalSheetReducedRecipPolynomial K σ)
      n (m' + 1)).submatrix (Sum.map Fin.succ id)
      (Sum.map (Fin.last m').succAbove id)).det ≠ 0 := by
    rw [criticalSheetReducedRecipPolynomial, ← criticalSheet_jacobian_eq_horizon K σ hsing]
    obtain ⟨n', hn'⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := (Fact.out : 1 < n); omega⟩
    subst hn'
    rw [det_submatrix_criticalObservationJacobian K, Matrix.submatrix_map,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det, RingHom.comp_apply]
    refine residue_criticalSheetSourceSchurLift_ne_zero K σ hsing ?_
    exact residue_det_submatrix_criticalReciprocalJacobianIntegral_ne_zero
      (K := K) (m := m' + 1) (n := n' + 1)
      (Nat.succ_lt_succ_iff.mp (Fact.out : 1 < m' + 1))
      (Nat.succ_lt_succ_iff.mp (Fact.out : 1 < n' + 1))
      Fact.out Fact.out
  have hcoord := ker_coord_ne_zero_of_det_submatrix_ne_zero
    (horizonObservationJacobian (criticalSheetReducedRecipPolynomial K σ) n (m' + 1))
    hinj hsurj hB hker hne
  simpa [horizonConormalVector] using hcoord
end

end GaloisForLFunctions.HTGeometry
