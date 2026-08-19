import GaloisForLFunctions.HTGeometry.CriticalSchurGenerationHypothesis
import GaloisForLFunctions.HTGeometry.CriticalSchurSourceIntegralModels

/-!
# The observation Jacobian in the raw differentials

The observation coordinates are the high raw coefficients together with the high reciprocal
coefficients.  In the differentials of the raw coordinates the first block is the identity and the
second is the rectangular Schur Toeplitz block, by `dY = -Y² dX`.  This module sets up the two
families and the block matrix, and proves the identity column.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial IsLocalRing KaehlerDifferential Polynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- Source index attached to an observation index: the high raw coordinates for the raw block and
the low raw coordinates for the reciprocal block. -/
def criticalSourceIndexOfObservation : Fin n ⊕ Fin m → Fin (m + n)
  | Sum.inl i => ⟨m + (i : ℕ), by have := (Fact.out : 0 < n); omega⟩
  | Sum.inr j => ⟨(j : ℕ), by have := (Fact.out : 0 < n); omega⟩

theorem coe_algebraMap_criticalObservationCoordSchur (s : Fin n ⊕ Fin m) :
    ((algebraMap
        (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (criticalObservationCoordSchur K s) :
        criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :
      criticalSourceField K m n)
      = algebraMap (criticalObservationRing K m n) (criticalSourceField K m n)
        (MvPolynomial.X s) := by
  rw [criticalObservationCoordSchur, ← IsScalarTower.algebraMap_apply,
    coe_algebraMap_observationRing_schur K]

theorem algebraMap_criticalObservationCoordSchur_inl (i : Fin n) :
    algebraMap
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (criticalObservationCoordSchur K (Sum.inl i))
      = criticalSourceRawIntegral K (Fact.out : 0 < m) (Fact.out : 0 < n)
        ⟨m + (i : ℕ), by have := (Fact.out : 0 < n); omega⟩ := by
  apply Subtype.ext
  rw [coe_algebraMap_criticalObservationCoordSchur K,
    algebraMap_criticalObservationRing_X_inl K]
  rfl

theorem algebraMap_criticalObservationCoordSchur_inr (j : Fin m) :
    algebraMap
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (criticalObservationCoordSchur K (Sum.inr j))
      = criticalSourceRecipIntegral K (Fact.out : 0 < m) (Fact.out : 0 < n)
        ⟨n + (j : ℕ), by have := (Fact.out : 0 < m); omega⟩ := by
  apply Subtype.ext
  rw [coe_algebraMap_criticalObservationCoordSchur K,
    algebraMap_criticalObservationRing_X_inr K]
  rfl

/-- The auxiliary family of raw differentials. -/
noncomputable def criticalRawDifferential (t : Fin m ⊕ Fin n) :
    Ω[criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) ⁄ K] :=
  KaehlerDifferential.D K
    (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
    (criticalSourceRawIntegral K (Fact.out : 0 < m) (Fact.out : 0 < n)
      ((finSumFinEquiv t : Fin (m + n))))

/-- The observation family in block order: reciprocal observations first, then raw. -/
noncomputable def criticalObservationBlockCoord (s : Fin m ⊕ Fin n) :
    criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) :=
  criticalObservationCoordSchur K (Equiv.sumComm _ _ s)

/-- The observation Jacobian in the raw differentials, in block order. -/
noncomputable def criticalObservationJacobian :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n)
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :=
  Matrix.of fun t s =>
    match s with
    | Sum.inl s' =>
        if ((finSumFinEquiv t : Fin (m + n)) : ℕ) ≤ n + (s' : ℕ) then
          -((criticalSourceRecipPolynomialIntegral K (Fact.out : 0 < m) (Fact.out : 0 < n) *
            criticalSourceRecipPolynomialIntegral K (Fact.out : 0 < m)
              (Fact.out : 0 < n)).coeff (n + (s' : ℕ) - ((finSumFinEquiv t : Fin (m + n)) : ℕ)))
        else 0
    | Sum.inr s' => if t = Sum.inr s' then 1 else 0

theorem criticalObservationJacobian_hvw_inr (s : Fin n) :
    KaehlerDifferential.D K
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (algebraMap
          (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (criticalObservationBlockCoord K (Sum.inr s)))
      = ∑ t : Fin m ⊕ Fin n,
          criticalObservationJacobian K t (Sum.inr s) • criticalRawDifferential K t := by
  classical
  have hsum : ∑ t : Fin m ⊕ Fin n,
      criticalObservationJacobian K t (Sum.inr s) • criticalRawDifferential K t
      = criticalRawDifferential K (Sum.inr s) := by
    rw [Finset.sum_eq_single (Sum.inr s)]
    · show (if (Sum.inr s : Fin m ⊕ Fin n) = Sum.inr s then (1 : _) else 0) • _ = _
      rw [if_pos rfl, one_smul]
    · intro t _ ht
      show (if t = (Sum.inr s : Fin m ⊕ Fin n) then (1 : _) else 0) • _ = 0
      rw [if_neg ht, zero_smul]
    · exact fun h => absurd (Finset.mem_univ _) h
  rw [hsum, criticalRawDifferential, criticalObservationBlockCoord]
  show KaehlerDifferential.D K
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (algebraMap
        (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (criticalObservationCoordSchur K (Sum.inl s)))
    = KaehlerDifferential.D K
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) _
  rw [algebraMap_criticalObservationCoordSchur_inl K]
  congr 2

end

end GaloisForLFunctions.HTGeometry
