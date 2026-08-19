import GaloisForLFunctions.HTGeometry.CriticalObservationJacobianDet
import GaloisForLFunctions.HTGeometry.CriticalSchurSourceCotangent
import GaloisForLFunctions.HTGeometry.KaehlerJacobianFactorization

/-!
# The Schur place of the critical horizon ramifies

Assembling the pieces: the cotangent basis of the source Schur place in block order, the generation
hypothesis, the two columns of the Jacobian factorization, and the non-unit determinant give

```text
criticalSchur_map_maximalIdeal_le_sq :
    𝔪(observation Schur place) · (source Schur place)  ⊆  𝔪(source Schur place)²
```

which is the statement that the ramification index of the source Schur place over the observation
Schur place is at least two — obligation `(R)` of the projective-horizon card, in local form.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial IsLocalRing KaehlerDifferential Polynomial Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- Block index equivalence with the Schur coordinate index. -/
def criticalBlockIndexEquiv : Fin m ⊕ Fin n ≃ Fin (m + n - 1 + 1) :=
  finSumFinEquiv.trans (finCongr (by have := (Fact.out : 0 < n); omega))

/-- The cotangent basis in block order. -/
noncomputable def criticalSchurBlockCotangentBasis :
    Module.Basis (Fin m ⊕ Fin n)
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      Ω[criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)⁄K] :=
  (criticalSchurSourceCotangentBasis K (Fact.out : 0 < m)
    (Fact.out : 0 < n)).reindex (criticalBlockIndexEquiv (m := m) (n := n)).symm

theorem criticalSchur_hgen_block
    (a : criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :
    KaehlerDifferential.D K
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (algebraMap _ _ a) ∈
      Submodule.span (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (Set.range fun s : Fin m ⊕ Fin n =>
          KaehlerDifferential.D K
            (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
            (algebraMap _ _ (criticalObservationBlockCoord K s))) := by
  have h := criticalSchur_hgen K a
  refine Submodule.span_mono ?_ h
  rintro _ ⟨s, rfl⟩
  refine ⟨Equiv.sumComm _ _ s, ?_⟩
  have hcoord : criticalObservationBlockCoord K (Equiv.sumComm (Fin n) (Fin m) s)
      = criticalObservationCoordSchur K s := by
    show criticalObservationCoordSchur K
      (Equiv.sumComm (Fin m) (Fin n) (Equiv.sumComm (Fin n) (Fin m) s)) = _
    congr 1
    exact Sum.swap_swap s
  show KaehlerDifferential.D K
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (algebraMap _ _ (criticalObservationBlockCoord K (Equiv.sumComm (Fin n) (Fin m) s))) = _
  rw [hcoord]

/-- **`(R)` in local form: the Schur place ramifies.**  The extended maximal ideal of the
observation Schur place lies in the square of the maximal ideal of the source Schur place. -/
theorem criticalSchur_map_maximalIdeal_le_sq :
    (maximalIdeal
        (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))).map
      (algebraMap
        (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)))
      ≤ (maximalIdeal
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))) ^ 2 :=
  map_maximalIdeal_le_sq_of_factorized_jacobian
    (criticalSchurBlockCotangentBasis K)
    (criticalObservationBlockCoord K)
    (criticalRawDifferential K)
    (criticalObservationJacobian K)
    (criticalSchur_hgen_block K)
    (fun s => by
      cases s with
      | inl s' => exact criticalObservationJacobian_hvw_inl K s'
      | inr s' => exact criticalObservationJacobian_hvw_inr K s')
    (not_isUnit_det_criticalObservationJacobian K)
    (criticalSchurObservation_map_maximalIdeal_ne_bot K Fact.out Fact.out)

end

end GaloisForLFunctions.HTGeometry
