import GaloisForLFunctions.HTGeometry.CriticalSchurCollisionSupportBound
import GaloisForLFunctions.HTGeometry.TranspositionBlockInvariance
import GaloisForLFunctions.HTGeometry.ValuationInertiaIntermediateUnramified
import GaloisForLFunctions.HTGeometry.CriticalSheetOrbitRamification

/-!
# The block field of the critical horizon is unramified at the Schur place

The Schur meridian acts on sheets as one transposition, a transposition preserves every block with
at least two elements, so Schur inertia lies in the stabiliser of every such block.  The field fixed
by that stabiliser is therefore unramified at the Schur place.

```text
criticalBlockStabilizer                      the stabiliser of a block inside the Galois group
criticalSchurInertia_smul_block_eq           inertia preserves a block of size at least two
criticalSchurInertia_le_blockStabilizer
criticalSchurInertia_ramificationIdx_blockField_eq_one
    ** `E3` at the Schur place **
```

Combined with `isUnramifiedAt_of_aeval_derivative_notMem` — which handles every height-one prime of
the chart away from the Jacobian divisor — the block field is unramified at every height-one prime
of the chart ring, which is what the torus/slice reduction consumes.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MulAction
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]


noncomputable local instance criticalBlockSheetDecEq : DecidableEq (criticalGeometricSheet K m n) :=
  Classical.decEq _

/-- **Schur inertia preserves every block of the monodromy action with at least two elements.** -/
theorem criticalSchurInertia_smul_block_eq [DecidableEq K] (hm : 1 < m) (hn : 1 < n)
    {B : Set (criticalGeometricSheet K m n)}
    (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
    (hB2 : ∃ x ∈ B, ∃ y ∈ B, x ≠ y)
    (g : ((criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn)).inertiaSubgroup (criticalObservationField K m n))) :
    criticalSchurInertiaAction K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g • B = B := by
  refine isBlock_perm_smul_eq_of_eq_one_or_isSwap hB ?_ ?_ hB2
  · exact criticalSchurInertiaAction_range_le_monodromy K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn) ⟨g, rfl⟩
  · exact criticalSchurInertiaAction_eq_one_or_isSwap_of_collisionSupport_ncard_le_two K hm hn
      (criticalSchur_collisionSupport_ncard_le_two K hm hn) g

/-- The stabiliser, inside the Galois group of the normal closure, of a block of sheets. -/
noncomputable def criticalBlockStabilizer (B : Set (criticalGeometricSheet K m n)) :
    Subgroup (criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
      criticalNormalClosure K m n) :=
  (MulAction.stabilizer (Equiv.Perm (criticalGeometricSheet K m n)) B).comap
    (criticalNormalClosureAction K m n)

/-- **Schur inertia lies in the stabiliser of every block with at least two elements.** -/
theorem criticalSchurInertia_le_blockStabilizer [DecidableEq K] (hm : 1 < m) (hn : 1 < n)
    {B : Set (criticalGeometricSheet K m n)}
    (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
    (hB2 : ∃ x ∈ B, ∃ y ∈ B, x ≠ y)
    (g : ((criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn)).decompositionSubgroup (criticalObservationField K m n)))
    (hg : g ∈ (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn)).inertiaSubgroup (criticalObservationField K m n)) :
    ((g : criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
      criticalNormalClosure K m n)) ∈ criticalBlockStabilizer K B :=
  criticalSchurInertia_smul_block_eq K hm hn hB hB2 ⟨g, hg⟩

/-- **`E3` on the horizon: the block field is unramified at the Schur place.** -/
theorem criticalSchurInertia_ramificationIdx_blockField_eq_one [DecidableEq K] (hm : 1 < m) (hn : 1 < n)
    {B : Set (criticalGeometricSheet K m n)}
    (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
    (hB2 : ∃ x ∈ B, ∃ y ∈ B, x ≠ y) :
    (ValuationInertia.intermediateCentre
        (IntermediateField.fixedField (criticalBlockStabilizer K B))
        (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn))
        (criticalSchurNormalBase_algebraMap_mem K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn))).ramificationIdx
      (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) = 1 := by
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
  haveI := criticalNormalClosure_isGalois K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
  haveI := criticalIntermediateCentre_charZero K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
    (IntermediateField.fixedField (criticalBlockStabilizer K B))
    (ValuationInertia.intermediateCentre
      (IntermediateField.fixedField (criticalBlockStabilizer K B))
      (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn))
      (criticalSchurNormalBase_algebraMap_mem K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)))
  exact ValuationInertia.ramificationIdx_fixedField_eq_one_of_inertia_le
    (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
    (criticalBlockStabilizer K B)
    (criticalSchurNormalBase_algebraMap_mem K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
    (ValuationSubring.ne_top_of_isDiscreteValuationRing _)
    (IsLocalRing.maximalIdeal
      (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)))
    (IsDiscreteValuationRing.not_a_field _)
    (criticalSchurNormalBase_centre K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
    (fun g => criticalSchurInertia_le_blockStabilizer K hm hn hB hB2
      (g : (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)).decompositionSubgroup (criticalObservationField K m n)) g.2)

end

end GaloisForLFunctions.HTGeometry
