import GaloisForLFunctions.HTGeometry.CriticalSchurInertiaCyclic
import GaloisForLFunctions.HTGeometry.CyclicRepStabilizerBound

/-!
# The order of the Schur inertia group, from the ramification of the sheets

```text
natCard_criticalSchurInertiaGroup_eq_sheet_mul'   the orbit–stabiliser product, folded
natCard_criticalSchurInertiaGroup_le_two_of_ramification
    ** every sheet over a place of ramification index ≤ 2  ⟹  |I| ≤ 2 **
```

This is the last group-theoretic step of the card's `(D)`.  It combines the orbit formula
(`CriticalSheetOrbitRamification`), cyclicity of tame inertia (`CriticalSchurInertiaCyclic`) and the
abstract bound `CyclicRepStabilizerBound.natCard_le_two_of_isCyclic_of_stabilizer_card`.

**Elaboration note, recorded because it cost a dozen rebuilds.**  On the horizon's sheet and
permutation types every `rw`, `show`, `change` and `MulAction.stabilizer` unfolding exhausts the
elaborator — a `rw` has to compute a motive over those types, and `MulAction.compHom` plus
`SetLike` membership is several unfolds deep.  The working discipline is: state every group-theoretic
step abstractly, phrase its hypothesis as a *cardinality inequality of naturals over a plain
subtype*, and instantiate with `Eq.trans_le` rather than `rw`.  The same theorem with
`MulAction.orbit` and `MulAction.stabilizer` in its statement does not elaborate at twenty million
heartbeats; this one takes seconds.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 3000000
set_option maxHeartbeats 8000000
set_option maxSynthPendingDepth 3

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}

/-- The orbit–stabiliser product, with the inertia group under its corpus name. -/
theorem natCard_criticalSchurInertiaGroup_eq_sheet_mul' (hm : 0 < m) (hn : 0 < n)
    (σ : criticalGeometricSheet K m n) :
    Nat.card (criticalSchurInertiaGroup K hm hn)
      = (ValuationInertia.intermediateCentre (AlgHom.fieldRange σ)
          (criticalNormalClosureSchurValuationSubring K hm hn)
          (criticalSchurNormalBase_algebraMap_mem K hm hn)).ramificationIdx
            (CriticalSchurNormalBaseRing K hm hn)
        * Nat.card {g : criticalSchurInertiaGroup K hm hn //
            criticalSchurInertiaAction K hm hn g σ = σ} :=
  natCard_criticalSchurInertiaGroup_eq_sheet_mul K hm hn σ

/-- **The order of the Schur inertia group from the ramification bound.** -/
theorem natCard_criticalSchurInertiaGroup_le_two_of_ramification (hm : 0 < m) (hn : 0 < n)
    (hram : ∀ σ : criticalGeometricSheet K m n,
      (ValuationInertia.intermediateCentre (AlgHom.fieldRange σ)
        (criticalNormalClosureSchurValuationSubring K hm hn)
        (criticalSchurNormalBase_algebraMap_mem K hm hn)).ramificationIdx
          (CriticalSchurNormalBaseRing K hm hn) ≤ 2) :
    Nat.card (criticalSchurInertiaGroup K hm hn) ≤ 2 := by
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm hn
  haveI : Finite (criticalSchurInertiaGroup K hm hn) := inferInstance
  haveI := isCyclic_criticalSchurInertiaGroup K hm hn
  refine natCard_le_two_of_isCyclic_of_stabilizer_card
    (criticalSchurInertiaAction K hm hn) (criticalSchurInertiaAction_injective K hm hn) ?_
  intro σ
  exact (natCard_criticalSchurInertiaGroup_eq_sheet_mul' K hm hn σ).trans_le
    (Nat.mul_le_mul_right _ (hram σ))

end

end GaloisForLFunctions.HTGeometry
