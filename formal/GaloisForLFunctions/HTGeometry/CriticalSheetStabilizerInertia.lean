import GaloisForLFunctions.HTGeometry.CriticalSchurInertiaAction
import GaloisForLFunctions.HTGeometry.ValuationInertiaIntermediateField
import Mathlib.FieldTheory.Galois.Basic

/-!
# The stabiliser of a sheet is an inertia group

A geometric sheet `σ` is fixed by a normal-closure automorphism exactly when that automorphism fixes
`σ`'s image field pointwise.  Combined with `ValuationInertiaIntermediateField` this identifies the
stabiliser of `σ` inside the Schur inertia group with the inertia group of `AlgHom.fieldRange σ`:

```text
criticalNormalClosureAction_eq_self_iff      the sheet is fixed ⟺ its field range is fixed
criticalSchurInertiaGroup_eq                 the corpus's inertia group IS the valuation one
criticalSchurInertiaAction_apply
natCard_sheetStabilizer_eq_natCard_inertiaSubgroup
    ** |Stab_I(σ)| = |W.inertiaSubgroup (fieldRange σ)| **
```

With `ValuationInertiaRamificationIndex.natCard_inertiaSubgroup_eq_ramificationIdxIn` at both the
observation field and `fieldRange σ`, and `ramificationIdxIn_tower` between them, this makes the
`I`-orbit of a sheet equal to the ramification index of the place `σ` sits over.

Two elaboration notes.  The field stack of the critical horizon is heavy enough that the default
instance budget times out on `IsLocalRing.ResidueField`-level unfolding, so the heartbeat options are
raised.  And the last step must not be a `rw`: computing the motive for
`natCard_inertiaSubgroup_intermediate` blows the `isDefEq` budget, while `Eq.trans` against the same
lemma costs nothing.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

variable (K : Type*) [Field K] [CharZero K] (m n : ℕ)

/-- **A sheet is fixed by a normal-closure automorphism exactly when that automorphism fixes the
field the sheet generates.** -/
theorem criticalNormalClosureAction_eq_self_iff
    (τ : criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
      criticalNormalClosure K m n)
    (σ : criticalGeometricSheet K m n) :
    criticalNormalClosureAction K m n τ σ = σ ↔
      τ ∈ (AlgHom.fieldRange σ).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    obtain ⟨y, rfl⟩ := hx
    exact congrFun (congrArg (fun f : criticalSourceField K m n →ₐ[criticalObservationField K m n]
      criticalNormalClosure K m n => (f : criticalSourceField K m n → criticalNormalClosure K m n))
      h) y
  · intro h
    apply AlgHom.ext
    intro y
    exact h (σ y) ⟨y, rfl⟩

theorem criticalSchurInertiaGroup_eq (hm : 0 < m) (hn : 0 < n) :
    criticalSchurInertiaGroup K hm hn
      = (criticalNormalClosureSchurValuationSubring K hm hn).inertiaSubgroup
          (criticalObservationField K m n) := rfl

theorem criticalSchurInertiaAction_apply (hm : 0 < m) (hn : 0 < n)
    (g : criticalSchurInertiaGroup K hm hn) (σ : criticalGeometricSheet K m n) :
    criticalSchurInertiaAction K hm hn g σ
      = criticalNormalClosureAction K m n
          ((g : criticalSchurDecompositionGroup K hm hn) :
            criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
              criticalNormalClosure K m n) σ := rfl

/-- **The stabiliser of a sheet inside the Schur inertia group is the inertia group of the field
that sheet generates.** -/
theorem natCard_sheetStabilizer_eq_natCard_inertiaSubgroup
    (hm : 0 < m) (hn : 0 < n) (σ : criticalGeometricSheet K m n) :
    Nat.card {g : (criticalNormalClosureSchurValuationSubring K hm hn).inertiaSubgroup
        (criticalObservationField K m n) //
        criticalSchurInertiaAction K hm hn g σ = σ}
      = Nat.card ((criticalNormalClosureSchurValuationSubring K hm hn).inertiaSubgroup
          (AlgHom.fieldRange σ)) := by
  have hgen := ValuationInertia.natCard_inertiaSubgroup_intermediate
    (criticalNormalClosureSchurValuationSubring K hm hn) (AlgHom.fieldRange σ)
  refine Eq.trans ?_ hgen.symm
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [criticalSchurInertiaAction_apply K m n hm hn g σ,
    criticalNormalClosureAction_eq_self_iff, IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x => h (x : criticalNormalClosure K m n) x.property,
    fun h x hx => h ⟨x, hx⟩⟩

end

end GaloisForLFunctions.HTGeometry
