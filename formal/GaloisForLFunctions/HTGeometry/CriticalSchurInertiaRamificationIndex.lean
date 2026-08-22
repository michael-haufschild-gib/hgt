import GaloisForLFunctions.HTGeometry.ValuationInertiaRamificationIndex
import GaloisForLFunctions.HTGeometry.CriticalSchurIntegralClosurePlace

/-!
# The Schur inertia group has order the ramification index

The general dictionary of `ValuationInertiaRamificationIndex`, instantiated at the bottom of the
horizon's own tower: the observation Schur DVR, the critical normal closure, and the chosen upper
Schur valuation subring.

```text
ValuationSubring.ne_top_of_isDiscreteValuationRing   a DVR valuation subring is proper
criticalSchurNormalBase_algebraMap_mem
criticalSchurNormalBase_centre     the nonunits of the base are exactly its maximal ideal
natCard_criticalSchurInertiaGroup_eq_ramificationIdxIn
    ** Nat.card (criticalSchurInertiaGroup) = ramificationIdxIn (𝔪_A) (normal integral closure) **
```

The corpus previously had only the *injection* `criticalSchurIdealInertiaToInertia_injective`
together with `natCard_criticalSchurIdealInertiaGroup_eq_ramificationIdxIn`, i.e. `e ≤ |I|`.  The
equality is what the orbit count needs, because the orbit of a sheet is `|I|` divided by the order
of its stabiliser and both must be computed, not merely bounded.

The `centre` condition is the two halves of locality: a ring hom carries units to units, and
`criticalSchurObservationValuationToNormalClosure_isLocalHom` carries nonunits to nonunits.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing
open scoped Pointwise

set_option synthInstance.maxHeartbeats 3000000
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

/-- A valuation subring that is a discrete valuation ring is proper. -/
theorem ValuationSubring.ne_top_of_isDiscreteValuationRing {L : Type*} [Field L]
    (W : ValuationSubring L) [IsDiscreteValuationRing W] : W ≠ ⊤ := by
  intro h
  subst h
  refine IsDiscreteValuationRing.not_isField (↥(⊤ : ValuationSubring L)) ?_
  exact (Subring.topEquiv (R := L)).toMulEquiv.isField (Field.toIsField L)

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}

/-- The image of the observation Schur DVR in the normal closure, as an algebra map. -/
theorem criticalSchurNormalBase_algebraMap_mem (hm : 0 < m) (hn : 0 < n)
    (a : CriticalSchurNormalBaseRing K hm hn) :
    algebraMap (CriticalSchurNormalBaseRing K hm hn) (criticalNormalClosure K m n) a
      ∈ criticalNormalClosureSchurValuationSubring K hm hn :=
  criticalNormalClosureSchurValuationSubring_observation_mem K hm hn a

theorem criticalSchurNormalBase_centre (hm : 0 < m) (hn : 0 < n)
    (a : CriticalSchurNormalBaseRing K hm hn) :
    (¬ IsUnit (⟨algebraMap (CriticalSchurNormalBaseRing K hm hn)
        (criticalNormalClosure K m n) a,
      criticalSchurNormalBase_algebraMap_mem K hm hn a⟩ :
        criticalNormalClosureSchurValuationSubring K hm hn))
      ↔ a ∈ IsLocalRing.maximalIdeal (CriticalSchurNormalBaseRing K hm hn) := by
  have hcoe : (⟨algebraMap (CriticalSchurNormalBaseRing K hm hn)
      (criticalNormalClosure K m n) a,
      criticalSchurNormalBase_algebraMap_mem K hm hn a⟩ :
        criticalNormalClosureSchurValuationSubring K hm hn)
      = criticalSchurObservationValuationToNormalClosure K hm hn a := rfl
  rw [hcoe, IsLocalRing.mem_maximalIdeal]
  constructor
  · intro h hu
    exact h (hu.map (criticalSchurObservationValuationToNormalClosure K hm hn))
  · intro h hu
    exact h (IsLocalHom.map_nonunit (f := criticalSchurObservationValuationToNormalClosure K hm hn)
      a hu)

/-- **The Schur inertia group has order the ramification index of the Schur place.** -/
theorem natCard_criticalSchurInertiaGroup_eq_ramificationIdxIn (hm : 0 < m) (hn : 0 < n) :
    Nat.card (criticalSchurInertiaGroup K hm hn)
      = Ideal.ramificationIdxIn
          (IsLocalRing.maximalIdeal (CriticalSchurNormalBaseRing K hm hn))
          (CriticalSchurNormalIntegralClosure K hm hn) := by
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  haveI : IsScalarTower (criticalObservationField K m n) (criticalSourceField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    AlgebraicClosure.instIsScalarTower (criticalSourceField K m n)
  haveI : Algebra.IsAlgebraic (criticalObservationField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    Algebra.IsAlgebraic.trans (criticalObservationField K m n) (criticalSourceField K m n)
      (criticalSourceAlgebraicClosure K m n)
  haveI : Normal (criticalObservationField K m n) (criticalSourceAlgebraicClosure K m n) :=
    { splits' _ := IsAlgClosed.splits _ }
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm hn
  haveI : Normal (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    normalClosure.normal (criticalObservationField K m n) (criticalSourceField K m n)
      (criticalSourceAlgebraicClosure K m n)
  haveI : IsGalois (criticalObservationField K m n) (criticalNormalClosure K m n) := inferInstance
  exact ValuationInertia.natCard_inertiaSubgroup_eq_ramificationIdxIn
    (R := CriticalSchurNormalBaseRing K hm hn)
    (T := CriticalSchurNormalIntegralClosure K hm hn)
    (criticalObservationField K m n)
    (IsLocalRing.maximalIdeal (CriticalSchurNormalBaseRing K hm hn))
    (criticalNormalClosureSchurValuationSubring K hm hn)
    (ValuationSubring.ne_top_of_isDiscreteValuationRing _)
    (criticalSchurNormalBase_algebraMap_mem K hm hn)
    (criticalSchurNormalBase_centre K hm hn)

end

end GaloisForLFunctions.HTGeometry
