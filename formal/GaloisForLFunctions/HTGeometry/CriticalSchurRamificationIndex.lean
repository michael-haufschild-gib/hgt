import GaloisForLFunctions.HTGeometry.CriticalSchurNormalRamifies
import GaloisForLFunctions.HTGeometry.CriticalSchurRamificationInertia

/-!
# The ramification index at the Schur place of the critical horizon

Ruling out ramification index zero (the prime lies over a nonzero prime) and ramification index one
(the extended maximal ideal is not the maximal ideal of the localization) leaves

```text
criticalSchur_two_le_ramificationIdxIn
    ** 2 ≤ ramificationIdxIn 𝔪(observation Schur place) (normal integral closure) **
criticalSchurInertiaGroup_nontrivial
```

and therefore discharges the ramification hypothesis of the endgame: full symmetric monodromy now
follows from the reduction-degree count (or the collision count) together with primitivity alone.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000

noncomputable local instance sheetDecEqRamificationBound (K : Type*) [Field K] (m n : ℕ) :
    DecidableEq (criticalGeometricSheet K m n) := Classical.decEq _

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- The ramification index of the Schur prime of the normal integral closure is at least two. -/
theorem criticalSchur_two_le_ramificationIdx' :
    2 ≤ Ideal.ramificationIdx'
      (maximalIdeal (CriticalSchurNormalBaseRing K (Fact.out : 0 < m) (Fact.out : 0 < n)))
      (criticalSchurNormalIntegralClosurePrime K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
  haveI hlies :
      (criticalSchurNormalIntegralClosurePrime K (Fact.out : 0 < m) (Fact.out : 0 < n)).LiesOver
        (maximalIdeal (CriticalSchurNormalBaseRing K (Fact.out : 0 < m) (Fact.out : 0 < n))) :=
    criticalSchurNormalIntegralClosurePrime_liesOver K (Fact.out : 0 < m) (Fact.out : 0 < n)
  have hp : maximalIdeal
      (CriticalSchurNormalBaseRing K (Fact.out : 0 < m) (Fact.out : 0 < n)) ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field _
  have hpP : (maximalIdeal
        (CriticalSchurNormalBaseRing K (Fact.out : 0 < m) (Fact.out : 0 < n))).map
        (algebraMap (CriticalSchurNormalBaseRing K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (CriticalSchurNormalIntegralClosure K (Fact.out : 0 < m) (Fact.out : 0 < n)))
      ≤ criticalSchurNormalIntegralClosurePrime K (Fact.out : 0 < m) (Fact.out : 0 < n) :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq hlies.over)
  have h0 := Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
    (criticalSchurNormalIntegralClosurePrime K (Fact.out : 0 < m) (Fact.out : 0 < n)) hp
  have h1 : Ideal.ramificationIdx'
      (maximalIdeal (CriticalSchurNormalBaseRing K (Fact.out : 0 < m) (Fact.out : 0 < n)))
      (criticalSchurNormalIntegralClosurePrime K (Fact.out : 0 < m) (Fact.out : 0 < n)) ≠ 1 := by
    rw [Ne, Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff
      (criticalSchurNormalIntegralClosurePrime_ne_bot K (Fact.out : 0 < m) (Fact.out : 0 < n))
      hpP]
    exact criticalSchur_map_maximalIdeal_localization_ne K
  omega

/-- **`(R)`: the Schur place of the critical horizon ramifies.**  The common ramification index of
the primes of the normal integral closure over the observation Schur place is at least two. -/
theorem criticalSchur_two_le_ramificationIdxIn :
    2 ≤ Ideal.ramificationIdxIn
      (maximalIdeal (CriticalSchurNormalBaseRing K (Fact.out : 0 < m) (Fact.out : 0 < n)))
      (CriticalSchurNormalIntegralClosure K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
  let F := criticalObservationField K m n
  let E := criticalSourceField K m n
  let L := criticalNormalClosure K m n
  let O := CriticalSchurNormalBaseRing K (Fact.out : 0 < m) (Fact.out : 0 < n)
  let S := CriticalSchurNormalIntegralClosure K (Fact.out : 0 < m) (Fact.out : 0 < n)
  let p := IsLocalRing.maximalIdeal O
  let P := criticalSchurNormalIntegralClosurePrime K (Fact.out : 0 < m) (Fact.out : 0 < n)
  let G := L ≃ₐ[F] L
  haveI : FiniteDimensional F E :=
    criticalSourceField_finiteDimensional_criticalObservationField K
      (Fact.out : 0 < m) (Fact.out : 0 < n)
  haveI : Algebra.IsSeparable F E := inferInstance
  haveI : IsScalarTower F E (criticalSourceAlgebraicClosure K m n) :=
    AlgebraicClosure.instIsScalarTower E
  haveI : Algebra.IsAlgebraic F (criticalSourceAlgebraicClosure K m n) :=
    Algebra.IsAlgebraic.trans F E (criticalSourceAlgebraicClosure K m n)
  haveI : Normal F (criticalSourceAlgebraicClosure K m n) :=
    { splits' _ := IsAlgClosed.splits _ }
  haveI : FiniteDimensional F L :=
    criticalNormalClosure_finiteDimensional K (Fact.out : 0 < m) (Fact.out : 0 < n)
  haveI : Normal F L :=
    normalClosure.normal F E (criticalSourceAlgebraicClosure K m n)
  haveI : IsGalois F L := inferInstance
  haveI : IsGaloisGroup G O S := IsGaloisGroup.of_isFractionRing G O S F L
  haveI : Finite G := IsGaloisGroup.finite G O S
  haveI : Module.Flat O S := inferInstance
  haveI : P.LiesOver p :=
    criticalSchurNormalIntegralClosurePrime_liesOver K (Fact.out : 0 < m) (Fact.out : 0 < n)
  have hp : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P G,
    ← Ideal.ramificationIdx'_eq_ramificationIdx p P hp]
  exact criticalSchur_two_le_ramificationIdx' K

/-- **The Schur inertia group of the critical horizon is nontrivial**, unconditionally. -/
instance criticalSchurInertiaGroup_nontrivial :
    Nontrivial (criticalSchurInertiaGroup K (Fact.out : 0 < m) (Fact.out : 0 < n)) :=
  nontrivial_criticalSchurInertiaGroup_of_ramificationIdx K
    (Fact.out : 0 < m) (Fact.out : 0 < n) (criticalSchur_two_le_ramificationIdxIn K)

/-- **The reduction-degree count alone produces the transposition.** -/
theorem exists_criticalGeometricMonodromy_isSwap_of_degree
    (hdeg : Nat.card (criticalGeometricSheet K m n)
      ≤ (Set.range (criticalGeometricSheetToSchurReducedFibre K
          (Fact.out : 1 < m) (Fact.out : 1 < n))).ncard + 1) :
    ∃ τ : Equiv.Perm (criticalGeometricSheet K m n),
      τ.IsSwap ∧ τ ∈ criticalGeometricMonodromy K m n :=
  exists_criticalGeometricMonodromy_isSwap_of_ramification_of_degree K
    (Fact.out : 1 < m) (Fact.out : 1 < n) (criticalSchur_two_le_ramificationIdxIn K) hdeg

/-- **The endgame with ramification discharged.**  The reduction-degree count and primitivity give
full symmetric monodromy. -/
theorem criticalGeometricMonodromy_eq_top_of_degree_of_isPreprimitive
    (hdeg : Nat.card (criticalGeometricSheet K m n)
      ≤ (Set.range (criticalGeometricSheetToSchurReducedFibre K
          (Fact.out : 1 < m) (Fact.out : 1 < n))).ncard + 1)
    (hprim : MulAction.IsPreprimitive (criticalGeometricMonodromy K m n)
      (criticalGeometricSheet K m n)) :
    criticalGeometricMonodromy K m n = ⊤ :=
  criticalGeometricMonodromy_eq_top_of_ramification_of_degree_of_isPreprimitive K
    (Fact.out : 1 < m) (Fact.out : 1 < n) (criticalSchur_two_le_ramificationIdxIn K) hdeg hprim

/-- **The endgame in collision form, with ramification discharged.** -/
theorem criticalGeometricMonodromy_eq_top_of_collision_of_isPreprimitive
    (hcollision : (collisionSupport (criticalGeometricSheetToSchurReducedFibre K
      (Fact.out : 1 < m) (Fact.out : 1 < n))).ncard ≤ 2)
    (hprim : MulAction.IsPreprimitive (criticalGeometricMonodromy K m n)
      (criticalGeometricSheet K m n)) :
    criticalGeometricMonodromy K m n = ⊤ :=
  criticalGeometricMonodromy_eq_top_of_ramification_of_collision_of_isPreprimitive K
    (Fact.out : 1 < m) (Fact.out : 1 < n) (criticalSchur_two_le_ramificationIdxIn K)
    hcollision hprim

end

end GaloisForLFunctions.HTGeometry
