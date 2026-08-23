import GaloisForLFunctions.HTGeometry.CriticalSheetLabelInertiaOrbit
import GaloisForLFunctions.HTGeometry.CriticalSchurInertiaOrderTwo
import GaloisForLFunctions.HTGeometry.CriticalSchurCollisionSupportFibre
import GaloisForLFunctions.HTGeometry.CriticalSchurRamificationIndex
import GaloisForLFunctions.HTGeometry.CriticalSchurCollisionInertia

/-!
# `(D)`: at most two sheets of the critical horizon collide

The canonical label fibre lies inside one orbit of the Schur inertia group, and that group has
order at most two.  Since every collision of the Schur reduction carries the canonical label, the
collision support has at most two elements.

```text
criticalSchur_collisionSupport_ncard_le_two
    ** |collision support| ≤ 2 **
```

No residue degree is computed: the label fibre is an inertia orbit because a Galois element with the
right place and the right residues differs from an inertia element only by something that fixes the
sheet's own field, and the residue degree cancels between the two levels of the tower.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]


/-- The range of a map out of a finite type is no bigger than the type. -/
theorem ncard_range_le_natCard {ι α : Type*} [Finite ι] (f : ι → α) :
    (Set.range f).ncard ≤ Nat.card ι := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_le_card_of_surjective (Set.rangeFactorization f) ?_
  rintro ⟨y, x, rfl⟩
  exact ⟨x, rfl⟩

noncomputable local instance collisionBoundSheetDecEq : DecidableEq (criticalGeometricSheet K m n) :=
  Classical.decEq _

/-- **The collision support of the Schur reduction has at most two elements.** -/
theorem criticalSchur_collisionSupport_ncard_le_two [DecidableEq K] (hm : 1 < m) (hn : 1 < n) :
    (collisionSupport (criticalGeometricSheetToSchurReducedFibre K hm hn)).ncard ≤ 2 := by
  classical
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
  set f : ((criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn)).inertiaSubgroup (criticalObservationField K m n))
      → criticalGeometricSheet K m n := fun i =>
    (((i : (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)).decompositionSubgroup (criticalObservationField K m n)) :
      criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
        criticalNormalClosure K m n)).toAlgHom.comp
      (criticalSourceNormalClosureEmbedding K m n) with hf
  have hsub : collisionSupport (criticalGeometricSheetToSchurReducedFibre K hm hn)
      ⊆ Set.range f := by
    intro σ hσ
    have hlabel : criticalGeometricSheetToSchurReducedFibre K hm hn σ
        = criticalGeometricSheetToSchurReducedFibre K hm hn
          (criticalSourceNormalClosureEmbedding K m n) :=
      criticalSchur_collisionSupport_reducedFibre_eq K hσ
        (criticalSourceNormalClosureEmbedding_mem_collisionSupport K hm hn)
    obtain ⟨i, hi, hiσ⟩ := criticalSchur_exists_inertiaSubgroup_comp_eq K hm hn rfl hlabel
    exact ⟨⟨i, hi⟩, (AlgHom.ext fun x => (hiσ x).symm)⟩
  refine le_trans (Set.ncard_le_ncard hsub (Set.finite_range f)) ?_
  refine le_trans (ncard_range_le_natCard f) (natCard_criticalSchurInertiaGroup_le_two K hm hn)

/-- **The critical geometric monodromy contains a literal transposition**, unconditionally.  The
Schur inertia group has order exactly two and at most two sheets collide, so its generator acts as a
single swap. -/
theorem exists_criticalGeometricMonodromy_isSwap (hm : 1 < m) (hn : 1 < n) :
    ∃ t : Equiv.Perm (criticalGeometricSheet K m n),
      t.IsSwap ∧ t ∈ criticalGeometricMonodromy K m n := by
  haveI : DecidableEq K := Classical.decEq K
  exact exists_criticalGeometricMonodromy_isSwap_of_collisionSupport_ncard_le_two_of_card K hm hn
    (natCard_criticalSchurInertiaGroup_eq_two K hm hn)
    (criticalSchur_collisionSupport_ncard_le_two K hm hn)

/-- **`(4)`: a primitive critical geometric monodromy of the horizon is the full symmetric
group.**  Everything except primitivity is now discharged. -/
theorem criticalGeometricMonodromy_eq_top_of_isPreprimitive
    (hprim : MulAction.IsPreprimitive (criticalGeometricMonodromy K m n)
      (criticalGeometricSheet K m n)) :
    criticalGeometricMonodromy K m n = ⊤ := by
  haveI : DecidableEq K := Classical.decEq K
  exact criticalGeometricMonodromy_eq_top_of_collision_of_isPreprimitive K
    (criticalSchur_collisionSupport_ncard_le_two K (Fact.out : 1 < m) (Fact.out : 1 < n)) hprim

end

end GaloisForLFunctions.HTGeometry
