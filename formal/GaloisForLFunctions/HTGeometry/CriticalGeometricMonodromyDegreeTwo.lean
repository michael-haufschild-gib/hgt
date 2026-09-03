import GaloisForLFunctions.HTGeometry.CriticalGeometricMonodromyJordan
import GaloisForLFunctions.HTGeometry.CriticalGeometricDegreeExact
import GaloisForLFunctions.HTGeometry.CriticalGeometricMonodromyTransitive
import GaloisForLFunctions.HTGeometry.CriticalOneStepRigidity

/-!
# The two-sheet critical horizon

A transitive permutation group on a two-element set is the full permutation group.  The exact
critical degree therefore closes the exceptional `(1,1)` horizon directly, without a ramification
or Kummer argument.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem subgroup_eq_top_of_card_two_of_isPretransitive
    {X : Type*} [Fintype X] (H : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 2) [MulAction.IsPretransitive H X] : H = ⊤ := by
  classical
  obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card X)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H x y
  change (g : Equiv.Perm X) x = y at hg
  have huniv : (Finset.univ : Finset X) = {x, y} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcard, Finset.card_pair hxy]
  have hall (z : X) : z = x ∨ z = y := by
    have hz : z ∈ ({x, y} : Finset X) := by
      rw [← huniv]
      exact Finset.mem_univ z
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hz
  have hgy : (g : Equiv.Perm X) y = x := by
    rcases hall ((g : Equiv.Perm X) y) with h | h
    · exact h
    · exfalso
      apply hxy
      exact (g : Equiv.Perm X).injective (hg.trans h.symm)
  have hperm : (g : Equiv.Perm X) = Equiv.swap x y := by
    apply Equiv.Perm.ext
    intro z
    rcases hall z with rfl | rfl
    · simpa using hg
    · simpa using hgy
  rw [Subgroup.eq_top_iff']
  intro σ
  by_cases hσ : σ = 1
  · simpa [hσ]
  · have hσx : σ x = y := by
      rcases hall (σ x) with h | h
      · exfalso
        apply hσ
        have hσy : σ y = y := by
          rcases hall (σ y) with h' | h'
          · exfalso
            apply hxy
            exact σ.injective (h.trans h'.symm)
          · exact h'
        apply Equiv.Perm.ext
        intro z
        rcases hall z with rfl | rfl
        · simpa [h]
        · simpa [hσy]
      · exact h
    have hσeq : σ = Equiv.swap x y := by
      have hσy : σ y = x := by
        rcases hall (σ y) with h | h
        · exact h
        · exfalso
          apply hxy
          exact σ.injective (hσx.trans h.symm)
      apply Equiv.Perm.ext
      intro z
      rcases hall z with rfl | rfl
      · simpa [hσx]
      · simpa [hσy]
    rw [hσeq, ← hperm]
    exact g.property

/-- The exceptional two-sheet critical horizon has full symmetric monodromy over every
algebraically closed field of characteristic zero. -/
theorem criticalGeometricMonodromy_one_one_eq_top
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] :
    criticalGeometricMonodromy K 1 1 = ⊤ := by
  letI : Finite (criticalGeometricSheet K 1 1) :=
    finite_criticalGeometricSheet K (by omega) (by omega)
  letI : Fintype (criticalGeometricSheet K 1 1) := Fintype.ofFinite _
  letI : MulAction.IsPretransitive (criticalGeometricMonodromy K 1 1)
      (criticalGeometricSheet K 1 1) :=
    criticalGeometricMonodromy_isPretransitive K (by omega) (by omega)
  apply subgroup_eq_top_of_card_two_of_isPretransitive
  rw [← Nat.card_eq_fintype_card,
    natCard_criticalGeometricSheet_eq_criticalHorizonMultiplicity K (by omega) (by omega)]
  simp [criticalHorizonMultiplicity]

/-- One-step postcritical rigidity for the exceptional two-sheet horizon, over every algebraically
closed field of characteristic zero. -/
theorem criticalObservation_sup_postcritical_eq_criticalSourceFieldSup_one_one
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] :
    criticalObservationField K 1 1
        ⊔ IntermediateField.adjoin K {postcriticalRawFieldElement K 1 1}
        ⊔ IntermediateField.adjoin K {postcriticalReciprocalFieldElement K 1 1}
      = criticalSourceFieldSup K 1 1 :=
  criticalObservation_sup_postcritical_eq_criticalSourceFieldSup K
    (by omega) (by omega) (criticalGeometricMonodromy_one_one_eq_top K)

end

end GaloisForLFunctions.HTGeometry
