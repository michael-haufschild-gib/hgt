import GaloisForLFunctions.HTGeometry.Critical.Geometric.MonodromyFaithful
import GaloisForLFunctions.HTGeometry.Critical.Normal.ClosureSchurValuation
import GaloisForLFunctions.HTGeometry.PermutationCollisionInertia

/-!
# Actual Schur inertia acting on actual critical sheets

The decomposition and inertia subgroups of the chosen Schur place are literal subgroups of the
Galois group of the actual normal closure.  Restricting the normal-closure action gives their
permutation actions on the concrete geometric sheets.  The inertia action is faithful and its image
lies in actual geometric monodromy.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 200000

/-- Permutation action of the Schur decomposition group on actual geometric sheets. -/
noncomputable def criticalSchurDecompositionAction
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSchurDecompositionGroup K hm hn →*
      Equiv.Perm (criticalGeometricSheet K m n) :=
  (criticalNormalClosureAction K m n).comp
    (criticalSchurDecompositionGroup K hm hn).subtype

/-- Permutation action of the Schur inertia group on actual geometric sheets. -/
noncomputable def criticalSchurInertiaAction
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSchurInertiaGroup K hm hn →*
      Equiv.Perm (criticalGeometricSheet K m n) :=
  (criticalSchurDecompositionAction K hm hn).comp
    (criticalSchurInertiaGroup K hm hn).subtype

/-- Every actual Schur inertia permutation belongs to actual geometric monodromy. -/
theorem criticalSchurInertiaAction_range_le_monodromy
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    MonoidHom.range (criticalSchurInertiaAction K hm hn) ≤
      criticalGeometricMonodromy K m n := by
  rintro _ ⟨g, rfl⟩
  refine ⟨((g : criticalSchurDecompositionGroup K hm hn) :
    criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
      criticalNormalClosure K m n), rfl⟩

/-- The actual Schur inertia action on sheets is faithful. -/
theorem criticalSchurInertiaAction_injective
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Function.Injective (criticalSchurInertiaAction K hm hn) := by
  intro g h hgh
  apply Subtype.ext
  apply Subtype.ext
  exact criticalNormalClosureAction_injective K hm hn hgh

/-- The inertia group and its concrete permutation image have the same cardinality. -/
theorem natCard_criticalSchurInertiaAction_range
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Nat.card (MonoidHom.range (criticalSchurInertiaAction K hm hn)) =
      Nat.card (criticalSchurInertiaGroup K hm hn) := by
  exact Nat.card_congr
    (Equiv.ofInjective (criticalSchurInertiaAction K hm hn)
      (criticalSchurInertiaAction_injective K hm hn)).symm

noncomputable local instance criticalGeometricSheetDecidableEq
    (K : Type*) [Field K] (m n : ℕ) :
    DecidableEq (criticalGeometricSheet K m n) :=
  Classical.decEq _

/-- **Simple nontrivial inertia produces an actual geometric transposition.**  If every element of
the Schur inertia group acts either trivially or by one swap, nontriviality of that inertia group
and faithfulness of its action select a genuine swap in actual geometric monodromy. -/
theorem exists_criticalGeometricMonodromy_isSwap_of_simple_nontrivial_inertia
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    [Nontrivial (criticalSchurInertiaGroup K hm hn)]
    (hsimple : ∀ g : criticalSchurInertiaGroup K hm hn,
      criticalSchurInertiaAction K hm hn g = 1 ∨
        (criticalSchurInertiaAction K hm hn g).IsSwap) :
    ∃ τ : Equiv.Perm (criticalGeometricSheet K m n),
      τ.IsSwap ∧ τ ∈ criticalGeometricMonodromy K m n := by
  classical
  obtain ⟨g, hg⟩ := exists_ne (1 : criticalSchurInertiaGroup K hm hn)
  have haction : criticalSchurInertiaAction K hm hn g ≠ 1 := by
    intro h
    apply hg
    apply criticalSchurInertiaAction_injective K hm hn
    simpa using h
  rcases hsimple g with htrivial | hswap
  · exact absurd htrivial haction
  · refine ⟨criticalSchurInertiaAction K hm hn g, hswap, ?_⟩
    exact criticalSchurInertiaAction_range_le_monodromy K hm hn ⟨g, rfl⟩

end

end GaloisForLFunctions.HTGeometry
