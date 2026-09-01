import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms
import GaloisForLFunctions.RHTower.FiniteQuantumObserverGraphSharpness
import GaloisForLFunctions.RHTower.FiniteLocalizedSpectralSupportRecurrenceLaw

/-!
# Finite target profiles for observer-coherence graphs

Closed finite-volume isoperimetric applications of arXiv:2603.03257 to observer graphs.
-/

namespace RHTower

/-- Observer family is empty, or one record carries at least the average directed coherence
weight of a fixed sector pair. -/
theorem finiteObserverUnionWeight_empty_or_exists_averageRecord
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ) (i j : Fin d) :
    Fintype.card J = 0 ∨ ∃ a : J,
      finiteObserverUnionWeight lam block i j ≤
        (Fintype.card J : ℝ) * (lam a * ‖block a i j‖ ^ 2) := by
  simpa [finiteObserverUnionWeight] using
    (GaloisForLFunctions.HTGeometry.finiteFamilySum_empty_or_le_card_mul
      (fun a : J ↦ lam a * ‖block a i j‖ ^ 2))

/-- Every finite observer system either has no coherence edge, or some coherent pair has strictly
positive target-avoiding anchored profile. -/
theorem finiteObserverCoherenceGraph_edgeless_or_exists_positiveTargetProfile
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ) :
    (∀ i j, ¬(finiteObserverCoherenceGraph lam block).Adj i j) ∨
      ∃ i j,
        0 < GaloisForLFunctions.HTGeometry.targetAvoidingIsoperimetricProfile
          (finiteObserverCoherenceGraph lam block) {i} {j} := by
  classical
  by_cases hedge : ∃ i j, (finiteObserverCoherenceGraph lam block).Adj i j
  · right
    obtain ⟨i, j, hij⟩ := hedge
    exact ⟨i, j,
      GaloisForLFunctions.HTGeometry.targetAvoidingIsoperimetricProfile_pos_of_adj
        (finiteObserverCoherenceGraph lam block) hij⟩
  · left
    intro i j hij
    exact hedge ⟨i, j, hij⟩

/-- The canonical two-sector uniform pure observer has positive finite-volume profile from sector
`0` to sector `1`.  Its complete coherence graph cannot evade the target without cutting an edge. -/
theorem uniformPureObserver_two_targetAvoidingIsoperimetricProfile_pos :
    0 < GaloisForLFunctions.HTGeometry.targetAvoidingIsoperimetricProfile
      (finiteObserverCoherenceGraph uniformPureObserverWeight
        (uniformPureObserverBlock 2))
      ({(0 : Fin 2)} : Finset (Fin 2)) ({(1 : Fin 2)} : Finset (Fin 2)) := by
  apply GaloisForLFunctions.HTGeometry.targetAvoidingIsoperimetricProfile_pos_of_adj
  rw [uniformPureObserver_coherenceGraph_eq_top (by norm_num)]
  simp

/-- A localized spectral support has fewer than two vertices, or it contains a pair separated by
positive finite-volume profile inside its selected clique. -/
theorem finiteLocalizedSpectralSupportGraph_small_or_exists_positiveTargetProfile
    {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    S.card < 2 ∨ ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
      0 < GaloisForLFunctions.HTGeometry.targetAvoidingIsoperimetricProfile
        (finiteLocalizedSpectralSupportGraph S) {i} {j} := by
  by_cases hcard : 2 ≤ S.card
  · right
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    refine ⟨i, hi, j, hj, hij, ?_⟩
    apply GaloisForLFunctions.HTGeometry.targetAvoidingIsoperimetricProfile_pos_of_adj
    exact ⟨hij, hi, hj⟩
  · left
    omega

end RHTower
