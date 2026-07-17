import Mathlib.Combinatorics.Matroid.Minor.Contract

/-!
# Wick-contracted interaction matroids

This module retains the full matroid structure behind a finite Wick-reduced transcendence-rank
profile.  A selected base packet is contracted, and the result is restricted to the signal
labels.  Elements already in the closure of the base become loops.  Enlarging the base by a
disjoint closure-neutral counterterm packet leaves the entire signal matroid unchanged, not only
its total rank.

The statements are generic matroid infrastructure.  In the QFT application, the ambient matroid
is the comap of an algebraic matroid along a labeled connected-correlator evaluation map, the base
contains the face-complete Gaussian/Wick data, and the signal contains higher connected jets.
-/

open Matroid Set

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*}

/-- Contract a selected base packet and retain only the labeled signal ground set. -/
def wickContractedInteractionMatroid
    (M : Matroid α) (base signal : Set α) : Matroid α :=
  (M ／ base) ↾ signal

private theorem delete_restrict_eq_of_disjoint
    (M : Matroid α) {deleted retained : Set α}
    (hdisj : Disjoint deleted retained) :
    (M ＼ deleted) ↾ retained = M ↾ retained := by
  apply Matroid.ext_indep
  · simp
  · intro I _hI
    rw [Matroid.restrict_indep_iff, Matroid.delete_indep_iff,
      Matroid.restrict_indep_iff]
    constructor
    · rintro ⟨⟨hMI, _⟩, hIR⟩
      exact ⟨hMI, hIR⟩
    · rintro ⟨hMI, hIR⟩
      exact ⟨⟨hMI, hdisj.symm.mono_left hIR⟩, hIR⟩

/-- If every signal label lies in the closure of a disjoint base, Wick contraction turns the
complete signal restriction into the loopy matroid. -/
theorem wickContractedInteractionMatroid_eq_loopyOn_of_signal_subset_closure
    (M : Matroid α) {base signal : Set α}
    (hdisj : Disjoint signal base) (hclosure : signal ⊆ M.closure base) :
    wickContractedInteractionMatroid M base signal = Matroid.loopyOn signal := by
  apply (M ／ base).restrict_subset_loops_eq
  rw [Matroid.contract_loops_eq]
  intro e heS
  exact ⟨hclosure heS, fun heB ↦ Set.disjoint_left.1 hdisj heS heB⟩

/-- **Full counterterm neutrality.**  Contracting extra counterterm labels that already lie in
the closure of a disjoint base preserves the entire matroid on any disjoint signal set. -/
theorem wickContractedInteractionMatroid_eq_of_counterterms_subset_closure
    (M : Matroid α) {base counterterms signal : Set α}
    (hcounterBase : Disjoint counterterms base)
    (hcounterSignal : Disjoint counterterms signal)
    (hclosure : counterterms ⊆ M.closure base) :
    wickContractedInteractionMatroid M (base ∪ counterterms) signal =
      wickContractedInteractionMatroid M base signal := by
  have hloops : counterterms ⊆ (M ／ base).loops := by
    rw [Matroid.contract_loops_eq]
    intro e heC
    exact ⟨hclosure heC, fun heB ↦ Set.disjoint_left.1 hcounterBase heC heB⟩
  unfold wickContractedInteractionMatroid
  rw [← Matroid.contract_contract]
  rw [Matroid.contract_eq_delete_of_subset_loops hloops]
  exact delete_restrict_eq_of_disjoint (M ／ base) hcounterSignal

end GaloisForLFunctions.HTGeometry
