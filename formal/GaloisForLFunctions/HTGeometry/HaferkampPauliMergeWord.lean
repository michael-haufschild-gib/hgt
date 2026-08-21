import GaloisForLFunctions.HTGeometry.HaferkampPauliMergeSchedule

/-!
# Certified execution of an ordered Pauli merge word

An Appendix-B light-cone block supplies a fixed time-ordered list of distinct
two-qubit locations.  This module turns any such list into a certified merge
schedule.  Identity pairs are skipped; every emitted location has the exact
nonidentity witness needed by the closed local `SU(4)` transport theorem.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A genuine directed two-qubit location. -/
abbrev PauliMergeEdge (Q : Type*) := { e : Q × Q // e.1 ≠ e.2 }

namespace PauliMergeEdge

/-- Forget the location certificate. -/
def pair {Q : Type*} : PauliMergeEdge Q → Q × Q := Subtype.val

end PauliMergeEdge

namespace PauliMergeSchedule

/-- Execute an ordered word of genuine two-qubit locations.  An identity pair
needs no gate; otherwise the local exact transport is recorded as one merge
step. -/
def executeWord
    {Q : Type*} [DecidableEq Q]
    (P : Q → Option (Fin 3)) :
    (edges : List (PauliMergeEdge Q)) →
      Σ R : Q → Option (Fin 3), PauliMergeSchedule Q P R
  | [] => ⟨P, .done P⟩
  | ⟨(a, b), hab⟩ :: edges =>
      if hlocal : P a ≠ none ∨ P b ≠ none then
        let P' := updateTwoQubitPauliLabel P a b none (some 2)
        let tail := executeWord P' edges
        ⟨tail.1, .step P a b hab hlocal tail.2⟩
      else
        executeWord P edges

/-- The emitted schedule uses an ordered subword of the given block word. -/
theorem executeWord_edgeList_sublist
    {Q : Type*} [DecidableEq Q]
    (P : Q → Option (Fin 3)) (edges : List (PauliMergeEdge Q)) :
    (executeWord P edges).2.edgeList.Sublist (edges.map PauliMergeEdge.pair) := by
  induction edges generalizing P with
  | nil =>
      simp [executeWord, edgeList]
  | cons e edges ih =>
      rcases e with ⟨⟨a, b⟩, hab⟩
      rw [executeWord.eq_2]
      by_cases hlocal : P a ≠ none ∨ P b ≠ none
      · rw [dif_pos hlocal]
        exact List.Sublist.cons_cons _ (ih _)
      · rw [dif_neg hlocal]
        exact List.Sublist.cons _ (ih P)

end PauliMergeSchedule

end

end GaloisForLFunctions.HTGeometry
