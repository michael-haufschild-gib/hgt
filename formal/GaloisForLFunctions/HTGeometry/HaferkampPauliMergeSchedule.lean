import GaloisForLFunctions.HTGeometry.HaferkampEdgeListArchitecture
import GaloisForLFunctions.HTGeometry.HaferkampLiftedPauliTransport

/-!
# Certified Pauli merge schedules

An Appendix-B block is ultimately a finite ordered word of local merges. This
dependent schedule records the exact label state before each merge, so every
step has the nonidentity witness required to select its closed local `SU(4)`
transport. The theorem below turns that certificate into one full-register
unitary word.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite ordered schedule of exact Pauli support merges. -/
inductive PauliMergeSchedule
    (Q : Type*) [DecidableEq Q] :
    (Q → Option (Fin 3)) → (Q → Option (Fin 3)) → Type _
  | done (P : Q → Option (Fin 3)) : PauliMergeSchedule Q P P
  | step (P : Q → Option (Fin 3)) (a b : Q) (hab : a ≠ b)
      (hlocal : P a ≠ none ∨ P b ≠ none) {R : Q → Option (Fin 3)} :
      PauliMergeSchedule Q (updateTwoQubitPauliLabel P a b none (some 2)) R →
        PauliMergeSchedule Q P R

namespace PauliMergeSchedule

/-- Ordered edge word underlying a certified merge schedule. -/
def edgeList
    {Q : Type*} [DecidableEq Q] {P R : Q → Option (Fin 3)} :
    PauliMergeSchedule Q P R → List (Q × Q)
  | .done _ => []
  | .step _ a b _ _ tail => (a, b) :: tail.edgeList

/-- Every edge in a schedule is a genuine two-qubit location. -/
theorem edgeList_distinct
    {Q : Type*} [DecidableEq Q] {P R : Q → Option (Fin 3)}
    (schedule : PauliMergeSchedule Q P R) :
    ∀ e ∈ schedule.edgeList, e.1 ≠ e.2 := by
  induction schedule with
  | done P => simp [edgeList]
  | @step P a b hab hlocal R tail ih =>
      intro e he
      simp only [edgeList, List.mem_cons] at he
      rcases he with rfl | he
      · exact hab
      · exact ih e he

/-- Concatenate two certified schedules whose endpoint and starting label
match.  The physical order of their merge steps is preserved. -/
def append
    {Q : Type*} [DecidableEq Q] {P R S : Q → Option (Fin 3)} :
    PauliMergeSchedule Q P R → PauliMergeSchedule Q R S →
      PauliMergeSchedule Q P S
  | .done _, right => right
  | .step P a b hab hlocal tail, right =>
      .step P a b hab hlocal (tail.append right)

/-- The edge word of a concatenated schedule is the concatenation of its
two edge words. -/
theorem edgeList_append
    {Q : Type*} [DecidableEq Q] {P R S : Q → Option (Fin 3)}
    (left : PauliMergeSchedule Q P R) (right : PauliMergeSchedule Q R S) :
    (left.append right).edgeList = left.edgeList ++ right.edgeList := by
  induction left with
  | done P => rfl
  | step P a b hab hlocal tail ih =>
      simp [append, edgeList, ih]

/-- The literal ordered architecture implementing the schedule's edge word. -/
def architecture
    {n : ℕ} {P R : Fin n → Option (Fin 3)}
    (schedule : PauliMergeSchedule (Fin n) P R) :
    TwoQubitArchitecture n schedule.edgeList.length :=
  TwoQubitArchitecture.ofEdgeList schedule.edgeList schedule.edgeList_distinct

/-- Every certified schedule is implemented by a product of lifted local
`SU(4)` gates, up to an explicit nonzero scalar on its Pauli direction. -/
theorem exists_transport
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {P R : Q → Option (Fin 3)}
    (schedule : PauliMergeSchedule Q P R) :
    ∃ W : Matrix.unitaryGroup (Q → Bool) ℂ, ∃ c : ℂ, c ≠ 0 ∧
      (W : Matrix (Q → Bool) (Q → Bool) ℂ) * finitePauliMatrix P *
        Matrix.conjTranspose (W : Matrix (Q → Bool) (Q → Bool) ℂ) =
      c • finitePauliMatrix R := by
  induction schedule with
  | done P =>
      exact ⟨1, 1, one_ne_zero, by simp⟩
  | @step P a b hab hlocal R tail ih =>
      obtain ⟨U₁, c₁, hc₁, hU₁⟩ :=
        finitePauliMatrix_exists_twoQubitLift_transport P a b hab hlocal
      obtain ⟨W₂, c₂, hc₂, hW₂⟩ := ih
      refine ⟨W₂ * twoQubitLift a b hab U₁, c₁ * c₂,
        mul_ne_zero hc₁ hc₂, ?_⟩
      rw [unitary_mul_conjugation_smul W₂ (twoQubitLift a b hab U₁) _ _ c₁ hU₁]
      rw [hW₂]
      simp [smul_smul]

/-- A schedule whose terminal label is `Z` at `root` implements the exact
root-targeted Pauli transport required of one backwards-light-cone block. -/
theorem exists_transport_to_root
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {P R : Q → Option (Fin 3)} (root : Q)
    (schedule : PauliMergeSchedule Q P R) (hroot : R root = some 2) :
    ∃ W : Matrix.unitaryGroup (Q → Bool) ℂ, ∃ c : ℂ, c ≠ 0 ∧
      (W : Matrix (Q → Bool) (Q → Bool) ℂ) * finitePauliMatrix P *
        Matrix.conjTranspose (W : Matrix (Q → Bool) (Q → Bool) ℂ) =
      c • finitePauliMatrix R ∧ R root = some 2 := by
  obtain ⟨W, c, hc, hW⟩ := schedule.exists_transport
  exact ⟨W, c, hc, hW, hroot⟩

end PauliMergeSchedule

end

end GaloisForLFunctions.HTGeometry
