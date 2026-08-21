import GaloisForLFunctions.HTGeometry.HaferkampPauliMergeSchedule

/-!
# Pauli transport along certified qubit paths

This is the path-level induction required by Appendix B of Haferkamp et al.
Each edge receives the exact lifted local `SU(4)` transport, and the resulting
product moves a nonidentity Pauli direction to a `Z` at the path endpoint.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A nontrivial directed qubit path, represented inductively from its source
to its target. -/
inductive QubitMergePath (Q : Type*) : Q → Q → Type _
  | single {a t : Q} : a ≠ t → QubitMergePath Q a t
  | extend {a b t : Q} : a ≠ b → QubitMergePath Q b t → QubitMergePath Q a t

namespace QubitMergePath

/-- Pauli label left after the successive local support merges along a path. -/
def transportLabel
    {Q : Type*} [DecidableEq Q] {a t : Q}
    (path : QubitMergePath Q a t) (P : Q → Option (Fin 3)) :
    Q → Option (Fin 3) :=
  match path with
  | @single _ a t _ => updateTwoQubitPauliLabel P a t none (some 2)
  | @extend _ a b _ _ tail =>
      tail.transportLabel (updateTwoQubitPauliLabel P a b none (some 2))

/-- Every nontrivial merge path leaves a literal `Z` on its endpoint. -/
theorem transportLabel_target_eq_Z
    {Q : Type*} [DecidableEq Q] {a t : Q}
    (path : QubitMergePath Q a t) (P : Q → Option (Fin 3)) :
    path.transportLabel P t = some 2 := by
  induction path generalizing P with
  | @single a t hab =>
      simp [transportLabel, updateTwoQubitPauliLabel]
  | @extend a b t hab tail ih =>
      exact ih _

/-- A certified path canonically induces the corresponding ordered merge
schedule. -/
def toPauliMergeSchedule
    {Q : Type*} [DecidableEq Q] {a t : Q}
    (path : QubitMergePath Q a t) (P : Q → Option (Fin 3))
    (ha : P a ≠ none) :
    PauliMergeSchedule Q P (path.transportLabel P) :=
  match path with
  | @single _ a t hab =>
      PauliMergeSchedule.step P a t hab ha (PauliMergeSchedule.done _)
  | @extend _ a b t hab tail =>
      let P₁ := updateTwoQubitPauliLabel P a b none (some 2)
      have hb : P₁ b ≠ none := by
        simp [P₁, updateTwoQubitPauliLabel]
      PauliMergeSchedule.step P a b hab ha (tail.toPauliMergeSchedule P₁ hb)

/-- A product of lifted local gates transports initial nonidentity support at
the source through the certified path. -/
theorem exists_transport
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {a t : Q} (path : QubitMergePath Q a t)
    (P : Q → Option (Fin 3)) (ha : P a ≠ none) :
    ∃ W : Matrix.unitaryGroup (Q → Bool) ℂ, ∃ c : ℂ, c ≠ 0 ∧
      (W : Matrix (Q → Bool) (Q → Bool) ℂ) * finitePauliMatrix P *
        Matrix.conjTranspose (W : Matrix (Q → Bool) (Q → Bool) ℂ) =
      c • finitePauliMatrix (path.transportLabel P) := by
  induction path generalizing P with
  | @single a t hab =>
      obtain ⟨U, c, hc, hU⟩ :=
        finitePauliMatrix_exists_twoQubitLift_transport P a t hab (Or.inl ha)
      exact ⟨twoQubitLift a t hab U, c, hc, by simp [transportLabel, hU]⟩
  | @extend a b t hab tail ih =>
      obtain ⟨U₁, c₁, hc₁, hU₁⟩ :=
        finitePauliMatrix_exists_twoQubitLift_transport P a b hab (Or.inl ha)
      let P₁ := updateTwoQubitPauliLabel P a b none (some 2)
      have hb : P₁ b ≠ none := by
        simp [P₁, updateTwoQubitPauliLabel]
      obtain ⟨W₂, c₂, hc₂, hW₂⟩ := ih P₁ hb
      refine ⟨W₂ * twoQubitLift a b hab U₁, c₁ * c₂,
        mul_ne_zero hc₁ hc₂, ?_⟩
      rw [unitary_mul_conjugation_smul W₂ (twoQubitLift a b hab U₁) _ _ c₁ hU₁]
      rw [hW₂]
      simp [transportLabel, P₁, smul_smul]

end QubitMergePath

end

end GaloisForLFunctions.HTGeometry
