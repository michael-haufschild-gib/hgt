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
      (ha : P a ≠ none) {R : Q → Option (Fin 3)} :
      PauliMergeSchedule Q (updateTwoQubitPauliLabel P a b none (some 2)) R →
        PauliMergeSchedule Q P R

namespace PauliMergeSchedule

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
  | @step P a b hab ha R tail ih =>
      obtain ⟨U₁, c₁, hc₁, hU₁⟩ :=
        finitePauliMatrix_exists_twoQubitLift_transport P a b hab (Or.inl ha)
      obtain ⟨W₂, c₂, hc₂, hW₂⟩ := ih
      refine ⟨W₂ * twoQubitLift a b hab U₁, c₁ * c₂,
        mul_ne_zero hc₁ hc₂, ?_⟩
      rw [unitary_mul_conjugation_smul W₂ (twoQubitLift a b hab U₁) _ _ c₁ hU₁]
      rw [hW₂]
      simp [smul_smul]

end PauliMergeSchedule

end

end GaloisForLFunctions.HTGeometry
