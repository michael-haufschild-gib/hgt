import GaloisForLFunctions.HTGeometry.HaferkampPauliMergeSchedule
import GaloisForLFunctions.HTGeometry.HaferkampSublistGateEmbedding
import GaloisForLFunctions.HTGeometry.HaferkampTotalTwoQubitLift

/-!
# Local gate-word realization of a Pauli merge schedule

Every certified support merge can be realized by one explicit local `SU(4)`
gate. This module retains that full local gate list instead of only its final
register unitary, allowing a schedule to be embedded in its original block.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace PauliMergeSchedule

/-- A certified merge schedule has an aligned local `SU(4)` gate word whose
reverse-chronological register product performs its exact Pauli transport. -/
theorem exists_localGateWord_transport
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {P R : Q → Option (Fin 3)}
    (schedule : PauliMergeSchedule Q P R) :
    ∃ localGates : List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ),
      localGates.length = schedule.edgeList.length ∧
      ∃ c : ℂ, c ≠ 0 ∧
        ((haferkampGateWordReverseProduct (fun (edge : Q × Q) U =>
          totalTwoQubitLift edge U) schedule.edgeList localGates :
          Matrix.unitaryGroup (Q → Bool) ℂ) :
          Matrix (Q → Bool) (Q → Bool) ℂ) *
            finitePauliMatrix P *
            Matrix.conjTranspose
              ((haferkampGateWordReverseProduct (fun (edge : Q × Q) U =>
                totalTwoQubitLift edge U) schedule.edgeList localGates :
                Matrix.unitaryGroup (Q → Bool) ℂ) :
                Matrix (Q → Bool) (Q → Bool) ℂ) =
          c • finitePauliMatrix R := by
  induction schedule with
  | done P =>
      refine ⟨[], rfl, 1, one_ne_zero, ?_⟩
      simp [haferkampGateWordReverseProduct]
  | @step P a b hab hlocal R tail ih =>
      obtain ⟨U₁, c₁, hc₁, hU₁⟩ :=
        finitePauliMatrix_exists_twoQubitLift_transport P a b hab hlocal
      obtain ⟨gates, hgates, c₂, hc₂, htail⟩ := ih
      refine ⟨U₁ :: gates, by simp [edgeList, hgates], c₁ * c₂,
        mul_ne_zero hc₁ hc₂, ?_⟩
      have htotal : totalTwoQubitLift (a, b) U₁ = twoQubitLift a b hab U₁ :=
        totalTwoQubitLift_eq_twoQubitLift (a, b) hab U₁
      simp only [edgeList]
      rw [haferkampGateWordReverseProduct_cons]
      rw [htotal]
      rw [unitary_mul_conjugation_smul
        (haferkampGateWordReverseProduct (fun (edge : Q × Q) U =>
          totalTwoQubitLift edge U) tail.edgeList gates)
        (twoQubitLift a b hab U₁) _ _ c₁ hU₁]
      rw [htail]
      simp [smul_smul]

end PauliMergeSchedule

end

end GaloisForLFunctions.HTGeometry
