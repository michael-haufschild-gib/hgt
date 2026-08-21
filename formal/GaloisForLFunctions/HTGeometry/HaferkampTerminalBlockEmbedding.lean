import GaloisForLFunctions.HTGeometry.HaferkampTerminalPauliCoordinate
import GaloisForLFunctions.HTGeometry.HaferkampAmbientProductDerivative

/-!
# Terminal-aware full light-cone blocks

The Appendix-B derivative is taken at the final root-targeting gate selected
by a coalescing light-cone schedule.  This module retains that gate after
embedding the schedule into the physical block: its local Clifford value is
explicit and every later physical gate is the identity.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BackwardsLightCone

/-- A full light-cone block realizes root-only Pauli transport through local
Cliffords while retaining an explicitly selected final root-targeting gate.
All physical locations after that gate carry the identity. -/
theorem exists_full_block_transport_root_Z_with_terminal_gate
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    (cone : BackwardsLightCone n edges root) (hn : 1 < n)
    (P : Fin n → Option (Fin 3)) (hP : ∃ q, P q ≠ none) :
    ∃ blockGates : List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ),
      blockGates.length = edges.length ∧
      (∀ U ∈ blockGates, IsBoolTwoQubitPauliClifford
        (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) ∧
      ∃ terminalGate : Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
      ∃ beforeBlockEdges afterBlockEdges : List (Fin n × Fin n),
      ∃ beforeBlockGates afterBlockGates :
        List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ),
        edges = beforeBlockEdges ++ ((cone.mergePlan.terminal, root) :: afterBlockEdges) ∧
        blockGates = beforeBlockGates ++ (terminalGate :: afterBlockGates) ∧
        beforeBlockGates.length = beforeBlockEdges.length ∧
        afterBlockGates.length = afterBlockEdges.length ∧
        (∀ U ∈ afterBlockGates, U = 1) ∧
        IsBoolTwoQubitPauliClifford
          (terminalGate : Matrix (Bool × Bool) (Bool × Bool) ℂ) ∧
        ∃ c : ℂ, c ≠ 0 ∧
          ((edgeListBlockContraction edges blockGates :
            Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * finitePauliMatrix P *
            Matrix.conjTranspose
              (edgeListBlockContraction edges blockGates :
                Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
            c • finitePauliMatrix (Function.update (fun _ => none) root (some 2))) := by
  let zero : Fin n := ⟨0, lt_trans Nat.zero_lt_one hn⟩
  let one : Fin n := ⟨1, hn⟩
  letI : Nontrivial (Fin n) := ⟨zero, one, by simp [zero, one]⟩
  obtain ⟨before, Pbefore, earlierSchedule, horder, hsub, hbefore, hlocal⟩ :=
    cone.mergePlan.exists_schedule_before_terminal P hP
  obtain ⟨earlierGates, hEarlierLength, hEarlierClifford, cEarlier, hcEarlier,
    hEarlierTransport⟩ := earlierSchedule.exists_localGateWord_transport_clifford
  obtain ⟨terminalGate, cTerminal, hcTerminal, hTerminalClifford,
    hTerminalTransport⟩ :=
    finitePauliMatrix_exists_twoQubitLift_transport_clifford Pbefore
      cone.mergePlan.terminal root cone.mergePlan.terminal_ne_root hlocal
  let selectedEdges := earlierSchedule.edgeList ++ [(cone.mergePlan.terminal, root)]
  let selectedGates := earlierGates ++ [terminalGate]
  have hSelectedLength : selectedGates.length = selectedEdges.length := by
    simp [selectedEdges, selectedGates, hEarlierLength]
  have hSelectedSublist : selectedEdges.Sublist edges := by
    change (earlierSchedule.edgeList ++ [(cone.mergePlan.terminal, root)]).Sublist edges
    have hplan : (earlierSchedule.edgeList ++ [(cone.mergePlan.terminal, root)]).Sublist
        cone.mergePlan.selectedEdges := by
      rw [TemporalRootMergePlan.selectedEdges, horder, List.map_append]
      simp only [List.map_cons, List.map_nil]
      rw [cone.mergePlan.parent_terminal]
      exact List.Sublist.append hsub (by simp)
    exact hplan.trans cone.mergePlan.selectedEdges_sublist
  obtain ⟨blockGates, embedding⟩ :=
    exists_haferkampGateWordEmbedding 1 hSelectedSublist selectedGates hSelectedLength
  have hBlockClifford : ∀ U ∈ blockGates, IsBoolTwoQubitPauliClifford
      (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) :=
    embedding.forall_blockGates one_isBoolTwoQubitPauliClifford (by
      intro U hU
      simp only [selectedGates, List.mem_append, List.mem_singleton] at hU
      rcases hU with hU | rfl
      · exact hEarlierClifford U hU
      · exact hTerminalClifford)
  obtain ⟨beforeBlockEdges, afterBlockEdges, beforeBlockGates, afterBlockGates,
    hBlockEdges, hBlockGates, hBeforeLength, hAfterLength, hSuffixIdentity⟩ :=
    embedding.terminal_gate_suffix
      ⟨earlierSchedule.edgeList, rfl⟩ ⟨earlierGates, rfl⟩
  have hTerminalTotal : totalTwoQubitLift (cone.mergePlan.terminal, root) terminalGate =
      twoQubitLift cone.mergePlan.terminal root cone.mergePlan.terminal_ne_root terminalGate :=
    totalTwoQubitLift_eq_twoQubitLift (cone.mergePlan.terminal, root)
      cone.mergePlan.terminal_ne_root terminalGate
  have hSelectedProduct :
      haferkampGateWordReverseProduct totalTwoQubitLift selectedEdges selectedGates =
        totalTwoQubitLift (cone.mergePlan.terminal, root) terminalGate *
          haferkampGateWordReverseProduct totalTwoQubitLift
            earlierSchedule.edgeList earlierGates := by
    change haferkampGateWordReverseProduct totalTwoQubitLift
        (earlierSchedule.edgeList ++ [(cone.mergePlan.terminal, root)])
        (earlierGates ++ [terminalGate]) = _
    rw [haferkampGateWordReverseProduct_append totalTwoQubitLift
      earlierSchedule.edgeList [(cone.mergePlan.terminal, root)]
      earlierGates [terminalGate] hEarlierLength.symm]
    simp [haferkampGateWordReverseProduct]
  have hTerminalTransportTotal :
      (totalTwoQubitLift (cone.mergePlan.terminal, root) terminalGate :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * finitePauliMatrix Pbefore *
        Matrix.conjTranspose
          (totalTwoQubitLift (cone.mergePlan.terminal, root) terminalGate :
            Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
        cTerminal • finitePauliMatrix
          (updateTwoQubitPauliLabel Pbefore cone.mergePlan.terminal root none (some 2)) := by
    rw [hTerminalTotal]
    exact hTerminalTransport
  have hOutput :
      updateTwoQubitPauliLabel Pbefore cone.mergePlan.terminal root none (some 2) =
        Function.update (fun _ => none) root (some 2) := by
    have hnot : ¬ (Pbefore cone.mergePlan.terminal = none ∧ Pbefore root = none) := by
      simpa only [not_and_or] using hlocal
    have hcomplete : TemporalRootMergePlan.execute cone.mergePlan.parent
        cone.mergePlan.order P =
        updateTwoQubitPauliLabel Pbefore cone.mergePlan.terminal root none (some 2) := by
      rw [horder, TemporalRootMergePlan.execute_append]
      simp only [TemporalRootMergePlan.execute]
      rw [cone.mergePlan.parent_terminal]
      rw [← hbefore]
      rw [TemporalRootMergePlan.mergeLabel, if_neg hnot]
    exact hcomplete.symm.trans (cone.mergePlan.execute_order_eq_root_Z P hP)
  have hSelectedTransport :
      ((haferkampGateWordReverseProduct totalTwoQubitLift selectedEdges selectedGates :
        Matrix.unitaryGroup (Fin n → Bool) ℂ) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * finitePauliMatrix P *
        Matrix.conjTranspose
          ((haferkampGateWordReverseProduct totalTwoQubitLift selectedEdges selectedGates :
            Matrix.unitaryGroup (Fin n → Bool) ℂ) :
            Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
        (cEarlier * cTerminal) •
          finitePauliMatrix (Function.update (fun _ => none) root (some 2)) := by
    rw [hSelectedProduct]
    rw [unitary_mul_conjugation_smul
      (totalTwoQubitLift (cone.mergePlan.terminal, root) terminalGate)
      (haferkampGateWordReverseProduct totalTwoQubitLift
        earlierSchedule.edgeList earlierGates)
      _ _ cEarlier hEarlierTransport]
    rw [hTerminalTransportTotal, hOutput]
    simp [smul_smul]
  refine ⟨blockGates, embedding.blockGates_length_eq, hBlockClifford,
    terminalGate, beforeBlockEdges, afterBlockEdges, beforeBlockGates, afterBlockGates,
    hBlockEdges, hBlockGates, hBeforeLength, hAfterLength, hSuffixIdentity, hTerminalClifford,
    cEarlier * cTerminal, mul_ne_zero hcEarlier hcTerminal, ?_⟩
  change ((haferkampGateWordReverseProduct totalTwoQubitLift edges blockGates :
      Matrix.unitaryGroup (Fin n → Bool) ℂ) :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * finitePauliMatrix P *
      Matrix.conjTranspose
        ((haferkampGateWordReverseProduct totalTwoQubitLift edges blockGates :
          Matrix.unitaryGroup (Fin n → Bool) ℂ) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      (cEarlier * cTerminal) •
        finitePauliMatrix (Function.update (fun _ => none) root (some 2))
  rw [embedding.reverseProduct_eq totalTwoQubitLift_one]
  exact hSelectedTransport

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
