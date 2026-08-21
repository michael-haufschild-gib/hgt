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

/-- Equation (B6) at a concrete final root-targeting gate: the ambient
ordered-product derivative in the local `I ⊗ Z` coordinate is root-Pauli
left multiplication of the full block word. -/
theorem exists_terminal_ambient_derivative_coordinate
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    (cone : BackwardsLightCone n edges root) (hn : 1 < n)
    (P : Fin n → Option (Fin 3)) (hP : ∃ q, P q ≠ none) :
    ∃ blockGates : List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ),
      ∃ terminalGate : Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
      ∃ matrices : List (Matrix (Fin n → Bool) (Fin n → Bool) ℂ),
      ∃ i : Fin matrices.length, ∃ H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ,
        blockGates.length = edges.length ∧
        matrices = List.zipWith (fun edge gate =>
          (totalTwoQubitLift edge gate : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
          edges blockGates ∧
        H = twoQubitLiftMatrix cone.mergePlan.terminal root
          cone.mergePlan.terminal_ne_root
          (boolTwoQubitPauli none (some 2) *
            (terminalGate : Matrix (Bool × Bool) (Bool × Bool) ℂ)) ∧
        ambientOrderedMatrixProductDerivative matrices.length (fun j => matrices.get j)
          (ambientCoordinateDirection i H) =
          finitePauliMatrix (Function.update (fun _ => none) root (some 2)) *
            matrices.reverse.prod := by
  obtain ⟨blockGates, hBlockLength, hBlockClifford, terminalGate,
    beforeBlockEdges, afterBlockEdges, beforeBlockGates, afterBlockGates,
    hBlockEdges, hBlockGates, hBeforeLength, hAfterLength, hSuffixIdentity,
    hTerminalClifford, c, hc, hTransport⟩ :=
    cone.exists_full_block_transport_root_Z_with_terminal_gate hn P hP
  let matrices := List.zipWith (fun edge gate =>
    (totalTwoQubitLift edge gate : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
    edges blockGates
  let beforeMatrices := List.zipWith (fun edge gate =>
    (totalTwoQubitLift edge gate : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
    beforeBlockEdges beforeBlockGates
  let afterMatrices := List.zipWith (fun edge gate =>
    (totalTwoQubitLift edge gate : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
    afterBlockEdges afterBlockGates
  have hmatrices : matrices = beforeMatrices ++
      (totalTwoQubitLift (cone.mergePlan.terminal, root) terminalGate :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :: afterMatrices := by
    change List.zipWith (fun edge gate =>
      (totalTwoQubitLift edge gate : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
      edges blockGates = _
    conv_lhs => rw [hBlockEdges]
    rw [hBlockGates, List.zipWith_append hBeforeLength.symm]
    rfl
  have hzipSuffix : ∀ (suffixEdges : List (Fin n × Fin n))
      (suffixGates : List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ)),
      suffixGates.length = suffixEdges.length →
      (∀ U ∈ suffixGates, U = 1) →
      ∀ M ∈ List.zipWith (fun edge gate =>
        (totalTwoQubitLift edge gate : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
        suffixEdges suffixGates, M = 1 := by
    intro suffixEdges
    induction suffixEdges with
    | nil =>
        intro suffixGates hlength hidentity
        have hnil : suffixGates = [] := by
          apply List.eq_nil_of_length_eq_zero
          simpa using hlength
        subst suffixGates
        simp
    | cons edge suffixEdges ih =>
        intro suffixGates hlength hidentity
        cases suffixGates with
        | nil => simp at hlength
        | cons gate suffixGates =>
            simp only [List.length_cons, Nat.succ.injEq] at hlength
            intro M hM
            change M ∈
              (totalTwoQubitLift edge gate : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ::
                List.zipWith (fun edge gate =>
                  (totalTwoQubitLift edge gate : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
                  suffixEdges suffixGates at hM
            simp only [List.mem_cons] at hM
            rcases hM with rfl | hM
            · rw [hidentity gate (by simp)]
              exact congrArg (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
                (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
                (totalTwoQubitLift_one edge)
            · exact ih suffixGates hlength
                (fun U hU => hidentity U (by simp only [List.mem_cons]; exact Or.inr hU)) M hM
  have hafterMatrices : ∀ M ∈ afterMatrices, M = 1 := by
    exact hzipSuffix afterBlockEdges afterBlockGates hAfterLength hSuffixIdentity
  let H := twoQubitLiftMatrix cone.mergePlan.terminal root
    cone.mergePlan.terminal_ne_root
    (boolTwoQubitPauli none (some 2) *
      (terminalGate : Matrix (Bool × Bool) (Bool × Bool) ℂ))
  have hH : H = finitePauliMatrix
      (Function.update (fun _ => none) root (some 2)) *
      (totalTwoQubitLift (cone.mergePlan.terminal, root) terminalGate :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
    dsimp [H]
    rw [twoQubitLiftMatrix_terminal_coordinate]
    rw [← totalTwoQubitLift_eq_twoQubitLift
      (cone.mergePlan.terminal, root) cone.mergePlan.terminal_ne_root terminalGate]
    congr 2
    funext q
    by_cases hq : q = root
    · subst q
      simp [updateTwoQubitPauliLabel]
    · simp [updateTwoQubitPauliLabel, hq]
  let i : Fin matrices.length := ⟨beforeMatrices.length, by
    rw [hmatrices]
    simp [beforeMatrices, List.length_zipWith, hBeforeLength]⟩
  have hafterReverse : ∀ M ∈ afterMatrices.reverse, M = 1 := by
    intro M hM
    exact hafterMatrices M (by simpa using hM)
  have hmatricesProduct : matrices.reverse.prod =
      (totalTwoQubitLift (cone.mergePlan.terminal, root) terminalGate :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * beforeMatrices.reverse.prod := by
    rw [hmatrices, List.reverse_append, List.prod_append]
    rw [List.reverse_cons, List.prod_append, List.prod_eq_one hafterReverse]
    simp
  refine ⟨blockGates, terminalGate, matrices, i, H,
    hBlockLength, rfl, rfl, ?_⟩
  have hderivative :=
    ambientOrderedMatrixProductDerivative_list_coordinate_of_suffix_one
      matrices beforeMatrices afterMatrices
      (totalTwoQubitLift (cone.mergePlan.terminal, root) terminalGate :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
      hmatrices hafterMatrices H
  change ambientOrderedMatrixProductDerivative matrices.length (fun j => matrices.get j)
      (ambientCoordinateDirection i H) = _
  rw [show i = ⟨beforeMatrices.length, by
    rw [hmatrices]
    simp [beforeMatrices, List.length_zipWith, hBeforeLength]⟩ by rfl]
  rw [hderivative, hH, Matrix.mul_assoc, hmatricesProduct]

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
