import GaloisForLFunctions.HTGeometry.HaferkampEntrywiseLiftDerivative
import GaloisForLFunctions.HTGeometry.HaferkampTerminalBlockEmbedding

/-!
# A genuine terminal `SU(4)` chart for the full light-cone block

This connects Appendix B's terminal-coordinate algebra to an actual real
one-parameter path of local `SU(4)` gates.  The finite product is
differentiated entrywise, keeping the physical identity suffix explicit.
-/

open scoped BigOperators ComplexConjugate Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BackwardsLightCone

/-- The physical full block has a real local `SU(4)` curve through its
terminal gate whose entrywise contraction derivative is `i` times the
root-`Z` Pauli direction.  This is the analytic form of Appendix B equation
(B6) for the selected terminal root-targeting location. -/
theorem exists_terminal_block_real_derivative_coordinate
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    (cone : BackwardsLightCone n edges root) (hn : 1 < n)
    (P : Fin n → Option (Fin 3)) (hP : ∃ q, P q ≠ none) :
    ∃ blockGates : List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ),
      ∃ terminalGate : Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
      ∃ beforeBlockEdges afterBlockEdges : List (Fin n × Fin n),
      ∃ beforeBlockGates afterBlockGates :
        List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ),
        blockGates.length = edges.length ∧
        (∀ U ∈ blockGates, IsBoolTwoQubitPauliClifford
          (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) ∧
        edges = beforeBlockEdges ++ ((cone.mergePlan.terminal, root) :: afterBlockEdges) ∧
        blockGates = beforeBlockGates ++ (terminalGate :: afterBlockGates) ∧
        beforeBlockGates.length = beforeBlockEdges.length ∧
        afterBlockGates.length = afterBlockEdges.length ∧
        (∀ U ∈ afterBlockGates, U = 1) ∧
        ∃ c : ℂ, c ≠ 0 ∧
          ((edgeListBlockContraction edges blockGates :
            Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * finitePauliMatrix P *
            Matrix.conjTranspose
              (edgeListBlockContraction edges blockGates :
                Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
            c • finitePauliMatrix (Function.update (fun _ => none) root (some 2))) ∧
        (∀ t : ℝ,
          (beforeBlockGates ++ terminalPauliGatePath terminalGate t :: afterBlockGates).length =
            edges.length) ∧
        beforeBlockGates ++ terminalPauliGatePath terminalGate 0 :: afterBlockGates =
          blockGates ∧
        EntrywiseMatrixHasDerivAt
          (fun t => (List.zipWith (fun edge gate =>
            (totalTwoQubitLift edge gate : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
            edges
            (beforeBlockGates ++ terminalPauliGatePath terminalGate t :: afterBlockGates)).reverse.prod)
          (Complex.I • (finitePauliMatrix
            (Function.update (fun _ => none) root (some 2)) *
            (List.zipWith (fun edge gate =>
              (totalTwoQubitLift edge gate : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
              edges blockGates).reverse.prod)) 0 := by
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
  have hmatricesProduct : matrices.reverse.prod =
      (totalTwoQubitLift (cone.mergePlan.terminal, root) terminalGate :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * beforeMatrices.reverse.prod := by
    have hafterReverse : ∀ M ∈ afterMatrices.reverse, M = 1 := by
      intro M hM
      exact hafterMatrices M (by simpa using hM)
    rw [hmatrices, List.reverse_append, List.prod_append]
    rw [List.reverse_cons, List.prod_append, List.prod_eq_one hafterReverse]
    simp
  have hterminal : EntrywiseMatrixHasDerivAt (fun t : ℝ =>
      (totalTwoQubitLift (cone.mergePlan.terminal, root)
        (terminalPauliGatePath terminalGate t) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
      (Complex.I • H) 0 := by
    have htotal (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
        (totalTwoQubitLift (cone.mergePlan.terminal, root) U :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
        (twoQubitLift cone.mergePlan.terminal root cone.mergePlan.terminal_ne_root U :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
      exact congrArg (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
        (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
        (totalTwoQubitLift_eq_twoQubitLift
          (cone.mergePlan.terminal, root) cone.mergePlan.terminal_ne_root U)
    rw [show (fun t : ℝ =>
      (totalTwoQubitLift (cone.mergePlan.terminal, root)
        (terminalPauliGatePath terminalGate t) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) =
      (fun t : ℝ =>
        (twoQubitLift cone.mergePlan.terminal root cone.mergePlan.terminal_ne_root
          (terminalPauliGatePath terminalGate t) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) by
        funext t; exact htotal (terminalPauliGatePath terminalGate t)]
    exact entrywiseHasDerivAt_twoQubitLift_terminalPauliGatePath
      cone.mergePlan.terminal root cone.mergePlan.terminal_ne_root terminalGate
  have hcurveMatrices : ∀ t : ℝ,
      List.zipWith (fun edge gate =>
        (totalTwoQubitLift edge gate : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
        edges (beforeBlockGates ++ terminalPauliGatePath terminalGate t :: afterBlockGates) =
        beforeMatrices ++
          (totalTwoQubitLift (cone.mergePlan.terminal, root)
            (terminalPauliGatePath terminalGate t) :
            Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :: afterMatrices := by
    intro t
    conv_lhs => rw [hBlockEdges]
    rw [List.zipWith_append hBeforeLength.symm]
    rfl
  refine ⟨blockGates, terminalGate, beforeBlockEdges, afterBlockEdges,
    beforeBlockGates, afterBlockGates, hBlockLength, hBlockClifford, hBlockEdges,
    hBlockGates, hBeforeLength, hAfterLength, hSuffixIdentity, c, hc, hTransport, ?_, ?_, ?_⟩
  · intro t
    simp [hBlockEdges, hBeforeLength, hAfterLength]
  · simp [hBlockGates]
  · rw [show (fun t =>
      (List.zipWith (fun edge gate =>
        (totalTwoQubitLift edge gate : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
        edges (beforeBlockGates ++ terminalPauliGatePath terminalGate t :: afterBlockGates)).reverse.prod) =
      (fun t => (beforeMatrices ++
        (totalTwoQubitLift (cone.mergePlan.terminal, root)
          (terminalPauliGatePath terminalGate t) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :: afterMatrices).reverse.prod) by
        funext t; rw [hcurveMatrices]]
    rw [show (Complex.I • (finitePauliMatrix
        (Function.update (fun _ => none) root (some 2)) * matrices.reverse.prod)) =
      (Complex.I • H) * beforeMatrices.reverse.prod by
        rw [hmatricesProduct, hH, smul_mul_assoc, Matrix.mul_assoc]]
    exact entrywiseHasDerivAt_reverseProd_replace_of_suffix_one
      beforeMatrices afterMatrices hterminal hafterMatrices

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
