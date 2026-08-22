import GaloisForLFunctions.HTGeometry.HaferkampFlattenedCoordinateDerivative
import GaloisForLFunctions.HTGeometry.HaferkampBlockRankInduction

/-!
# Real terminal phase curves in flattened BLC words

Each retained flattened terminal coordinate receives its literal determinant-one
local phase curve.  The resulting full-word contraction has the exact
entrywise derivative required by the rank proof.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BackwardsLightCone

/-- The flattened full-register contraction obtained by varying one retained
terminal `SU(4)` gate along its exact real phase path. -/
def TerminalBlockPrefixAssembly.terminalCoordinateCurve
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (i : Fin labels.length) (t : ℝ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  (List.map (fun U : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
      (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
      (assembly.liftedWord.take (assembly.terminalIndices i).1) ++
    (totalTwoQubitLift (cone.mergePlan.terminal, root)
      (terminalPauliGatePath (assembly.terminalLocalGate i) t) :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ::
    List.map (fun U : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
      (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
      (assembly.liftedWord.drop ((assembly.terminalIndices i).1 + 1))).reverse.prod

/-- At zero, a terminal-coordinate curve is the original flattened
contraction. -/
theorem TerminalBlockPrefixAssembly.terminalCoordinateCurve_zero
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (i : Fin labels.length) :
    assembly.terminalCoordinateCurve i 0 = assembly.liftedWord.reverse.prod := by
  unfold terminalCoordinateCurve
  rw [terminalPauliGatePath_zero]
  have hgate :
      (totalTwoQubitLift (cone.mergePlan.terminal, root) (assembly.terminalLocalGate i) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      (assembly.liftedWord.get (assembly.terminalIndices i) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
    exact congrArg (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
      (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
      (assembly.liftedWord_get_terminalLocalGate i).symm
  rw [hgate]
  have hsplit : assembly.liftedWord =
      assembly.liftedWord.take (assembly.terminalIndices i).1 ++
        assembly.liftedWord.get (assembly.terminalIndices i) ::
          assembly.liftedWord.drop ((assembly.terminalIndices i).1 + 1) := by
    calc
      assembly.liftedWord = assembly.liftedWord.take (assembly.terminalIndices i).1 ++
          assembly.liftedWord.drop (assembly.terminalIndices i).1 :=
        (List.take_append_drop (assembly.terminalIndices i).1 assembly.liftedWord).symm
      _ = assembly.liftedWord.take (assembly.terminalIndices i).1 ++
          assembly.liftedWord.get (assembly.terminalIndices i) ::
            assembly.liftedWord.drop ((assembly.terminalIndices i).1 + 1) := by
        rw [← List.getElem_cons_drop (as := assembly.liftedWord)
          (i := (assembly.terminalIndices i).1) (assembly.terminalIndices i).2]
        simp only [List.get_eq_getElem]
  calc
    (List.map (fun U : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
        (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
        (assembly.liftedWord.take (assembly.terminalIndices i).1) ++
      (assembly.liftedWord.get (assembly.terminalIndices i) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ::
      List.map (fun U : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
        (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
        (assembly.liftedWord.drop ((assembly.terminalIndices i).1 + 1))).reverse.prod =
        (List.map (fun U : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
            (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
          assembly.liftedWord).reverse.prod := by
      simpa only [List.map_append, List.map_cons] using
        congrArg (fun word : List (Matrix.unitaryGroup (Fin n → Bool) ℂ) =>
          (List.map (fun U : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
            (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) word).reverse.prod)
          hsplit.symm
    _ = assembly.liftedWord.reverse.prod :=
      List.map_coe_unitary_reverse_prod assembly.liftedWord

/-- The terminal-coordinate curve has derivative `i` times the corresponding
ambient selected-coordinate variation of the flattened word. -/
theorem TerminalBlockPrefixAssembly.entrywiseHasDerivAt_terminalCoordinateCurve
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (i : Fin labels.length) :
    EntrywiseMatrixHasDerivAt (assembly.terminalCoordinateCurve i)
      (Complex.I • haferkampUnitaryListCoordinateOutput assembly.liftedWord
        (assembly.terminalIndices i)
        (finitePauliMatrix (Function.update (fun _ => none) root (some 2)))) 0 := by
  let word := assembly.liftedWord
  let index := assembly.terminalIndices i
  let before := List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
      (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
    (word.take index.1)
  let after := List.map (fun V : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
      (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
    (word.drop (index.1 + 1))
  let U := assembly.terminalLocalGate i
  have hterminal := entrywiseHasDerivAt_totalTwoQubitLift_terminalPauliGatePath
    (cone := cone) U
  have hgate : word.get index =
      totalTwoQubitLift (cone.mergePlan.terminal, root) U := by
    dsimp [word, index, U]
    exact assembly.liftedWord_get_terminalLocalGate i
  have hbefore : before.reverse.prod =
      ((word.take index.1).reverse.prod : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
    dsimp [before]
    exact List.map_coe_unitary_reverse_prod (word.take index.1)
  have hafter : after.reverse.prod =
      ((word.drop (index.1 + 1)).reverse.prod :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
    dsimp [after]
    exact List.map_coe_unitary_reverse_prod (word.drop (index.1 + 1))
  have houtput : after.reverse.prod *
      (Complex.I • (finitePauliMatrix
        (Function.update (fun _ => none) root (some 2)) *
        (totalTwoQubitLift (cone.mergePlan.terminal, root) U :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ))) * before.reverse.prod =
      Complex.I • haferkampUnitaryListCoordinateOutput word index
        (finitePauliMatrix (Function.update (fun _ => none) root (some 2))) := by
    unfold haferkampUnitaryListCoordinateOutput
    rw [hafter, hbefore, hgate, Matrix.mul_smul, smul_mul_assoc]
  change EntrywiseMatrixHasDerivAt
    (fun t => (before ++
      (totalTwoQubitLift (cone.mergePlan.terminal, root)
        (terminalPauliGatePath U t) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ::
      after).reverse.prod) _ 0
  have hderiv := entrywiseHasDerivAt_reverseProd_replace before after hterminal
  rw [houtput] at hderiv
  simpa [word, index] using hderiv

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
