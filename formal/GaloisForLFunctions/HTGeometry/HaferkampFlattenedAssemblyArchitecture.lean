import GaloisForLFunctions.HTGeometry.HaferkampTerminalHybridEuclideanArchitectureAnalytic
import GaloisForLFunctions.HTGeometry.HaferkampFlattenedTerminalPhaseGenericity
import GaloisForLFunctions.HTGeometry.HaferkampEdgeListGateCompilation

/-!
# Native finite architecture of a flattened BLC assembly

The recursive Appendix-B block assembly is compiled to one ordered finite
two-qubit architecture.  Its local parameter family and contraction agree
exactly with the established flattened lifted word.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BackwardsLightCone

/-- Chronological edge word underlying a recursive terminal-aware BLC
assembly. -/
def TerminalBlockPrefixAssembly.flattenedEdgeWord
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))} :
    TerminalBlockPrefixAssembly cone pre labels → List (Fin n × Fin n)
  | .nil _ => []
  | .cons _ tail => edges ++ tail.flattenedEdgeWord

/-- Flattening preserves the common edge/gate word length. -/
theorem TerminalBlockPrefixAssembly.flattenedEdgeWord_length_eq_gateWord_length
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    assembly.flattenedEdgeWord.length = assembly.gateWord.length := by
  induction assembly with
  | nil => rfl
  | cons step tail ih =>
      simp [flattenedEdgeWord, gateWord, step.block.gates_length, ih]

/-- Every edge in the flattened assembly is a genuine two-qubit location. -/
theorem TerminalBlockPrefixAssembly.flattenedEdgeWord_distinct
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    ∀ edge ∈ assembly.flattenedEdgeWord, edge.1 ≠ edge.2 := by
  induction assembly with
  | nil => simp [flattenedEdgeWord]
  | cons step tail ih =>
      intro edge hedge
      simp only [flattenedEdgeWord, List.mem_append] at hedge
      rcases hedge with hedge | hedge
      · exact cone.edge_distinct edge hedge
      · exact ih edge hedge

/-- The existing flattened lifted word is the pointwise lift of the flattened
edge and local-gate words. -/
theorem TerminalBlockPrefixAssembly.liftedWord_eq_zipWith_flattenedEdgeWord_gateWord
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    assembly.liftedWord =
      List.zipWith totalTwoQubitLift assembly.flattenedEdgeWord assembly.gateWord := by
  induction assembly with
  | nil => rfl
  | cons step tail ih =>
      simp only [TerminalBlockPrefixAssembly.liftedWord,
        TerminalBlockPrefixAssembly.flattenedEdgeWord,
        TerminalBlockPrefixAssembly.gateWord]
      rw [List.zipWith_append step.block.gates_length.symm]
      rw [ih]

/-- Native finite two-qubit architecture of the full flattened assembly. -/
def TerminalBlockPrefixAssembly.flattenedArchitecture
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    TwoQubitArchitecture n assembly.flattenedEdgeWord.length :=
  TwoQubitArchitecture.ofEdgeList assembly.flattenedEdgeWord
    assembly.flattenedEdgeWord_distinct

/-- Native gate parameters of the full flattened assembly. -/
def TerminalBlockPrefixAssembly.flattenedGateParameters
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    Fin assembly.flattenedEdgeWord.length →
      Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
  edgeListGatesAsFn assembly.gateWord assembly.flattenedEdgeWord.length
    assembly.flattenedEdgeWord_length_eq_gateWord_length.symm

/-- The native architecture contraction is exactly the flattened BLC
contraction already used by the terminal-phase rank witness. -/
theorem TerminalBlockPrefixAssembly.flattenedArchitecture_contraction_eq
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    (assembly.flattenedArchitecture.contraction assembly.flattenedGateParameters :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      (assembly.liftedWord.reverse.prod :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  unfold flattenedArchitecture flattenedGateParameters
  rw [← edgeListBlockContraction_eq_ofEdgeList_contraction
    assembly.flattenedEdgeWord assembly.flattenedEdgeWord_distinct assembly.gateWord
    assembly.flattenedEdgeWord_length_eq_gateWord_length.symm]
  unfold edgeListBlockContraction haferkampGateWordReverseProduct
  rw [← assembly.liftedWord_eq_zipWith_flattenedEdgeWord_gateWord]

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
