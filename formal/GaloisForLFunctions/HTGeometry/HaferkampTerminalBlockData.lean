import GaloisForLFunctions.HTGeometry.HaferkampTerminalPhaseBlockDerivative

/-!
# Bundled terminal-aware light-cone blocks

The block-rank recursion must retain one compatible witness: its local
Clifford word, terminal `SU(4)` curve, Pauli transport, and derivative
identity.  This record packages precisely that closed witness.
-/

open scoped BigOperators ComplexConjugate Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BackwardsLightCone

/-- A physical light-cone block together with its selected terminal `SU(4)`
curve and all identities needed by the Appendix-B prefix induction. -/
structure TerminalBlockData
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    (cone : BackwardsLightCone n edges root) (P : Fin n → Option (Fin 3)) where
  gates : List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
  terminalGate : Matrix.specialUnitaryGroup (Bool × Bool) ℂ
  prefixEdges : List (Fin n × Fin n)
  suffixEdges : List (Fin n × Fin n)
  prefixGates : List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
  suffixGates : List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
  gates_length : gates.length = edges.length
  gates_clifford : ∀ U ∈ gates, IsBoolTwoQubitPauliClifford
    (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)
  edges_decomp : edges = prefixEdges ++ ((cone.mergePlan.terminal, root) :: suffixEdges)
  gates_decomp : gates = prefixGates ++ (terminalGate :: suffixGates)
  prefix_length : prefixGates.length = prefixEdges.length
  suffix_length : suffixGates.length = suffixEdges.length
  suffix_identity : ∀ U ∈ suffixGates, U = 1
  transportCoeff : ℂ
  transportCoeff_ne_zero : transportCoeff ≠ 0
  transport :
    ((edgeListBlockContraction edges gates :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * finitePauliMatrix P *
      Matrix.conjTranspose
        (edgeListBlockContraction edges gates :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      transportCoeff •
        finitePauliMatrix (Function.update (fun _ => none) root (some 2)))
  curve_length : ∀ t : ℝ,
    (prefixGates ++ terminalPauliGatePath terminalGate t :: suffixGates).length =
      edges.length
  curve_zero : prefixGates ++ terminalPauliGatePath terminalGate 0 :: suffixGates = gates
  contraction_derivative :
    EntrywiseMatrixHasDerivAt
      (fun t => (List.zipWith (fun edge gate =>
        (totalTwoQubitLift edge gate : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
        edges
        (prefixGates ++ terminalPauliGatePath terminalGate t :: suffixGates)).reverse.prod)
      (Complex.I • (finitePauliMatrix
        (Function.update (fun _ => none) root (some 2)) *
        (List.zipWith (fun edge gate =>
          (totalTwoQubitLift edge gate : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
          edges gates).reverse.prod)) 0

/-- Every nonidentity Pauli label has a bundled terminal-aware physical BLC
block. -/
theorem exists_terminalBlockData
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    (cone : BackwardsLightCone n edges root) (hn : 1 < n)
    (P : Fin n → Option (Fin 3)) (hP : ∃ q, P q ≠ none) :
    Nonempty (TerminalBlockData cone P) := by
  obtain ⟨gates, terminalGate, beforeEdges, afterEdges, beforeGates, afterGates,
    hgatesLength, hgatesClifford, hedges, hgates, hbeforeLength, hafterLength,
    hafterIdentity, c, hc, htransport, hcurveLength, hcurveZero, hderivative⟩ :=
    cone.exists_terminal_block_real_derivative_coordinate hn P hP
  exact ⟨⟨gates, terminalGate, beforeEdges, afterEdges, beforeGates, afterGates,
    hgatesLength, hgatesClifford, hedges, hgates, hbeforeLength, hafterLength,
    hafterIdentity, c, hc, htransport, hcurveLength, hcurveZero, hderivative⟩⟩

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
