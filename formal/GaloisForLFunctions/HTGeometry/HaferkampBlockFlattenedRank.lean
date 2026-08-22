import GaloisForLFunctions.HTGeometry.HaferkampBlockFlattening
import GaloisForLFunctions.HTGeometry.HaferkampBlockRankInduction

/-!
# Rank of flattened terminal-aware BLC coordinates

The recursive BLC assembly supplies one physically valid terminal coordinate
per requested Pauli direction.  This file feeds its exact stripped-coordinate
identity into the generic finite-word rank argument.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BackwardsLightCone

/-- The retained terminal coordinates of a flattened terminal-aware BLC
assembly give linearly independent ambient coordinate outputs whenever their
requested Pauli labels are linearly independent. -/
theorem TerminalBlockPrefixAssembly.linearIndependent_terminalCoordinateOutputs
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℂ (fun i : Fin labels.length =>
      finitePauliMatrix (labels.get i))) :
    LinearIndependent ℂ (fun i =>
      haferkampUnitaryListCoordinateOutput assembly.liftedWord
        (assembly.terminalIndices i)
        (finitePauliMatrix (Function.update (fun _ => none) root (some 2)))) := by
  apply linearIndependent_haferkampSelectedUnitaryListCoordinateOutputs
    assembly.liftedWord assembly.terminalIndices
    (fun i => labels.get i) hlabels
    (fun _ => finitePauliMatrix (Function.update (fun _ => none) root (some 2)))
    (fun i => assembly.terminalCoefficient i)
    (fun i => assembly.terminalCoefficient_apply_ne_zero i)
  intro i
  simpa only [TerminalBlockPrefixAssembly.terminalPrefix, mul_one] using
    assembly.terminalCoordinate_stripped i

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
