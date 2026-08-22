import GaloisForLFunctions.HTGeometry.HaferkampCliffordSign
import GaloisForLFunctions.HTGeometry.HaferkampBlockPrefixAssembly

/-!
# Sign control for terminal BLC coordinates

The terminal-coordinate coefficients in the BLC recursion are inherited from
unitary Pauli conjugations.  They are therefore literal signs.  This removes
the phase ambiguity that is harmless for complex matrix rank but essential
for real state-vector rank.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BackwardsLightCone

/-- The Pauli coefficient produced by a terminal BLC block is a sign. -/
theorem TerminalBlockData.transportCoeff_eq_one_or_neg_one
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root} {P : Fin n → Option (Fin 3)}
    (block : TerminalBlockData cone P) :
    block.transportCoeff = 1 ∨ block.transportCoeff = -1 := by
  exact pauli_conjugation_scalar_eq_one_or_neg_one
    (edgeListBlockContraction edges block.gates) P
    (Function.update (fun _ => none) root (some 2)) block.transportCoeff
    block.transport

/-- The coefficient introduced when a fresh Pauli passes through a Clifford
prefix is a sign. -/
theorem TerminalBlockPrefixStep.prefixCoeff_eq_one_or_neg_one
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {P : Fin n → Option (Fin 3)}
    (step : TerminalBlockPrefixStep cone pre P) :
    step.prefixCoeff = 1 ∨ step.prefixCoeff = -1 := by
  exact pauli_conjugation_scalar_eq_one_or_neg_one pre P step.transportedLabel
    step.prefixCoeff step.prefix_transport

/-- The stripped terminal coordinate has only a real sign coefficient. -/
theorem TerminalBlockPrefixStep.strippedCoeff_eq_one_or_neg_one
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {P : Fin n → Option (Fin 3)}
    (step : TerminalBlockPrefixStep cone pre P) :
    (step.block.transportCoeff * step.prefixCoeff)⁻¹ = 1 ∨
      (step.block.transportCoeff * step.prefixCoeff)⁻¹ = -1 := by
  rcases step.block.transportCoeff_eq_one_or_neg_one with hblock | hblock <;>
    rcases step.prefixCoeff_eq_one_or_neg_one with hprefix | hprefix <;>
    simp [hblock, hprefix]

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
