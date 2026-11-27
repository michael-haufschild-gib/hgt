import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion
import GaloisForLFunctions.HTGeometry.Quantum.FirstCircuitSaturationBoundary

/-! # Reflection in time preserves distance to every physical gate budget -/

open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- Invert an attaining circuit and conjugate its global phase. Applying
the same operation at the reflected time gives equality of optimal errors. -/
theorem orbitCircuitDistance_neg_time {N : ℕ} (H : selfAdjoint (Reg N)) (j : ℕ) (t : ℝ) :
    orbitCircuitDistance H j (-t)=orbitCircuitDistance H j t := by
  have hle (r : ℝ) : orbitCircuitDistance H j (-r)≤orbitCircuitDistance H j r := by
    apply (hasProjectiveCircuitApproximation_iff_infDist ..).mp
    exact ((hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val r) j _).mpr le_rfl).neg_time H
  exact le_antisymm (hle t) (by simpa only [neg_neg] using hle (-t))

#print axioms orbitCircuitDistance_neg_time
end
end GaloisForLFunctions.HTGeometry
