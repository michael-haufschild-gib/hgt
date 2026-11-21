import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ResolvedVisits
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateOccupation

/-!
# Mean spacing of zero-gate returns at fine time resolution

Successive first visits separated by at least `h` give a covering and a
packing of return windows. The enclosing-arc Haar law and the spectral
speed squeeze their normalized mean spacing to the reciprocal occupation.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Operator error corresponding to a covering arc of length `r` turns. -/
def zeroGateArcTolerance (r : ℝ) : ℝ := 2 * Real.sin (Real.pi * r / 2)

/-- The zero-gate return set at the indicated covering-arc tolerance. -/
def zeroGateReturnSet {n : ℕ} (H : selfAdjoint (Reg n)) (r : ℝ) : Set ℝ :=
  {t | orbitCircuitDistance H 0 t ≤ zeroGateArcTolerance r}

/-- Haar mass of the short-arc return set for a `D`-dimensional register. -/
def zeroGateArcDensity (D : ℕ) (r : ℝ) : ℝ := (D : ℝ) * r ^ (D - 1)

/-- Each recorded time is the first return at least `h` after its predecessor. -/
def IsZeroGateReturnSequence {n : ℕ} (H : selfAdjoint (Reg n)) (r a h : ℝ)
    (t : ℕ → ℝ) : Prop :=
  t 0 = a ∧ ∀ j, IsLeast {v | t j + h ≤ v ∧ v ∈ zeroGateReturnSet H r} (t (j + 1))

end

end GaloisForLFunctions.HTGeometry
