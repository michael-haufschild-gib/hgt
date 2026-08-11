import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.LatticeDirectionCapacity
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.CapacityPolarPortBridge
import Mathlib

/-!
# The vertical fibre of a finite lattice-direction port

If a real Hilbert port tower realizes a finite marked lattice-direction Gram family, then the
multivalued part of its closed graph is exactly the span of the marked directions whose capacities
diverge.
-/

open Filter GaloisForLFunctions.HTGeometry
open scoped Topology RealInnerProductSpace

namespace HTGeometry.ConstraintMotiveRelativity

section PortLaw

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
variable {T : X →ₗ.[ℝ] Y} {r : ℕ}

/-- **Relation-valued form of the finite lattice-direction law.**  A port tower whose Gram family
is a finite marked lattice-direction family has vertical fibre exactly the divergent span. -/
theorem multivaluedHorizon_eq_divergentSpan (P : HilbertPortTower T)
    (L : LatticeDirectionData Y r) (hgram : ∀ n, P.gram n = L.gram n) :
    multivaluedHorizon T = (L.divergentSpan : Set Y) := by
  have hcharts : ∀ n, P.capacityChart.gram n = L.chart.gram n := hgram
  have hlim : P.capacityChart.cometricLimit = L.chart.cometricLimit :=
    CapacityChart.cometricLimit_congr hcharts
  have hker := L.ker_cometricLimit_eq_divergentSpan
  rw [P.multivaluedHorizon_eq_ker, ← P.capacityChart_cometricLimit, hlim, hker]

end PortLaw

end HTGeometry.ConstraintMotiveRelativity
