import GaloisForLFunctions.HTGeometry.HaferkampSpecialUnitaryPauliCoordinateMeasure
import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryHaarProductNullTransfer

/-!
# Positive local coordinate measure for finite two-qubit gate assignments

Taking the finite product of the local fifteen-coordinate Pauli measure gives
a positive finite measure on a complete `SU(4)` gate assignment.  This is the
concrete measure required by the architecture-level Haar-null transfer.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Independent local Pauli-coordinate measures for every gate of a finite
architecture. -/
def boolNonidentityTwoQubitPauliCoordinateProductMeasure
    (κ : Type*) [Fintype κ] (r : ℝ) :
    Measure (κ → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :=
  Measure.pi fun _ => boolNonidentityTwoQubitPauliCoordinateMeasure r

/-- The total mass of the gate-assignment coordinate measure is the finite
product of its one-gate masses. -/
theorem boolNonidentityTwoQubitPauliCoordinateProductMeasure_apply_univ
    (κ : Type*) [Fintype κ] (r : ℝ) :
    boolNonidentityTwoQubitPauliCoordinateProductMeasure κ r Set.univ =
      ∏ _ : κ, boolNonidentityTwoQubitPauliCoordinateMeasure r Set.univ := by
  unfold boolNonidentityTwoQubitPauliCoordinateProductMeasure
  exact Measure.pi_univ _

/-- Every positive-radius local Pauli-coordinate product has strictly
positive total mass, including the empty gate tuple. -/
theorem boolNonidentityTwoQubitPauliCoordinateProductMeasure_univ_pos
    (κ : Type*) [Fintype κ] {r : ℝ} (hr : 0 < r) :
    0 < boolNonidentityTwoQubitPauliCoordinateProductMeasure κ r Set.univ := by
  rw [boolNonidentityTwoQubitPauliCoordinateProductMeasure_apply_univ]
  exact CanonicallyOrderedAdd.prod_pos.mpr fun _ _ =>
    boolNonidentityTwoQubitPauliCoordinateMeasure_univ_pos hr

/-- The finite product of local Pauli-coordinate measures is finite. -/
noncomputable instance boolNonidentityTwoQubitPauliCoordinateProductMeasure_isFinite
    (κ : Type*) [Fintype κ] (r : ℝ) :
    IsFiniteMeasure (boolNonidentityTwoQubitPauliCoordinateProductMeasure κ r) := by
  unfold boolNonidentityTwoQubitPauliCoordinateProductMeasure
  infer_instance

/-- Concrete architecture-level `SU(4)` Haar-null transfer for the product
local Pauli-coordinate measure. -/
theorem finiteSpecialUnitaryHaarProduct_eq_zero_of_pauliCoordinate_translates_null
    {κ : Type*} [Fintype κ] {r : ℝ} (hr : 0 < r)
    {s : Set (κ → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)}
    (hs : MeasurableSet s)
    (htrans : ∀ U : κ → Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
      boolNonidentityTwoQubitPauliCoordinateProductMeasure κ r
        ((fun V => U * V) ⁻¹' s) = 0) :
    finiteSpecialUnitaryHaarProduct κ (Bool × Bool) s = 0 :=
  finiteSpecialUnitaryHaarProduct_eq_zero_of_all_left_translates_null
    (boolNonidentityTwoQubitPauliCoordinateProductMeasure κ r) hs
    (boolNonidentityTwoQubitPauliCoordinateProductMeasure_univ_pos κ hr) htrans

end

end GaloisForLFunctions.HTGeometry
