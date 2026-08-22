import GaloisForLFunctions.HTGeometry.HaferkampSpecialUnitaryPauliLocalDiffeomorph
import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryHaarNullTransfer

/-!
# Positive local coordinate measure for the two-qubit `SU(4)` Pauli chart

The certified fifteen-coordinate Pauli chart pushes finite positive Lebesgue
mass from every sufficiently small closed coordinate ball to `SU(4)`.  This
is the concrete coordinate measure consumed by the Haar-null transfer.
-/

open Filter MeasureTheory MeasureTheory.Measure TopologicalSpace Metric
open scoped Matrix.Norms.Operator Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance haferkampSpecialUnitaryPauliCoordinateMeasureDecidableEqPauliLabel :
    DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance haferkampSpecialUnitaryPauliCoordinateMeasureFintypePauliLabel :
    Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

/-- The actual `SU(4)`-valued Pauli coordinate map is continuous. -/
theorem continuous_boolNonidentityTwoQubitPauliCoordinateGate :
    Continuous boolNonidentityTwoQubitPauliCoordinateGate := by
  apply continuous_induced_rng.2
  change Continuous (fun x =>
    (boolNonidentityTwoQubitPauliCoordinateGate x :
      Matrix (Bool × Bool) (Bool × Bool) ℂ))
  rw [show (fun x =>
    (boolNonidentityTwoQubitPauliCoordinateGate x :
      Matrix (Bool × Bool) (Bool × Bool) ℂ)) =
      boolNonidentityTwoQubitPauliCoordinateChart by
        funext x
        exact boolNonidentityTwoQubitPauliCoordinateGate_coe x]
  rw [continuous_iff_continuousAt]
  intro x
  exact (analyticAt_boolNonidentityTwoQubitPauliCoordinateChart x).continuousAt

/-- The inverse-function source contains a positive-radius closed coordinate
ball about the origin. -/
theorem exists_boolNonidentityTwoQubitPauli_coordinate_closedBall :
    ∃ r : ℝ, 0 < r ∧ closedBall 0 r ⊆
      boolNonidentityTwoQubitPauliObservedLocalHomeomorph.source := by
  have hsource : boolNonidentityTwoQubitPauliObservedLocalHomeomorph.source ∈ 𝓝 0 :=
    boolNonidentityTwoQubitPauliObservedLocalHomeomorph.open_source.mem_nhds
      zero_mem_boolNonidentityTwoQubitPauliObservedLocalHomeomorph_source
  exact nhds_basis_closedBall.mem_iff.mp hsource

/-- Pushforward of Lebesgue measure on a finite Pauli-coordinate ball. -/
def boolNonidentityTwoQubitPauliCoordinateMeasure (r : ℝ) :
    Measure (Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :=
  Measure.map boolNonidentityTwoQubitPauliCoordinateGate
    (volume.restrict (closedBall 0 r))

/-- The coordinate measure has exactly the source ball's total mass. -/
theorem boolNonidentityTwoQubitPauliCoordinateMeasure_apply_univ (r : ℝ) :
    boolNonidentityTwoQubitPauliCoordinateMeasure r Set.univ =
      (volume : Measure (boolNonidentityTwoQubitPauliLabel → ℝ))
        (closedBall 0 r) := by
  unfold boolNonidentityTwoQubitPauliCoordinateMeasure
  rw [Measure.map_apply continuous_boolNonidentityTwoQubitPauliCoordinateGate.measurable
    MeasurableSet.univ]
  simp only [Set.preimage_univ]
  exact Measure.restrict_apply_univ (μ := volume) (closedBall 0 r)

/-- Every positive-radius Pauli-coordinate ball pushes forward to a measure
of strictly positive mass. -/
theorem boolNonidentityTwoQubitPauliCoordinateMeasure_univ_pos
    {r : ℝ} (hr : 0 < r) :
    0 < boolNonidentityTwoQubitPauliCoordinateMeasure r Set.univ := by
  rw [boolNonidentityTwoQubitPauliCoordinateMeasure_apply_univ]
  exact Metric.measure_closedBall_pos volume 0 hr

/-- The coordinate measure is finite, hence available to Haar convolution. -/
noncomputable instance boolNonidentityTwoQubitPauliCoordinateMeasure_isFinite
    (r : ℝ) : IsFiniteMeasure (boolNonidentityTwoQubitPauliCoordinateMeasure r) where
  measure_univ_lt_top := by
    rw [boolNonidentityTwoQubitPauliCoordinateMeasure_apply_univ]
    exact measure_closedBall_lt_top

/-- A measurable set is null for the local Pauli-coordinate measure as soon
as its coordinate preimage inside the defining ball is Lebesgue-null. -/
theorem boolNonidentityTwoQubitPauliCoordinateMeasure_eq_zero_of_preimage_null
    (r : ℝ)
    {s : Set (Matrix.specialUnitaryGroup (Bool × Bool) ℂ)}
    (hs : MeasurableSet s)
    (hzero : (volume : Measure (boolNonidentityTwoQubitPauliLabel → ℝ))
      (boolNonidentityTwoQubitPauliCoordinateGate ⁻¹' s ∩ closedBall 0 r) = 0) :
    boolNonidentityTwoQubitPauliCoordinateMeasure r s = 0 := by
  unfold boolNonidentityTwoQubitPauliCoordinateMeasure
  rw [Measure.map_apply continuous_boolNonidentityTwoQubitPauliCoordinateGate.measurable hs,
    Measure.restrict_apply
      (continuous_boolNonidentityTwoQubitPauliCoordinateGate.measurable hs)]
  exact hzero

/-- Concrete `SU(4)` form of Haar-null transfer for the Pauli chart measure. -/
theorem finiteSpecialUnitaryHaar_eq_zero_of_pauliCoordinate_translates_null
    {r : ℝ} (hr : 0 < r)
    {s : Set (Matrix.specialUnitaryGroup (Bool × Bool) ℂ)}
    (hs : MeasurableSet s)
    (htrans : ∀ U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
      boolNonidentityTwoQubitPauliCoordinateMeasure r
        ((fun V => U * V) ⁻¹' s) = 0) :
    finiteSpecialUnitaryHaar (Bool × Bool) s = 0 :=
  finiteSpecialUnitaryHaar_eq_zero_of_all_left_translates_null
    (boolNonidentityTwoQubitPauliCoordinateMeasure r) hs
    (boolNonidentityTwoQubitPauliCoordinateMeasure_univ_pos hr) htrans

end

end GaloisForLFunctions.HTGeometry
