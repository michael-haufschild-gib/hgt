import GaloisForLFunctions.HTGeometry.HaferkampTerminalHybridEuclideanArchitectureAnalytic
import GaloisForLFunctions.HTGeometry.HaferkampTerminalHybridEuclideanRightGenericity
import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryHaarProductRightNullTransfer

/-!
# Terminal-hybrid Euclidean coordinate measure for a fixed architecture

The terminal-phase augmented local chart is assigned independently to every
gate location.  A bounded ball in this complete finite Euclidean source gives
a finite positive coordinate measure, and its right translates transfer to
the independent Haar gate law.
-/

open Filter MeasureTheory MeasureTheory.Measure TopologicalSpace Metric
open scoped Matrix.Norms.L2Operator Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance : DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance : Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

/-- The actual `SU(4)`-valued terminal-hybrid chart is continuous. -/
theorem continuous_terminalHybridEuclideanGate
    (N : ℕ) : Continuous (terminalHybridEuclideanGate N) := by
  apply continuous_induced_rng.2
  change Continuous (fun z =>
    (terminalHybridEuclideanGate N z :
      Matrix (Bool × Bool) (Bool × Bool) ℂ))
  rw [continuous_iff_continuousAt]
  intro z
  exact (analyticAt_terminalHybridEuclideanGate_coe N z).continuousAt

namespace TwoQubitArchitecture

/-- Apply the terminal-phase augmented Euclidean chart at every fixed gate
location. -/
def terminalHybridEuclideanGateAssignment {n R : ℕ}
    (_A : TwoQubitArchitecture n R) (N : ℕ) :
    (Fin R → terminalHybridEuclideanCoordinates N) →
      (Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :=
  fun z r => terminalHybridEuclideanGate N (z r)

/-- The gate-assignment terminal-hybrid chart is continuous. -/
theorem continuous_terminalHybridEuclideanGateAssignment {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) :
    Continuous (A.terminalHybridEuclideanGateAssignment N) := by
  apply continuous_pi
  intro r
  exact (continuous_terminalHybridEuclideanGate N).comp (continuous_apply r)

/-- Apply the terminal-hybrid gate chart after reindexing all gate-coordinate
blocks into one literal finite Euclidean source. -/
def terminalHybridEuclideanReindexedGateAssignment {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) :
    EuclideanSpace ℝ (Fin (Fintype.card
      (Fin R × terminalHybridCoordinateIndex N))) →
      (Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :=
  fun x => A.terminalHybridEuclideanGateAssignment N
    (terminalHybridCoordinateReindex R N x)

/-- The literal finite Euclidean terminal-hybrid gate-assignment chart is
continuous. -/
theorem continuous_terminalHybridEuclideanReindexedGateAssignment {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) :
    Continuous (A.terminalHybridEuclideanReindexedGateAssignment N) := by
  exact (A.continuous_terminalHybridEuclideanGateAssignment N).comp
    (terminalHybridCoordinateReindex R N).continuous

/-- Push forward one bounded terminal-hybrid coordinate ball to the complete
gate-assignment space. -/
def terminalHybridEuclideanCoordinateMeasure {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) (r : ℝ) :
    Measure (Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :=
  Measure.map (A.terminalHybridEuclideanGateAssignment N)
    (volume.restrict (closedBall 0 r))

/-- The terminal-hybrid coordinate measure has exactly the mass of its source
ball. -/
theorem terminalHybridEuclideanCoordinateMeasure_apply_univ {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) (r : ℝ) :
    A.terminalHybridEuclideanCoordinateMeasure N r Set.univ =
      (volume : Measure (Fin R → terminalHybridEuclideanCoordinates N))
        (closedBall 0 r) := by
  unfold terminalHybridEuclideanCoordinateMeasure
  rw [Measure.map_apply
    (A.continuous_terminalHybridEuclideanGateAssignment N).measurable
    MeasurableSet.univ]
  simp only [Set.preimage_univ]
  exact Measure.restrict_apply_univ (μ := volume) (closedBall 0 r)

/-- Every positive-radius complete terminal-hybrid coordinate ball has
positive mass. -/
theorem terminalHybridEuclideanCoordinateMeasure_univ_pos {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < A.terminalHybridEuclideanCoordinateMeasure N r Set.univ := by
  rw [terminalHybridEuclideanCoordinateMeasure_apply_univ]
  exact Metric.measure_closedBall_pos volume 0 hr

/-- The complete terminal-hybrid coordinate measure is finite. -/
noncomputable instance terminalHybridEuclideanCoordinateMeasure_isFinite {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) (r : ℝ) :
    IsFiniteMeasure (A.terminalHybridEuclideanCoordinateMeasure N r) where
  measure_univ_lt_top := by
    rw [terminalHybridEuclideanCoordinateMeasure_apply_univ]
    exact measure_closedBall_lt_top

/-- A null terminal-hybrid coordinate preimage in the bounded source ball
pushes forward to a null gate-assignment set. -/
theorem terminalHybridEuclideanCoordinateMeasure_eq_zero_of_preimage_null {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) (r : ℝ)
    {s : Set (Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)}
    (hs : MeasurableSet s)
    (hzero : (volume : Measure (Fin R → terminalHybridEuclideanCoordinates N))
      ((A.terminalHybridEuclideanGateAssignment N) ⁻¹' s ∩ closedBall 0 r) = 0) :
    A.terminalHybridEuclideanCoordinateMeasure N r s = 0 := by
  unfold terminalHybridEuclideanCoordinateMeasure
  rw [Measure.map_apply
    (A.continuous_terminalHybridEuclideanGateAssignment N).measurable hs,
    Measure.restrict_apply
      ((A.continuous_terminalHybridEuclideanGateAssignment N).measurable hs)]
  exact hzero

/-- Push forward one bounded literal finite Euclidean coordinate ball through
the complete terminal-hybrid gate chart. -/
def terminalHybridEuclideanReindexedCoordinateMeasure {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) (r : ℝ) :
    Measure (Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :=
  Measure.map (A.terminalHybridEuclideanReindexedGateAssignment N)
    (volume.restrict (closedBall 0 r))

/-- The reindexed terminal-hybrid coordinate measure has exactly the mass of
its literal finite Euclidean source ball. -/
theorem terminalHybridEuclideanReindexedCoordinateMeasure_apply_univ {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) (r : ℝ) :
    A.terminalHybridEuclideanReindexedCoordinateMeasure N r Set.univ =
      (volume : Measure (EuclideanSpace ℝ (Fin (Fintype.card
        (Fin R × terminalHybridCoordinateIndex N))))) (closedBall 0 r) := by
  unfold terminalHybridEuclideanReindexedCoordinateMeasure
  rw [Measure.map_apply
    (A.continuous_terminalHybridEuclideanReindexedGateAssignment N).measurable
    MeasurableSet.univ]
  simp only [Set.preimage_univ]
  exact Measure.restrict_apply_univ (μ := volume) (closedBall 0 r)

/-- Every positive-radius reindexed terminal-hybrid coordinate ball has
positive mass. -/
theorem terminalHybridEuclideanReindexedCoordinateMeasure_univ_pos {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < A.terminalHybridEuclideanReindexedCoordinateMeasure N r Set.univ := by
  rw [terminalHybridEuclideanReindexedCoordinateMeasure_apply_univ]
  exact Metric.measure_closedBall_pos volume 0 hr

/-- The reindexed terminal-hybrid coordinate measure is finite. -/
noncomputable instance terminalHybridEuclideanReindexedCoordinateMeasure_isFinite {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) (r : ℝ) :
    IsFiniteMeasure (A.terminalHybridEuclideanReindexedCoordinateMeasure N r) where
  measure_univ_lt_top := by
    rw [terminalHybridEuclideanReindexedCoordinateMeasure_apply_univ]
    exact measure_closedBall_lt_top

/-- A null preimage in the reindexed terminal-hybrid source ball pushes to a
null gate-assignment set. -/
theorem terminalHybridEuclideanReindexedCoordinateMeasure_eq_zero_of_preimage_null
    {n R : ℕ} (A : TwoQubitArchitecture n R) (N : ℕ) (r : ℝ)
    {s : Set (Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)}
    (hs : MeasurableSet s)
    (hzero : (volume : Measure (EuclideanSpace ℝ (Fin (Fintype.card
      (Fin R × terminalHybridCoordinateIndex N)))))
      ((A.terminalHybridEuclideanReindexedGateAssignment N) ⁻¹' s ∩
        closedBall 0 r) = 0) :
    A.terminalHybridEuclideanReindexedCoordinateMeasure N r s = 0 := by
  unfold terminalHybridEuclideanReindexedCoordinateMeasure
  rw [Measure.map_apply
    (A.continuous_terminalHybridEuclideanReindexedGateAssignment N).measurable hs,
    Measure.restrict_apply
      ((A.continuous_terminalHybridEuclideanReindexedGateAssignment N).measurable hs)]
  exact hzero

/-- Concrete architecture-level Haar-null transfer from one complete
terminal-hybrid Euclidean coordinate measure and all its right translates. -/
theorem finiteSpecialUnitaryHaarProduct_eq_zero_of_terminalHybridEuclideanCoordinate_right_translates_null
    {n R : ℕ} (A : TwoQubitArchitecture n R) (N : ℕ) {r : ℝ} (hr : 0 < r)
    {s : Set (Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)}
    (hs : MeasurableSet s)
    (htrans : ∀ U : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
      A.terminalHybridEuclideanCoordinateMeasure N r
        ((fun V => V * U) ⁻¹' s) = 0) :
    finiteSpecialUnitaryHaarProduct (Fin R) (Bool × Bool) s = 0 :=
  finiteSpecialUnitaryHaarProduct_eq_zero_of_all_right_translates_null
    (A.terminalHybridEuclideanCoordinateMeasure N r) hs
    (A.terminalHybridEuclideanCoordinateMeasure_univ_pos N hr) htrans

/-- Concrete architecture-level Haar-null transfer from the literal finite
Euclidean terminal-hybrid coordinate source and all its right translates. -/
theorem finiteSpecialUnitaryHaarProduct_eq_zero_of_terminalHybridEuclideanReindexedCoordinate_right_translates_null
    {n R : ℕ} (A : TwoQubitArchitecture n R) (N : ℕ) {r : ℝ} (hr : 0 < r)
    {s : Set (Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)}
    (hs : MeasurableSet s)
    (htrans : ∀ U : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
      A.terminalHybridEuclideanReindexedCoordinateMeasure N r
        ((fun V => V * U) ⁻¹' s) = 0) :
    finiteSpecialUnitaryHaarProduct (Fin R) (Bool × Bool) s = 0 :=
  finiteSpecialUnitaryHaarProduct_eq_zero_of_all_right_translates_null
    (A.terminalHybridEuclideanReindexedCoordinateMeasure N r) hs
    (A.terminalHybridEuclideanReindexedCoordinateMeasure_univ_pos N hr) htrans

end TwoQubitArchitecture

end

end GaloisForLFunctions.HTGeometry
