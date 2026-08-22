import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryPauliHybridEuclideanRank
import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryHaarNullTransfer

/-!
# Positive Euclidean coordinate measure for the global hybrid `SU(4)` atlas

The joint finite Euclidean hybrid chart pushes every bounded positive-radius
ball to a finite positive `SU(4)` measure.  Its all-left-translates nullity
is exactly the hypothesis that transfers to normalized Haar nullity.
-/

open Filter MeasureTheory MeasureTheory.Measure TopologicalSpace Metric
open scoped Matrix.Norms.L2Operator Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance : DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance : Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

/-- The `SU(4)`-valued version of the joint hybrid Euclidean chart. -/
def boolTwoQubitHybridEuclideanGate (N : ℕ) :
    boolTwoQubitHybridEuclideanCoordinates N →
      Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
  fun z => boolNonidentityTwoQubitPauliHybridAtlas N
    (boolTwoQubitHybridPauliProjection N z)
    (boolTwoQubitHybridWordProjection N z)

/-- Coercing the `SU(4)` chart to matrices recovers its analytic Euclidean chart. -/
theorem boolTwoQubitHybridEuclideanGate_coe
    (N : ℕ) (z : boolTwoQubitHybridEuclideanCoordinates N) :
    (boolTwoQubitHybridEuclideanGate N z :
      Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolTwoQubitHybridEuclideanChart N z := rfl

/-- The actual `SU(4)`-valued joint hybrid chart is continuous. -/
theorem continuous_boolTwoQubitHybridEuclideanGate
    (N : ℕ) : Continuous (boolTwoQubitHybridEuclideanGate N) := by
  apply continuous_induced_rng.2
  change Continuous (fun z =>
    (boolTwoQubitHybridEuclideanGate N z :
      Matrix (Bool × Bool) (Bool × Bool) ℂ))
  rw [show (fun z =>
    (boolTwoQubitHybridEuclideanGate N z :
      Matrix (Bool × Bool) (Bool × Bool) ℂ)) =
      boolTwoQubitHybridEuclideanChart N by
        funext z
        exact boolTwoQubitHybridEuclideanGate_coe N z]
  rw [continuous_iff_continuousAt]
  intro z
  exact (analyticAt_boolTwoQubitHybridEuclideanChart N z).continuousAt

/-- Push forward Euclidean volume on a bounded joint-coordinate ball to `SU(4)`. -/
def boolTwoQubitHybridEuclideanMeasure (N : ℕ) (r : ℝ) :
    Measure (Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :=
  Measure.map (boolTwoQubitHybridEuclideanGate N)
    (volume.restrict (closedBall 0 r))

/-- The hybrid coordinate measure has exactly its source ball's total mass. -/
theorem boolTwoQubitHybridEuclideanMeasure_apply_univ
    (N : ℕ) (r : ℝ) :
    boolTwoQubitHybridEuclideanMeasure N r Set.univ =
      (volume : Measure (boolTwoQubitHybridEuclideanCoordinates N))
        (closedBall 0 r) := by
  unfold boolTwoQubitHybridEuclideanMeasure
  rw [Measure.map_apply (continuous_boolTwoQubitHybridEuclideanGate N).measurable
    MeasurableSet.univ]
  simp only [Set.preimage_univ]
  exact Measure.restrict_apply_univ (μ := volume) (closedBall 0 r)

/-- Every positive-radius hybrid coordinate ball has positive mass. -/
theorem boolTwoQubitHybridEuclideanMeasure_univ_pos
    (N : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < boolTwoQubitHybridEuclideanMeasure N r Set.univ := by
  rw [boolTwoQubitHybridEuclideanMeasure_apply_univ]
  exact Metric.measure_closedBall_pos volume 0 hr

/-- The hybrid coordinate measure is finite. -/
noncomputable instance boolTwoQubitHybridEuclideanMeasure_isFinite
    (N : ℕ) (r : ℝ) : IsFiniteMeasure (boolTwoQubitHybridEuclideanMeasure N r) where
  measure_univ_lt_top := by
    rw [boolTwoQubitHybridEuclideanMeasure_apply_univ]
    exact measure_closedBall_lt_top

/-- Nullity of the ball-restricted coordinate preimage implies target nullity. -/
theorem boolTwoQubitHybridEuclideanMeasure_eq_zero_of_preimage_null
    (N : ℕ) (r : ℝ)
    {s : Set (Matrix.specialUnitaryGroup (Bool × Bool) ℂ)}
    (hs : MeasurableSet s)
    (hzero : (volume : Measure (boolTwoQubitHybridEuclideanCoordinates N))
      ((boolTwoQubitHybridEuclideanGate N) ⁻¹' s ∩ closedBall 0 r) = 0) :
    boolTwoQubitHybridEuclideanMeasure N r s = 0 := by
  unfold boolTwoQubitHybridEuclideanMeasure
  rw [Measure.map_apply (continuous_boolTwoQubitHybridEuclideanGate N).measurable hs,
    Measure.restrict_apply
      ((continuous_boolTwoQubitHybridEuclideanGate N).measurable hs)]
  exact hzero

/-- Concrete `SU(4)` Haar-null transfer for the global joint hybrid atlas. -/
theorem finiteSpecialUnitaryHaar_eq_zero_of_hybridEuclidean_translates_null
    (N : ℕ) {r : ℝ} (hr : 0 < r)
    {s : Set (Matrix.specialUnitaryGroup (Bool × Bool) ℂ)}
    (hs : MeasurableSet s)
    (htrans : ∀ U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
      boolTwoQubitHybridEuclideanMeasure N r
        ((fun V => U * V) ⁻¹' s) = 0) :
    finiteSpecialUnitaryHaar (Bool × Bool) s = 0 :=
  finiteSpecialUnitaryHaar_eq_zero_of_all_left_translates_null
    (boolTwoQubitHybridEuclideanMeasure N r) hs
    (boolTwoQubitHybridEuclideanMeasure_univ_pos N hr) htrans

end

end GaloisForLFunctions.HTGeometry
