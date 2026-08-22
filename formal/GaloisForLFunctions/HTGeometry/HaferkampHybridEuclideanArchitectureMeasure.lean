import GaloisForLFunctions.HTGeometry.HaferkampHybridEuclideanArchitectureAnalytic

/-!
# Global Euclidean coordinate measure for a fixed two-qubit architecture

One bounded ball in the complete finite gate-coordinate space pushes forward
directly to a finite positive measure on all `SU(4)` gate assignments.  This
avoids product-measure disintegration when transferring an analytic
coordinate-null locus to independent Haar gate law.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace Metric
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance haferkampHybridEuclideanArchitectureMeasureDecidableEqPauliLabel :
    DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance haferkampHybridEuclideanArchitectureMeasureFintypePauliLabel :
    Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

namespace TwoQubitArchitecture

/-- Apply the global hybrid Euclidean chart independently at every gate
location of a fixed architecture. -/
def hybridEuclideanGateAssignment {n R : ℕ}
    (_A : TwoQubitArchitecture n R) (N : ℕ) :
    (Fin R → boolTwoQubitHybridEuclideanCoordinates N) →
      (Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :=
  fun z r => boolTwoQubitHybridEuclideanGate N (z r)

/-- The gate-assignment version of the global hybrid chart is continuous. -/
theorem continuous_hybridEuclideanGateAssignment {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) :
    Continuous (A.hybridEuclideanGateAssignment N) := by
  apply continuous_pi
  intro r
  exact (continuous_boolTwoQubitHybridEuclideanGate N).comp (continuous_apply r)

/-- One fixed word length centers the global hybrid coordinate chart at every
finite local `SU(4)` gate assignment. -/
theorem exists_uniform_hybridEuclideanGateAssignment {n R : ℕ}
    (A : TwoQubitArchitecture n R) :
    ∃ N : ℕ, ∀ gates : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
      ∃ z : Fin R → boolTwoQubitHybridEuclideanCoordinates N,
        A.hybridEuclideanGateAssignment N z = gates := by
  obtain ⟨N, hN⟩ := exists_boolNonidentityTwoQubitPauliHybridAtlas_center
  refine ⟨N, fun gates => ?_⟩
  choose Y hY using fun r => hN (gates r)
  refine ⟨fun r => boolTwoQubitHybridEuclideanEmbed N 0 (Y r), ?_⟩
  funext r
  exact hY r

/-- The same uniform coordinates center the analytic architecture contraction
at the contraction of any prescribed gate assignment. -/
theorem exists_uniform_hybridEuclideanContraction_center {n R : ℕ}
    (A : TwoQubitArchitecture n R) :
    ∃ N : ℕ, ∀ gates : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
      ∃ z : Fin R → boolTwoQubitHybridEuclideanCoordinates N,
        A.hybridEuclideanGateAssignment N z = gates ∧
        A.hybridEuclideanContraction N z =
          (A.contraction gates : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  obtain ⟨N, hN⟩ := A.exists_uniform_hybridEuclideanGateAssignment
  refine ⟨N, fun gates => ?_⟩
  obtain ⟨z, hz⟩ := hN gates
  refine ⟨z, hz, ?_⟩
  rw [A.hybridEuclideanContraction_eq_contraction N z]
  exact congrArg (fun gs : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ =>
    (A.contraction gs : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) hz

/-- Push forward one bounded full coordinate ball to the complete gate
assignment space. -/
def hybridEuclideanCoordinateMeasure {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) (r : ℝ) :
    Measure (Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :=
  Measure.map (A.hybridEuclideanGateAssignment N)
    (volume.restrict (closedBall 0 r))

/-- The global coordinate measure has exactly the mass of its source ball. -/
theorem hybridEuclideanCoordinateMeasure_apply_univ {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) (r : ℝ) :
    A.hybridEuclideanCoordinateMeasure N r Set.univ =
      (volume : Measure (Fin R → boolTwoQubitHybridEuclideanCoordinates N))
        (closedBall 0 r) := by
  unfold hybridEuclideanCoordinateMeasure
  rw [Measure.map_apply (A.continuous_hybridEuclideanGateAssignment N).measurable
    MeasurableSet.univ]
  simp only [Set.preimage_univ]
  exact Measure.restrict_apply_univ (μ := volume) (closedBall 0 r)

/-- Every positive-radius complete coordinate ball has positive mass. -/
theorem hybridEuclideanCoordinateMeasure_univ_pos {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < A.hybridEuclideanCoordinateMeasure N r Set.univ := by
  rw [hybridEuclideanCoordinateMeasure_apply_univ]
  exact Metric.measure_closedBall_pos volume 0 hr

/-- The global coordinate measure is finite. -/
noncomputable instance hybridEuclideanCoordinateMeasure_isFinite {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) (r : ℝ) :
    IsFiniteMeasure (A.hybridEuclideanCoordinateMeasure N r) where
  measure_univ_lt_top := by
    rw [hybridEuclideanCoordinateMeasure_apply_univ]
    exact measure_closedBall_lt_top

/-- A null preimage in the bounded global Euclidean coordinate ball pushes to
a null gate-assignment set. -/
theorem hybridEuclideanCoordinateMeasure_eq_zero_of_preimage_null {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) (r : ℝ)
    {s : Set (Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)}
    (hs : MeasurableSet s)
    (hzero : (volume : Measure (Fin R → boolTwoQubitHybridEuclideanCoordinates N))
      ((A.hybridEuclideanGateAssignment N) ⁻¹' s ∩ closedBall 0 r) = 0) :
    A.hybridEuclideanCoordinateMeasure N r s = 0 := by
  unfold hybridEuclideanCoordinateMeasure
  rw [Measure.map_apply (A.continuous_hybridEuclideanGateAssignment N).measurable hs,
    Measure.restrict_apply
      ((A.continuous_hybridEuclideanGateAssignment N).measurable hs)]
  exact hzero

/-- Concrete architecture-level Haar-null transfer from the one global
hybrid Euclidean coordinate measure. -/
theorem finiteSpecialUnitaryHaarProduct_eq_zero_of_hybridEuclideanCoordinate_translates_null
    {n R : ℕ} (A : TwoQubitArchitecture n R) (N : ℕ) {r : ℝ} (hr : 0 < r)
    {s : Set (Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)}
    (hs : MeasurableSet s)
    (htrans : ∀ U : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
      A.hybridEuclideanCoordinateMeasure N r ((fun V => U * V) ⁻¹' s) = 0) :
    finiteSpecialUnitaryHaarProduct (Fin R) (Bool × Bool) s = 0 :=
  finiteSpecialUnitaryHaarProduct_eq_zero_of_all_left_translates_null
    (A.hybridEuclideanCoordinateMeasure N r) hs
    (A.hybridEuclideanCoordinateMeasure_univ_pos N hr) htrans

end TwoQubitArchitecture

end

end GaloisForLFunctions.HTGeometry
