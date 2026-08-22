import GaloisForLFunctions.HTGeometry.HaferkampTerminalHybridEuclideanArchitectureMeasure

/-!
# Intrinsic terminal-hybrid accessible rank

For a fixed architecture, a gate assignment is rank-deficient when every
right-translated terminal-hybrid Euclidean realization through that assignment
has differential rank below a threshold.  This is independent of a chosen
coordinate centre by definition, and the Appendix-B witness makes its pullback
under every right-translated coordinate law null.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace Metric
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance : DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance : Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

namespace TwoQubitArchitecture

/-- A gate tuple has terminal-hybrid rank below `k` when every fixed right
translate and every terminal-hybrid Euclidean realization through it has
differential rank below `k`. -/
def terminalHybridRankDeficient {n R : ℕ}
    (A : TwoQubitArchitecture n R) (k : ℕ)
    (gates : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) : Prop :=
  ∀ (N : ℕ) (U : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (x : EuclideanSpace ℝ (Fin (Fintype.card
      (Fin R × terminalHybridCoordinateIndex N)))),
    A.terminalHybridEuclideanReindexedGateAssignment N x * U = gates →
      Module.finrank ℝ
        (fderiv ℝ (A.terminalHybridEuclideanRightUnshiftedReindexedChart N U)
          x).range < k

end TwoQubitArchitecture

namespace BackwardsLightCone

/-- Pulling terminal-hybrid rank deficiency back through a fixed coordinate
chart and right translate lands in that chart's analytic low-rank locus. -/
theorem TerminalBlockPrefixAssembly.terminalHybridRankDeficient_preimage_subset_lowRank
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels) (N : ℕ)
    (U : Fin assembly.flattenedEdgeWord.length →
      Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    ((fun x => TwoQubitArchitecture.terminalHybridEuclideanReindexedGateAssignment
      assembly.flattenedArchitecture N x * U) ⁻¹'
      {gates | assembly.flattenedArchitecture.terminalHybridRankDeficient labels.length gates}) ≤
      {x | Module.finrank ℝ
        (fderiv ℝ
          (assembly.flattenedArchitecture.terminalHybridEuclideanRightUnshiftedReindexedChart N U)
          x).range < labels.length} := by
  intro x hx
  change assembly.flattenedArchitecture.terminalHybridRankDeficient labels.length
    (assembly.flattenedArchitecture.terminalHybridEuclideanReindexedGateAssignment N x * U) at hx
  exact hx N U x rfl

/-- Every fixed right translate of the terminal-hybrid coordinate law
annihilates the intrinsic rank-deficient gate assignments, provided that set
is measurable. -/
theorem TerminalBlockPrefixAssembly.terminalHybridRankDeficient_rightTranslate_null
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℂ (fun i : Fin labels.length =>
      finitePauliMatrix (labels.get i)))
    (N : ℕ) (U : Fin assembly.flattenedEdgeWord.length →
      Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (z : Fin assembly.flattenedEdgeWord.length →
      boolTwoQubitHybridEuclideanCoordinates N)
    (hz : (fun r => boolTwoQubitHybridEuclideanGate N (z r) * U r) =
      assembly.flattenedGateParameters)
    (hs : MeasurableSet {gates |
      assembly.flattenedArchitecture.terminalHybridRankDeficient labels.length gates}) :
    assembly.flattenedArchitecture.terminalHybridEuclideanReindexedCoordinateMeasure N 1
      ((fun V => V * U) ⁻¹'
        {gates | assembly.flattenedArchitecture.terminalHybridRankDeficient labels.length gates}) = 0 := by
  have hsU : MeasurableSet ((fun V => V * U) ⁻¹'
      {gates | assembly.flattenedArchitecture.terminalHybridRankDeficient labels.length gates}) :=
    hs.preimage (measurable_mul_const U)
  apply TwoQubitArchitecture.terminalHybridEuclideanReindexedCoordinateMeasure_eq_zero_of_preimage_null
    assembly.flattenedArchitecture N 1 hsU
  apply measure_mono_null
    (t := {x | Module.finrank ℝ
      (fderiv ℝ
        (assembly.flattenedArchitecture.terminalHybridEuclideanRightUnshiftedReindexedChart N U)
        x).range < labels.length})
  · intro x hx
    exact assembly.terminalHybridRankDeficient_preimage_subset_lowRank N U hx.1
  · exact assembly.unshiftedReindexedChart_lowRank_volume_zero hlabels N U z hz

/-- The intrinsic terminal-hybrid rank-deficient locus of a flattened BLC
assembly is null for independent Haar gates once its measurability has been
established. -/
theorem TerminalBlockPrefixAssembly.terminalHybridRankDeficient_haar_null
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℂ (fun i : Fin labels.length =>
      finitePauliMatrix (labels.get i)))
    (hs : MeasurableSet {gates |
      assembly.flattenedArchitecture.terminalHybridRankDeficient labels.length gates}) :
    finiteSpecialUnitaryHaarProduct (Fin assembly.flattenedEdgeWord.length) (Bool × Bool)
      {gates | assembly.flattenedArchitecture.terminalHybridRankDeficient labels.length gates} = 0 := by
  obtain ⟨N, hN⟩ :=
    TerminalBlockPrefixAssembly.exists_uniform_terminalHybridEuclidean_right_center assembly
  apply TwoQubitArchitecture.finiteSpecialUnitaryHaarProduct_eq_zero_of_terminalHybridEuclideanReindexedCoordinate_right_translates_null
    assembly.flattenedArchitecture N zero_lt_one hs
  intro U
  obtain ⟨z, hz⟩ := hN U
  exact assembly.terminalHybridRankDeficient_rightTranslate_null hlabels N U z hz hs

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
