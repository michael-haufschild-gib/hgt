import GaloisForLFunctions.HTGeometry.HaferkampTerminalHybridEuclideanRightRank
import GaloisForLFunctions.HTGeometry.AnalyticFiniteRankLocus
import GaloisForLFunctions.HTGeometry.FiniteEuclideanGateCoordinates

/-!
# Generic right-translated terminal-hybrid rank

The terminal Pauli rank witness is made into an analytic rank-locus statement
on one literal finite Euclidean source.  All affine coordinate changes are
represented by continuous linear maps, so the derivative calculation avoids
normalizing finite function addition.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.L2Operator

local instance haferkampTerminalHybridEuclideanRightGenericityDecidableEqPauliLabel :
    DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance haferkampTerminalHybridEuclideanRightGenericityFintypePauliLabel :
    Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

/-- Reindex every terminal-hybrid gate-coordinate block into one literal
finite Euclidean source. -/
def terminalHybridCoordinateReindex (R N : ℕ) :
    EuclideanSpace ℝ (Fin (Fintype.card
      (Fin R × terminalHybridCoordinateIndex N))) →L[ℝ]
      (Fin R → terminalHybridEuclideanCoordinates N) :=
  (finiteEuclideanGateUnflatten R (terminalHybridCoordinateIndex N)).comp
    (euclideanReindex (Fin R × terminalHybridCoordinateIndex N))

/-- The flattened terminal-hybrid coordinate source covers every gate-wise
terminal-hybrid coordinate assignment. -/
theorem terminalHybridCoordinateReindex_surjective (R N : ℕ) :
    Function.Surjective (terminalHybridCoordinateReindex R N) := by
  intro y
  obtain ⟨x, hx⟩ :=
    finiteEuclideanGateUnflatten_surjective R (terminalHybridCoordinateIndex N) y
  obtain ⟨w, hw⟩ :=
    euclideanReindex_surjective (Fin R × terminalHybridCoordinateIndex N) x
  refine ⟨w, ?_⟩
  change finiteEuclideanGateUnflatten R (terminalHybridCoordinateIndex N)
    (euclideanReindex (Fin R × terminalHybridCoordinateIndex N) w) = y
  rw [hw]
  exact hx

namespace TwoQubitArchitecture

/-- The right-translated terminal-hybrid contraction after reindexing all
gate-coordinate blocks into one finite Euclidean source. -/
def terminalHybridEuclideanRightReindexedChart {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ)
    (U : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (base : Fin R → terminalHybridEuclideanCoordinates N) :
    EuclideanSpace ℝ (Fin (Fintype.card
      (Fin R × terminalHybridCoordinateIndex N))) →
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  fun x => A.terminalHybridEuclideanRightContraction N U
    (base + terminalHybridCoordinateReindex R N x)

/-- The reindexed right-translated terminal-hybrid chart is analytic at every
finite Euclidean coordinate. -/
theorem analyticAt_terminalHybridEuclideanRightReindexedChart {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ)
    (U : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (base : Fin R → terminalHybridEuclideanCoordinates N)
    (x : EuclideanSpace ℝ (Fin (Fintype.card
      (Fin R × terminalHybridCoordinateIndex N)))) :
    AnalyticAt ℝ (A.terminalHybridEuclideanRightReindexedChart N U base) x := by
  change AnalyticAt ℝ
    (fun y => A.terminalHybridEuclideanRightContraction N U
      (base + terminalHybridCoordinateReindex R N y)) x
  have hL : AnalyticAt ℝ
      (fun y => base + terminalHybridCoordinateReindex R N y) x :=
    (analyticAt_const (v := base)).add
      ((terminalHybridCoordinateReindex R N).analyticAt x)
  exact AnalyticAt.comp
    (f := fun y => base + terminalHybridCoordinateReindex R N y)
    (g := A.terminalHybridEuclideanRightContraction N U)
    (A.analyticAt_terminalHybridEuclideanRightContraction N U
      (base + terminalHybridCoordinateReindex R N x)) hL

end TwoQubitArchitecture

namespace TwoQubitArchitecture

/-- The right-translated terminal-hybrid contraction after reindexing every
gate-coordinate block into one finite Euclidean source, without a base shift. -/
def terminalHybridEuclideanRightUnshiftedReindexedChart {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ)
    (U : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    EuclideanSpace ℝ (Fin (Fintype.card
      (Fin R × terminalHybridCoordinateIndex N))) →
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  fun x => A.terminalHybridEuclideanRightContraction N U
    (terminalHybridCoordinateReindex R N x)

/-- The unshifted reindexed right-translated chart is analytic everywhere. -/
theorem analyticAt_terminalHybridEuclideanRightUnshiftedReindexedChart {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ)
    (U : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (x : EuclideanSpace ℝ (Fin (Fintype.card
      (Fin R × terminalHybridCoordinateIndex N)))) :
    AnalyticAt ℝ (A.terminalHybridEuclideanRightUnshiftedReindexedChart N U) x := by
  change AnalyticAt ℝ
    (fun y => A.terminalHybridEuclideanRightContraction N U
      (terminalHybridCoordinateReindex R N y)) x
  exact AnalyticAt.comp
    (f := fun y => terminalHybridCoordinateReindex R N y)
    (g := A.terminalHybridEuclideanRightContraction N U)
    (A.analyticAt_terminalHybridEuclideanRightContraction N U
      (terminalHybridCoordinateReindex R N x))
    ((terminalHybridCoordinateReindex R N).analyticAt x)

end TwoQubitArchitecture

namespace BackwardsLightCone

/-- For every fixed right translate of the gate tuple, the locus where the
terminal-hybrid contraction has rank below the number of independent terminal
Pauli labels is Lebesgue-null. -/
theorem TerminalBlockPrefixAssembly.rightReindexedChart_lowRank_volume_zero
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
      assembly.flattenedGateParameters) :
    volume {x | Module.finrank ℝ
      (fderiv ℝ
        (assembly.flattenedArchitecture.terminalHybridEuclideanRightReindexedChart N U
          (assembly.terminalHybridCoordinateEmbedding N z 0)) x).range <
        labels.length} = 0 := by
  have hA : AnalyticOnNhd ℝ
      (assembly.flattenedArchitecture.terminalHybridEuclideanRightReindexedChart N U
        (assembly.terminalHybridCoordinateEmbedding N z 0)) Set.univ := by
    intro x _
    exact TwoQubitArchitecture.analyticAt_terminalHybridEuclideanRightReindexedChart
      assembly.flattenedArchitecture N U
      (assembly.terminalHybridCoordinateEmbedding N z 0) x
  have hLsurj : Function.Surjective
      (terminalHybridCoordinateReindex assembly.flattenedEdgeWord.length N) :=
    terminalHybridCoordinateReindex_surjective assembly.flattenedEdgeWord.length N
  have hbase : labels.length ≤ Module.finrank ℝ
      (fderiv ℝ
        (assembly.flattenedArchitecture.terminalHybridEuclideanRightContraction N U)
        (assembly.terminalHybridCoordinateEmbedding N z 0)).range := by
    exact assembly.finrank_range_ge_terminalHybridEuclideanRightContraction_fderiv
      hlabels N U z hz
  have hG : HasFDerivAt
      (assembly.flattenedArchitecture.terminalHybridEuclideanRightContraction N U)
      (fderiv ℝ
        (assembly.flattenedArchitecture.terminalHybridEuclideanRightContraction N U)
        (assembly.terminalHybridCoordinateEmbedding N z 0))
      (assembly.terminalHybridCoordinateEmbedding N z 0) :=
    (TwoQubitArchitecture.analyticAt_terminalHybridEuclideanRightContraction
      assembly.flattenedArchitecture N U
      (assembly.terminalHybridCoordinateEmbedding N z 0)).differentiableAt.hasFDerivAt
  have hL : HasFDerivAt
      (fun x => assembly.terminalHybridCoordinateEmbedding N z 0 +
        terminalHybridCoordinateReindex assembly.flattenedEdgeWord.length N x)
      (terminalHybridCoordinateReindex assembly.flattenedEdgeWord.length N) 0 :=
    (terminalHybridCoordinateReindex assembly.flattenedEdgeWord.length N).hasFDerivAt.const_add
      (assembly.terminalHybridCoordinateEmbedding N z 0)
  have hG0 : HasFDerivAt
      (assembly.flattenedArchitecture.terminalHybridEuclideanRightContraction N U)
      (fderiv ℝ
        (assembly.flattenedArchitecture.terminalHybridEuclideanRightContraction N U)
        (assembly.terminalHybridCoordinateEmbedding N z 0))
      (assembly.terminalHybridCoordinateEmbedding N z 0 +
        terminalHybridCoordinateReindex assembly.flattenedEdgeWord.length N 0) := by
    simpa only [map_zero, add_zero] using hG
  have hcomp := HasFDerivAt.comp
    (f := fun x => assembly.terminalHybridCoordinateEmbedding N z 0 +
      terminalHybridCoordinateReindex assembly.flattenedEdgeWord.length N x)
    (g := assembly.flattenedArchitecture.terminalHybridEuclideanRightContraction N U) 0 hG0 hL
  have hderiv : fderiv ℝ
      (assembly.flattenedArchitecture.terminalHybridEuclideanRightReindexedChart N U
        (assembly.terminalHybridCoordinateEmbedding N z 0)) 0 =
      (fderiv ℝ
        (assembly.flattenedArchitecture.terminalHybridEuclideanRightContraction N U)
        (assembly.terminalHybridCoordinateEmbedding N z 0)).comp
        (terminalHybridCoordinateReindex assembly.flattenedEdgeWord.length N) := by
    change fderiv ℝ
      (fun x => assembly.flattenedArchitecture.terminalHybridEuclideanRightContraction N U
        (assembly.terminalHybridCoordinateEmbedding N z 0 +
          terminalHybridCoordinateReindex assembly.flattenedEdgeWord.length N x)) 0 = _
    exact hcomp.fderiv
  have hrank : labels.length ≤ Module.finrank ℝ
      (fderiv ℝ
        (assembly.flattenedArchitecture.terminalHybridEuclideanRightReindexedChart N U
          (assembly.terminalHybridCoordinateEmbedding N z 0)) 0).range := by
    rw [hderiv]
    exact hbase.trans
      (finrank_range_comp_right_ge_of_surjective
        (terminalHybridCoordinateReindex assembly.flattenedEdgeWord.length N)
        (fderiv ℝ
          (assembly.flattenedArchitecture.terminalHybridEuclideanRightContraction N U)
          (assembly.terminalHybridCoordinateEmbedding N z 0)) hLsurj)
  exact analytic_lowRank_fderiv_volume_zero
    (assembly.flattenedArchitecture.terminalHybridEuclideanRightReindexedChart N U
      (assembly.terminalHybridCoordinateEmbedding N z 0)) hA hrank

/-- The unshifted finite Euclidean right-translated chart has a null locus
where its derivative rank falls below the independent terminal-label count. -/
theorem TerminalBlockPrefixAssembly.unshiftedReindexedChart_lowRank_volume_zero
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
      assembly.flattenedGateParameters) :
    volume {x | Module.finrank ℝ
      (fderiv ℝ
        (assembly.flattenedArchitecture.terminalHybridEuclideanRightUnshiftedReindexedChart N U)
        x).range < labels.length} = 0 := by
  let L := terminalHybridCoordinateReindex assembly.flattenedEdgeWord.length N
  let G := assembly.flattenedArchitecture.terminalHybridEuclideanRightContraction N U
  let F := assembly.flattenedArchitecture.terminalHybridEuclideanRightUnshiftedReindexedChart N U
  have hA : AnalyticOnNhd ℝ F Set.univ := by
    intro x _
    exact TwoQubitArchitecture.analyticAt_terminalHybridEuclideanRightUnshiftedReindexedChart
      assembly.flattenedArchitecture N U x
  have hLsurj : Function.Surjective L :=
    terminalHybridCoordinateReindex_surjective assembly.flattenedEdgeWord.length N
  obtain ⟨x0, hx0⟩ := hLsurj (assembly.terminalHybridCoordinateEmbedding N z 0)
  have hbase : labels.length ≤ Module.finrank ℝ
      (fderiv ℝ G (assembly.terminalHybridCoordinateEmbedding N z 0)).range := by
    exact assembly.finrank_range_ge_terminalHybridEuclideanRightContraction_fderiv
      hlabels N U z hz
  have hG : HasFDerivAt G
      (fderiv ℝ G (assembly.terminalHybridCoordinateEmbedding N z 0))
      (assembly.terminalHybridCoordinateEmbedding N z 0) :=
    (TwoQubitArchitecture.analyticAt_terminalHybridEuclideanRightContraction
      assembly.flattenedArchitecture N U
      (assembly.terminalHybridCoordinateEmbedding N z 0)).differentiableAt.hasFDerivAt
  have hGx0 : HasFDerivAt G
      (fderiv ℝ G (assembly.terminalHybridCoordinateEmbedding N z 0)) (L x0) := by
    rw [hx0]
    exact hG
  have hcomp := HasFDerivAt.comp (f := fun x => L x) (g := G) x0 hGx0 L.hasFDerivAt
  have hderiv : fderiv ℝ F x0 =
      (fderiv ℝ G (assembly.terminalHybridCoordinateEmbedding N z 0)).comp L := by
    change fderiv ℝ (G ∘ fun x => L x) x0 = _
    exact hcomp.fderiv
  have hrank : labels.length ≤ Module.finrank ℝ (fderiv ℝ F x0).range := by
    rw [hderiv]
    exact hbase.trans
      (finrank_range_comp_right_ge_of_surjective L
        (fderiv ℝ G (assembly.terminalHybridCoordinateEmbedding N z 0)) hLsurj)
  exact analytic_lowRank_fderiv_volume_zero_of_exists F hA ⟨x0, hrank⟩

/-- One terminal-hybrid word length provides a right-translation centre for
every finite gate tuple of the flattened architecture. -/
theorem TerminalBlockPrefixAssembly.exists_uniform_terminalHybridEuclidean_right_center
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels) :
    ∃ N : ℕ, ∀ U : Fin assembly.flattenedEdgeWord.length →
      Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
      ∃ z : Fin assembly.flattenedEdgeWord.length →
        boolTwoQubitHybridEuclideanCoordinates N,
        (fun r => boolTwoQubitHybridEuclideanGate N (z r) * U r) =
          assembly.flattenedGateParameters := by
  obtain ⟨N, hN⟩ := assembly.flattenedArchitecture.exists_uniform_hybridEuclideanGateAssignment
  refine ⟨N, ?_⟩
  intro U
  obtain ⟨z, hz⟩ := hN (fun r => assembly.flattenedGateParameters r * (U r)⁻¹)
  refine ⟨z, ?_⟩
  funext r
  have hzr := congrFun hz r
  change assembly.flattenedArchitecture.hybridEuclideanGateAssignment N z r * U r =
    assembly.flattenedGateParameters r
  rw [hzr]
  simp

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
