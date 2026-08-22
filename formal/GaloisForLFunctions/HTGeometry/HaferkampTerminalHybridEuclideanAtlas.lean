import GaloisForLFunctions.HTGeometry.HaferkampHybridEuclideanArchitectureMeasure

/-!
# Terminal-phase augmented global hybrid coordinates

An extra literal Euclidean phase coordinate is placed before the globally
centred hybrid `SU(4)` chart.  At every word centre this exactly reproduces
the terminal `I ⊗ Z` phase path used by Appendix B, while a finite-sum index
avoids product-type normalization overhead.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance : DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance : Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

/-- One extra terminal-phase coordinate followed by the local hybrid index. -/
abbrev terminalHybridCoordinateIndex (N : ℕ) :=
  Unit ⊕ boolTwoQubitHybridCoordinateIndex N

/-- Literal finite Euclidean source for the terminal-phase augmented chart. -/
abbrev terminalHybridEuclideanCoordinates (N : ℕ) :=
  EuclideanSpace ℝ (terminalHybridCoordinateIndex N)

/-- Project the terminal phase coordinate. -/
def terminalHybridPhaseProjection (N : ℕ) :
    terminalHybridEuclideanCoordinates N →L[ℝ] ℝ :=
  (show terminalHybridEuclideanCoordinates N →ₗ[ℝ] ℝ from
    { toFun := fun z =>
        (EuclideanSpace.equiv (terminalHybridCoordinateIndex N) ℝ z)
          (Sum.inl Unit.unit)
      map_add' := by
        intro z w
        simp
      map_smul' := by
        intro c z
        simp }).toContinuousLinearMap

/-- Project the underlying globally centred hybrid coordinate. -/
def terminalHybridCoordinateProjection (N : ℕ) :
    terminalHybridEuclideanCoordinates N →L[ℝ]
      boolTwoQubitHybridEuclideanCoordinates N :=
  (show terminalHybridEuclideanCoordinates N →ₗ[ℝ]
      boolTwoQubitHybridEuclideanCoordinates N from
    { toFun := fun z =>
        (EuclideanSpace.equiv (boolTwoQubitHybridCoordinateIndex N) ℝ).symm
          (fun ij =>
            (EuclideanSpace.equiv (terminalHybridCoordinateIndex N) ℝ z)
              (Sum.inr ij))
      map_add' := by
        intro z w
        apply (EuclideanSpace.equiv (boolTwoQubitHybridCoordinateIndex N) ℝ).injective
        ext ij
        simp
      map_smul' := by
        intro c z
        apply (EuclideanSpace.equiv (boolTwoQubitHybridCoordinateIndex N) ℝ).injective
        ext ij
        simp }).toContinuousLinearMap

/-- Embed a terminal phase and an underlying hybrid coordinate into the one
finite Euclidean source. -/
def terminalHybridEuclideanEmbed (N : ℕ) (t : ℝ)
    (z : boolTwoQubitHybridEuclideanCoordinates N) :
    terminalHybridEuclideanCoordinates N :=
  (EuclideanSpace.equiv (terminalHybridCoordinateIndex N) ℝ).symm
    (fun ij => match ij with
      | Sum.inl _ => t
      | Sum.inr j =>
          (EuclideanSpace.equiv (boolTwoQubitHybridCoordinateIndex N) ℝ z) j)

@[simp] theorem terminalHybridPhaseProjection_embed (N : ℕ) (t : ℝ)
    (z : boolTwoQubitHybridEuclideanCoordinates N) :
    terminalHybridPhaseProjection N (terminalHybridEuclideanEmbed N t z) = t := by
  simp [terminalHybridPhaseProjection, terminalHybridEuclideanEmbed]

@[simp] theorem terminalHybridCoordinateProjection_embed (N : ℕ) (t : ℝ)
    (z : boolTwoQubitHybridEuclideanCoordinates N) :
    terminalHybridCoordinateProjection N (terminalHybridEuclideanEmbed N t z) = z := by
  apply (EuclideanSpace.equiv (boolTwoQubitHybridCoordinateIndex N) ℝ).injective
  ext ij
  simp [terminalHybridCoordinateProjection, terminalHybridEuclideanEmbed]

/-- Prepend a literal terminal `I ⊗ Z` phase to the globally centred local
hybrid chart. -/
def terminalHybridEuclideanGate (N : ℕ) :
    terminalHybridEuclideanCoordinates N →
      Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
  fun z => terminalPauliPhase (terminalHybridPhaseProjection N z) *
    boolTwoQubitHybridEuclideanGate N (terminalHybridCoordinateProjection N z)

/-- The terminal-phase augmented chart is real analytic everywhere. -/
theorem analyticAt_terminalHybridEuclideanGate_coe (N : ℕ)
    (z : terminalHybridEuclideanCoordinates N) :
    AnalyticAt ℝ (fun w =>
      (terminalHybridEuclideanGate N w :
        Matrix (Bool × Bool) (Bool × Bool) ℂ)) z := by
  have hphase : AnalyticAt ℝ
      (fun w : terminalHybridEuclideanCoordinates N =>
        terminalPauliPhaseMatrix (terminalHybridPhaseProjection N w)) z :=
    (analyticAt_terminalPauliPhaseMatrix_l2
      (terminalHybridPhaseProjection N z)).comp
        ((terminalHybridPhaseProjection N).analyticAt z)
  have hhybrid : AnalyticAt ℝ
      (fun w : terminalHybridEuclideanCoordinates N =>
        boolTwoQubitHybridEuclideanChart N
          (terminalHybridCoordinateProjection N w)) z :=
    (analyticAt_boolTwoQubitHybridEuclideanChart N
      (terminalHybridCoordinateProjection N z)).comp
        ((terminalHybridCoordinateProjection N).analyticAt z)
  change AnalyticAt ℝ
    (fun w => terminalPauliPhaseMatrix (terminalHybridPhaseProjection N w) *
      boolTwoQubitHybridEuclideanChart N
        (terminalHybridCoordinateProjection N w)) z
  exact hphase.mul hhybrid

/-- At every exponential-word centre, the added coordinate is exactly the
terminal phase path used in the Appendix-B witness. -/
theorem terminalHybridEuclideanGate_wordCenter
    (N : ℕ) (Y : boolTwoQubitEuclideanWordCoordinates N) (t : ℝ) :
    terminalHybridEuclideanGate N
      (terminalHybridEuclideanEmbed N t
        (boolTwoQubitHybridEuclideanEmbed N 0 Y)) =
      terminalPauliGatePath
        (specialUnitaryNormalize (false, false)
          (finiteUnitaryEuclideanExponentialWord (Bool × Bool) N Y)) t := by
  apply Subtype.ext
  simp only [terminalHybridEuclideanGate,
    terminalHybridPhaseProjection_embed,
    terminalHybridCoordinateProjection_embed]
  change (terminalPauliPhase t : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
      (boolNonidentityTwoQubitPauliHybridAtlas N 0 Y :
        Matrix (Bool × Bool) (Bool × Bool) ℂ) = _
  rw [boolNonidentityTwoQubitPauliHybridAtlas_zero]
  rfl

end

end GaloisForLFunctions.HTGeometry
