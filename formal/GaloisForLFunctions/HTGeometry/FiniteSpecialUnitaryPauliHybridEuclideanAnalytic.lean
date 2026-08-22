import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryPauliHybridL2Analytic

/-!
# Joint Euclidean analytic coordinates for the hybrid `SU(4)` atlas

The Pauli and normalized exponential-word coordinates are flattened into one
literal finite Euclidean space.  This avoids expensive product-instance
normalization while giving a single globally centred real-analytic chart
family, suitable for Euclidean analytic null-set transfer.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance finiteSpecialUnitaryPauliHybridEuclideanAnalyticDecidableEqPauliLabel :
    DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance finiteSpecialUnitaryPauliHybridEuclideanAnalyticFintypePauliLabel :
    Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

/-- Index set for one Euclidean exponential-word coefficient. -/
abbrev boolTwoQubitWordCoordinateIndex (N : ℕ) :=
  Fin N × Fin (Module.finrank ℝ (selfAdjoint (Matrix (Bool × Bool) (Bool × Bool) ℂ)))

/-- Joint finite coordinate index: fifteen Pauli entries and all word entries. -/
abbrev boolTwoQubitHybridCoordinateIndex (N : ℕ) :=
  boolNonidentityTwoQubitPauliLabel ⊕ boolTwoQubitWordCoordinateIndex N

/-- Literal finite Euclidean source of a hybrid Pauli/exponential chart. -/
abbrev boolTwoQubitHybridEuclideanCoordinates (N : ℕ) :=
  EuclideanSpace ℝ (boolTwoQubitHybridCoordinateIndex N)

/-- Projection of joint Euclidean coordinates onto the fifteen Pauli coordinates. -/
def boolTwoQubitHybridPauliProjection (N : ℕ) :
    boolTwoQubitHybridEuclideanCoordinates N →L[ℝ]
      (boolNonidentityTwoQubitPauliLabel → ℝ) :=
  (show boolTwoQubitHybridEuclideanCoordinates N →ₗ[ℝ]
      (boolNonidentityTwoQubitPauliLabel → ℝ) from
    { toFun := fun z i => (EuclideanSpace.equiv (boolTwoQubitHybridCoordinateIndex N) ℝ z)
        (Sum.inl i)
      map_add' := by
        intro z w
        ext i
        simp
      map_smul' := by
        intro c z
        ext i
        simp }).toContinuousLinearMap

/-- Projection of joint Euclidean coordinates onto ordered exponential-word coordinates. -/
def boolTwoQubitHybridWordProjection (N : ℕ) :
    boolTwoQubitHybridEuclideanCoordinates N →L[ℝ]
      boolTwoQubitEuclideanWordCoordinates N :=
  (show boolTwoQubitHybridEuclideanCoordinates N →ₗ[ℝ]
      boolTwoQubitEuclideanWordCoordinates N from
    { toFun := fun z i j => (EuclideanSpace.equiv (boolTwoQubitHybridCoordinateIndex N) ℝ z)
        (Sum.inr (i, j))
      map_add' := by
        intro z w
        ext i j
        simp
      map_smul' := by
        intro c z
        ext i j
        simp }).toContinuousLinearMap

/-- The hybrid atlas as a map from one finite Euclidean coordinate space. -/
def boolTwoQubitHybridEuclideanChart (N : ℕ) :
    boolTwoQubitHybridEuclideanCoordinates N →
      Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun z => boolNonidentityTwoQubitPauliHybridAtlas N
    (boolTwoQubitHybridPauliProjection N z)
    (boolTwoQubitHybridWordProjection N z)

/-- Embed a prescribed Pauli coordinate and exponential word into the joint Euclidean source. -/
def boolTwoQubitHybridEuclideanEmbed (N : ℕ)
    (x : boolNonidentityTwoQubitPauliLabel → ℝ)
    (Y : boolTwoQubitEuclideanWordCoordinates N) :
    boolTwoQubitHybridEuclideanCoordinates N :=
  (EuclideanSpace.equiv (boolTwoQubitHybridCoordinateIndex N) ℝ).symm
    (fun ij => match ij with
      | Sum.inl i => x i
      | Sum.inr p => Y p.1 p.2)

@[simp] theorem boolTwoQubitHybridPauliProjection_embed
    (N : ℕ) (x : boolNonidentityTwoQubitPauliLabel → ℝ)
    (Y : boolTwoQubitEuclideanWordCoordinates N) :
    boolTwoQubitHybridPauliProjection N
      (boolTwoQubitHybridEuclideanEmbed N x Y) = x := by
  ext i
  simp [boolTwoQubitHybridPauliProjection, boolTwoQubitHybridEuclideanEmbed]

@[simp] theorem boolTwoQubitHybridWordProjection_embed
    (N : ℕ) (x : boolNonidentityTwoQubitPauliLabel → ℝ)
    (Y : boolTwoQubitEuclideanWordCoordinates N) :
    boolTwoQubitHybridWordProjection N
      (boolTwoQubitHybridEuclideanEmbed N x Y) = Y := by
  ext i j
  simp [boolTwoQubitHybridWordProjection, boolTwoQubitHybridEuclideanEmbed]

/-- The joint Euclidean hybrid chart is real analytic everywhere. -/
theorem analyticAt_boolTwoQubitHybridEuclideanChart
    (N : ℕ) (z : boolTwoQubitHybridEuclideanCoordinates N) :
    AnalyticAt ℝ (boolTwoQubitHybridEuclideanChart N) z := by
  let X := boolTwoQubitHybridPauliProjection N z
  let Y := boolTwoQubitHybridWordProjection N z
  have hpauli : AnalyticAt ℝ
      (fun w : boolTwoQubitHybridEuclideanCoordinates N =>
        boolNonidentityTwoQubitPauliCoordinateChart
          (boolTwoQubitHybridPauliProjection N w)) z :=
    (analyticAt_boolNonidentityTwoQubitPauliCoordinateChart_l2 X).comp
      ((boolTwoQubitHybridPauliProjection N).analyticAt z)
  have hword : AnalyticAt ℝ
      (fun w : boolTwoQubitHybridEuclideanCoordinates N =>
        (specialUnitaryNormalize (false, false)
          (finiteUnitaryEuclideanExponentialWord (Bool × Bool) N
            (boolTwoQubitHybridWordProjection N w)) :
          Matrix (Bool × Bool) (Bool × Bool) ℂ)) z :=
    AnalyticAt.comp
      (f := fun w : boolTwoQubitHybridEuclideanCoordinates N =>
        boolTwoQubitHybridWordProjection N w)
      (g := fun Z : boolTwoQubitEuclideanWordCoordinates N =>
        (specialUnitaryNormalize (false, false)
          (finiteUnitaryEuclideanExponentialWord (Bool × Bool) N Z) :
          Matrix (Bool × Bool) (Bool × Bool) ℂ))
      (analyticAt_finiteSpecialUnitaryNormalizedEuclideanExponentialWord_coe
        (i0 := (false, false)) N Y)
      ((boolTwoQubitHybridWordProjection N).analyticAt z)
  have h := hpauli.mul hword
  change AnalyticAt ℝ
    (fun w => boolNonidentityTwoQubitPauliCoordinateChart
      (boolTwoQubitHybridPauliProjection N w) *
      (specialUnitaryNormalize (false, false)
        (finiteUnitaryEuclideanExponentialWord (Bool × Bool) N
          (boolTwoQubitHybridWordProjection N w)) :
        Matrix (Bool × Bool) (Bool × Bool) ℂ)) z at h
  rw [show boolTwoQubitHybridEuclideanChart N = fun w =>
      boolNonidentityTwoQubitPauliCoordinateChart
        (boolTwoQubitHybridPauliProjection N w) *
      (specialUnitaryNormalize (false, false)
        (finiteUnitaryEuclideanExponentialWord (Bool × Bool) N
          (boolTwoQubitHybridWordProjection N w)) :
        Matrix (Bool × Bool) (Bool × Bool) ℂ) by
        funext w
        simpa [boolTwoQubitHybridEuclideanChart,
          boolNonidentityTwoQubitPauliCoordinateGate_coe] using
          congrArg (fun R : Matrix.specialUnitaryGroup (Bool × Bool) ℂ =>
            (R : Matrix (Bool × Bool) (Bool × Bool) ℂ))
            (boolNonidentityTwoQubitPauliHybridAtlas_eq N
              (boolTwoQubitHybridPauliProjection N w)
              (boolTwoQubitHybridWordProjection N w))]
  exact h

/-- One fixed joint Euclidean chart family is analytic and globally centred on finite `SU(4)`. -/
theorem exists_uniform_boolTwoQubitHybridEuclideanChart_l2 :
    ∃ N : ℕ, ∀ S : Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
      ∃ z : boolTwoQubitHybridEuclideanCoordinates N,
        boolTwoQubitHybridEuclideanChart N z =
          (S : Matrix (Bool × Bool) (Bool × Bool) ℂ) ∧
        AnalyticAt ℝ (boolTwoQubitHybridEuclideanChart N) z := by
  obtain ⟨N, hN⟩ := exists_boolNonidentityTwoQubitPauliHybridAtlas_center
  refine ⟨N, fun S => ?_⟩
  obtain ⟨Y, hY⟩ := hN S
  refine ⟨boolTwoQubitHybridEuclideanEmbed N 0 Y, ?_,
    analyticAt_boolTwoQubitHybridEuclideanChart N
      (boolTwoQubitHybridEuclideanEmbed N 0 Y)⟩
  simpa [boolTwoQubitHybridEuclideanChart] using
    congrArg (fun V : Matrix.specialUnitaryGroup (Bool × Bool) ℂ =>
      (V : Matrix (Bool × Bool) (Bool × Bool) ℂ)) hY

end

end GaloisForLFunctions.HTGeometry
