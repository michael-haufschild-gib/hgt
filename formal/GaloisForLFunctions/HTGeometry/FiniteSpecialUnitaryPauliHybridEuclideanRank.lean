import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryPauliHybridEuclideanAnalytic

/-!
# Rank transfer for joint Euclidean hybrid `SU(4)` coordinates

The fifteen-dimensional Pauli slice is an affine linear section of every
joint Euclidean hybrid chart.  Its exact rank therefore gives a rank-fifteen
witness for the full Euclidean chart at every exponential-word centre.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance finiteSpecialUnitaryPauliHybridEuclideanRankDecidableEqPauliLabel :
    DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance finiteSpecialUnitaryPauliHybridEuclideanRankFintypePauliLabel :
    Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

/-- Insert Pauli coordinates into the Pauli summand of the joint Euclidean source. -/
def boolTwoQubitHybridPauliInsertion (N : ℕ) :
    (boolNonidentityTwoQubitPauliLabel → ℝ) →L[ℝ]
      boolTwoQubitHybridEuclideanCoordinates N :=
  (show (boolNonidentityTwoQubitPauliLabel → ℝ) →ₗ[ℝ]
      boolTwoQubitHybridEuclideanCoordinates N from
    { toFun := fun x =>
        (EuclideanSpace.equiv (boolTwoQubitHybridCoordinateIndex N) ℝ).symm
          (fun ij => match ij with
            | Sum.inl i => x i
            | Sum.inr _ => 0)
      map_add' := by
        intro x y
        apply (EuclideanSpace.equiv (boolTwoQubitHybridCoordinateIndex N) ℝ).injective
        ext ij
        cases ij with
        | inl i => simp
        | inr p => simp
      map_smul' := by
        intro c x
        apply (EuclideanSpace.equiv (boolTwoQubitHybridCoordinateIndex N) ℝ).injective
        ext ij
        cases ij with
        | inl i => simp
        | inr p => simp }).toContinuousLinearMap

/-- Affine Pauli section through a fixed exponential-word coordinate. -/
def boolTwoQubitHybridPauliAffineEmbed (N : ℕ)
    (Y : boolTwoQubitEuclideanWordCoordinates N) :
    (boolNonidentityTwoQubitPauliLabel → ℝ) →
      boolTwoQubitHybridEuclideanCoordinates N :=
  fun x => boolTwoQubitHybridPauliInsertion N x +
    boolTwoQubitHybridEuclideanEmbed N 0 Y

/-- The affine section is the literal combined-coordinate embedding. -/
theorem boolTwoQubitHybridPauliAffineEmbed_eq_embed
    (N : ℕ) (Y : boolTwoQubitEuclideanWordCoordinates N)
    (x : boolNonidentityTwoQubitPauliLabel → ℝ) :
    boolTwoQubitHybridPauliAffineEmbed N Y x =
      boolTwoQubitHybridEuclideanEmbed N x Y := by
  apply (EuclideanSpace.equiv (boolTwoQubitHybridCoordinateIndex N) ℝ).injective
  ext ij
  cases ij with
  | inl i => simp [boolTwoQubitHybridPauliAffineEmbed,
      boolTwoQubitHybridPauliInsertion, boolTwoQubitHybridEuclideanEmbed]
  | inr p => simp [boolTwoQubitHybridPauliAffineEmbed,
      boolTwoQubitHybridPauliInsertion, boolTwoQubitHybridEuclideanEmbed]

/-- Restricting the joint chart to its affine Pauli section gives its fixed-word Pauli slice. -/
theorem boolTwoQubitHybridEuclideanChart_comp_pauliAffineEmbed
    (N : ℕ) (Y : boolTwoQubitEuclideanWordCoordinates N) :
    boolTwoQubitHybridEuclideanChart N ∘
      boolTwoQubitHybridPauliAffineEmbed N Y =
      boolNonidentityTwoQubitPauliHybridSlice N Y := by
  funext x
  change boolTwoQubitHybridEuclideanChart N
      (boolTwoQubitHybridPauliAffineEmbed N Y x) =
    boolNonidentityTwoQubitPauliHybridSlice N Y x
  rw [boolTwoQubitHybridPauliAffineEmbed_eq_embed]
  simp [boolTwoQubitHybridEuclideanChart,
    boolNonidentityTwoQubitPauliHybridSlice]

/-- The affine Pauli section has the evident constant derivative. -/
theorem hasFDerivAt_boolTwoQubitHybridPauliAffineEmbed
    (N : ℕ) (Y : boolTwoQubitEuclideanWordCoordinates N)
    (x : boolNonidentityTwoQubitPauliLabel → ℝ) :
    HasFDerivAt (boolTwoQubitHybridPauliAffineEmbed N Y)
      (boolTwoQubitHybridPauliInsertion N) x := by
  exact (boolTwoQubitHybridPauliInsertion N).hasFDerivAt.add_const _

/-- The full joint chart has derivative range dimension at least fifteen at every word centre. -/
theorem fifteen_le_finrank_range_fderiv_boolTwoQubitHybridEuclideanChart_at_embed
    (N : ℕ) (Y : boolTwoQubitEuclideanWordCoordinates N) :
    15 ≤ Module.finrank ℝ
      (fderiv ℝ (boolTwoQubitHybridEuclideanChart N)
        (boolTwoQubitHybridEuclideanEmbed N 0 Y)).range := by
  let E := boolTwoQubitHybridPauliAffineEmbed N Y
  let C := boolTwoQubitHybridEuclideanChart N
  let D : boolTwoQubitHybridEuclideanCoordinates N →L[ℝ]
      Matrix (Bool × Bool) (Bool × Bool) ℂ :=
    fderiv ℝ C (boolTwoQubitHybridEuclideanEmbed N 0 Y)
  have hEzero : E 0 = boolTwoQubitHybridEuclideanEmbed N 0 Y := by
    exact boolTwoQubitHybridPauliAffineEmbed_eq_embed N Y 0
  have hCbase : HasFDerivAt C D (boolTwoQubitHybridEuclideanEmbed N 0 Y) := by
    exact (analyticAt_boolTwoQubitHybridEuclideanChart N
      (boolTwoQubitHybridEuclideanEmbed N 0 Y)).differentiableAt.hasFDerivAt
  have hC : HasFDerivAt C D (E 0) := by
    rw [hEzero]
    exact hCbase
  have hE : HasFDerivAt E (boolTwoQubitHybridPauliInsertion N) 0 := by
    exact hasFDerivAt_boolTwoQubitHybridPauliAffineEmbed N Y 0
  have hcomp := HasFDerivAt.comp (f := E) (g := C) 0 hC hE
  have hs : C ∘ E = boolNonidentityTwoQubitPauliHybridSlice N Y := by
    exact boolTwoQubitHybridEuclideanChart_comp_pauliAffineEmbed N Y
  have hDcomp :
      fderiv ℝ (boolNonidentityTwoQubitPauliHybridSlice N Y) 0 =
        D.comp (boolTwoQubitHybridPauliInsertion N) := by
    rw [← hs]
    exact hcomp.fderiv
  have hslice : 15 ≤ Module.finrank ℝ
      (D.comp (boolTwoQubitHybridPauliInsertion N)).range := by
    rw [← hDcomp]
    exact le_of_eq
      (finrank_range_fderiv_boolNonidentityTwoQubitPauliHybridSlice_zero N Y).symm
  have hsub : (D.comp (boolTwoQubitHybridPauliInsertion N)).range ≤ D.range := by
    intro z hz
    rcases hz with ⟨x, rfl⟩
    exact ⟨boolTwoQubitHybridPauliInsertion N x, rfl⟩
  change 15 ≤ Module.finrank ℝ D.range
  exact hslice.trans (Submodule.finrank_mono hsub)

end

end GaloisForLFunctions.HTGeometry
