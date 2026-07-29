import GaloisForLFunctions.HTGeometry.SourceOddPositivitySquareLaw
import GaloisForLFunctions.HTGeometry.SymmetryFractureDefectConservation

/-!
# A unitary source-event reciprocal square is only transported polarity

The reciprocal-square architecture becomes source-derived in the finite involution/unitary event
model. The canonical transmuting map is `D = U * P`, where `P` is the source record projection.
Its domain square is exactly `P`; its codomain square is exactly the record projection of the
unitarily transported target involution `U * A * Uᴴ`.

This is also a sharp no-go. Both positive squares are projections related by unitary conjugation,
so the finite unitary colligation creates no spectral weights or curvature. A physical
reciprocal-square law needs nontrivial source weights, non-unitary/open evolution, genuinely
category-changing composition, or another source-derived structure beyond a fixed-carrier unitary
completion.

All results here are unconditional finite matrix algebra and are not new mathematics.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

set_option maxRecDepth 4096

/-- Source involution transported to the target by a complete event matrix. -/
def transportedSourceInvolution
    {n : Type*} [Fintype n]
    (A U : Matrix n n ℂ) : Matrix n n ℂ :=
  U * A * Uᴴ

/-- Unitary transport preserves self-adjointness of the source involution. -/
theorem transportedSourceInvolution_conjTranspose
    {n : Type*} [Fintype n]
    (A U : Matrix n n ℂ)
    (hAH : Aᴴ = A) :
    (transportedSourceInvolution A U)ᴴ =
      transportedSourceInvolution A U := by
  simp [transportedSourceInvolution, Matrix.conjTranspose_mul, hAH, Matrix.mul_assoc]

/-- Two-sided unitary transport preserves the involution law. -/
theorem transportedSourceInvolution_mul_self
    {n : Type*} [Fintype n] [DecidableEq n]
    (A U : Matrix n n ℂ)
    (hA2 : A * A = 1)
    (hUleft : Uᴴ * U = 1)
    (hUright : U * Uᴴ = 1) :
    transportedSourceInvolution A U *
      transportedSourceInvolution A U = 1 := by
  simp only [transportedSourceInvolution]
  calc
    (U * A * Uᴴ) * (U * A * Uᴴ) =
        U * A * (Uᴴ * U) * A * Uᴴ := by noncomm_ring
    _ = U * A * A * Uᴴ := by rw [hUleft, Matrix.mul_one]
    _ = U * Uᴴ := by rw [Matrix.mul_assoc U A A, hA2, Matrix.mul_one]
    _ = 1 := hUright

/-- Record projection commutes with two-sided unitary transport of its involution. -/
theorem transportedSourceInvolution_recordProjection
    {n : Type*} [Fintype n] [DecidableEq n]
    (A U : Matrix n n ℂ)
    (hUright : U * Uᴴ = 1) :
    involutionProjection (transportedSourceInvolution A U) =
      U * involutionProjection A * Uᴴ := by
  simp only [transportedSourceInvolution, involutionProjection,
    Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, mul_one]
  rw [hUright]

/--
**Finite source-event reciprocal-square law.** The canonical transmuting part of a complete
unitary event has the source record and transported target record as its two reciprocal squares.
-/
theorem sourceEvent_reciprocalSquareLaw
    {n : Type*} [Fintype n] [DecidableEq n]
    (A U : Matrix n n ℂ)
    (hA2 : A * A = 1)
    (hAH : Aᴴ = A)
    (hUleft : Uᴴ * U = 1)
    (hUright : U * Uᴴ = 1) :
    reciprocalDomainSquare (symmetryTransmutingPart A U) =
        involutionProjection A ∧
      reciprocalCodomainSquare (symmetryTransmutingPart A U) =
        involutionProjection (transportedSourceInvolution A U) := by
  constructor
  · exact symmetryTransmuting_adjoint_mul_self A U hA2 hAH hUleft
  · rw [reciprocalCodomainSquare, symmetryTransmutingPart,
      Matrix.conjTranspose_mul, involutionProjection_conjTranspose A hAH]
    calc
      U * involutionProjection A *
          (involutionProjection A * Uᴴ) =
          U * (involutionProjection A * involutionProjection A) * Uᴴ := by
            noncomm_ring
      _ = U * involutionProjection A * Uᴴ := by
        rw [(involutionProjection_isIdempotent A hA2).eq]
      _ = involutionProjection (transportedSourceInvolution A U) := by
        rw [transportedSourceInvolution_recordProjection A U hUright]

/--
The source and target record projections have equal rank because they are the reciprocal squares
of one transmuting map.
-/
theorem sourceEvent_reciprocalSquare_rank_eq_record
    {n : Type*} [Fintype n] [DecidableEq n]
    (A U : Matrix n n ℂ)
    (hA2 : A * A = 1)
    (hAH : Aᴴ = A)
    (hUleft : Uᴴ * U = 1)
    (hUright : U * Uᴴ = 1) :
    (involutionProjection A).rank =
      (involutionProjection (transportedSourceInvolution A U)).rank := by
  have hsquares :=
    sourceEvent_reciprocalSquareLaw A U hA2 hAH hUleft hUright
  rw [← hsquares.1, ← hsquares.2]
  exact reciprocalSquare_rank_eq (symmetryTransmutingPart A U)

end GaloisForLFunctions.HTGeometry
