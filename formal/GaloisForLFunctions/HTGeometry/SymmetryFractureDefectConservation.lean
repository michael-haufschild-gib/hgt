import GaloisForLFunctions.HTGeometry.EventInvolutionComplement

/-!
# Unitary completion of an involution-selected event defect

Let `A` be a self-adjoint involution.  Its continuation and record projections split a unitary
matrix `U` into

* `symmetryPreservingPart A U = U * continuation`, and
* `symmetryTransmutingPart A U = U * record`.

This file proves that the two parts are orthogonal partial isometries which reconstruct `U`.  The
initial defect of the preserving part is exactly the source record projection, while its final
defect is exactly the final projection of the transmuting part.  A target reporter then gives a
canonical linear equivalence from the preserving-part cokernel to the source record range, and the
transmuting part realizes that equivalence.

These are unconditional finite-dimensional matrix identities.  They are standard unitary-defect
algebra.  The file does not assert that a physical event is unitary, that an involution is selected
by an exceptional pure pair, or that either defect space is spacetime.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Part of a complete map carried by the positive/continuation sector of the source involution. -/
def symmetryPreservingPart
    (A U : Matrix n n ℂ) : Matrix n n ℂ :=
  U * involutionContinuationProjection A

/-- Part of a complete map carried by the negative/record sector of the source involution. -/
def symmetryTransmutingPart
    (A U : Matrix n n ℂ) : Matrix n n ℂ :=
  U * involutionProjection A

omit [Fintype n] in
/-- A self-adjoint involution has a self-adjoint record projection. -/
theorem involutionProjection_conjTranspose
    (A : Matrix n n ℂ) (hAstar : A.conjTranspose = A) :
    (involutionProjection A).conjTranspose = involutionProjection A := by
  simp [involutionProjection, Matrix.conjTranspose_smul, hAstar]

/-- A self-adjoint involution has a self-adjoint continuation projection. -/
theorem involutionContinuationProjection_conjTranspose
    (A : Matrix n n ℂ) (hAstar : A.conjTranspose = A) :
    (involutionContinuationProjection A).conjTranspose =
      involutionContinuationProjection A := by
  simp [involutionContinuationProjection, Matrix.conjTranspose_smul, hAstar]

/-- Preserving and transmuting parts reconstruct the complete map. -/
theorem symmetryPreserving_add_transmuting
    (A U : Matrix n n ℂ) :
    symmetryPreservingPart A U + symmetryTransmutingPart A U = U := by
  simp only [symmetryPreservingPart, symmetryTransmutingPart, ← Matrix.mul_add,
    involutionContinuation_add_record A, mul_one]

/-- The preserving part has positive source-involution character. -/
theorem symmetryPreserving_mul_involution
    (A U : Matrix n n ℂ) (hA : A * A = 1) :
    symmetryPreservingPart A U * A = symmetryPreservingPart A U := by
  have hQA :
      involutionContinuationProjection A * A =
        involutionContinuationProjection A := by
    simp only [involutionContinuationProjection, Matrix.smul_mul, add_mul,
      one_mul, hA]
    module
  simp only [symmetryPreservingPart, Matrix.mul_assoc, hQA]

/-- The transmuting part has negative source-involution character. -/
theorem symmetryTransmuting_mul_involution
    (A U : Matrix n n ℂ) (hA : A * A = 1) :
    symmetryTransmutingPart A U * A = -symmetryTransmutingPart A U := by
  have hPA :
      involutionProjection A * A = -involutionProjection A := by
    simp only [involutionProjection, Matrix.smul_mul, sub_mul, one_mul, hA]
    module
  simp only [symmetryTransmutingPart, Matrix.mul_assoc, hPA, Matrix.mul_neg]

/-- The initial projection of the preserving part is the continuation projection. -/
theorem symmetryPreserving_adjoint_mul_self
    (A U : Matrix n n ℂ)
    (hA : A * A = 1) (hAstar : A.conjTranspose = A)
    (hU : U.conjTranspose * U = 1) :
    (symmetryPreservingPart A U).conjTranspose *
        symmetryPreservingPart A U =
      involutionContinuationProjection A := by
  rw [symmetryPreservingPart, Matrix.conjTranspose_mul,
    involutionContinuationProjection_conjTranspose A hAstar]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc _ U.conjTranspose U, hU, mul_one]
  exact involutionContinuation_isIdempotent A hA

/-- The initial projection of the transmuting part is the source record projection. -/
theorem symmetryTransmuting_adjoint_mul_self
    (A U : Matrix n n ℂ)
    (hA : A * A = 1) (hAstar : A.conjTranspose = A)
    (hU : U.conjTranspose * U = 1) :
    (symmetryTransmutingPart A U).conjTranspose *
        symmetryTransmutingPart A U =
      involutionProjection A := by
  rw [symmetryTransmutingPart, Matrix.conjTranspose_mul,
    involutionProjection_conjTranspose A hAstar]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc _ U.conjTranspose U, hU, mul_one]
  exact (involutionProjection_isIdempotent A hA).eq

/-- The preserving part is initially orthogonal to the transmuting part. -/
theorem symmetryPreserving_adjoint_mul_transmuting
    (A U : Matrix n n ℂ)
    (hA : A * A = 1) (hAstar : A.conjTranspose = A)
    (hU : U.conjTranspose * U = 1) :
    (symmetryPreservingPart A U).conjTranspose *
        symmetryTransmutingPart A U = 0 := by
  rw [symmetryPreservingPart, symmetryTransmutingPart, Matrix.conjTranspose_mul,
    involutionContinuationProjection_conjTranspose A hAstar]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc _ U.conjTranspose U, hU, mul_one]
  exact involutionContinuation_mul_record A hA

/-- The transmuting part is initially orthogonal to the preserving part. -/
theorem symmetryTransmuting_adjoint_mul_preserving
    (A U : Matrix n n ℂ)
    (hA : A * A = 1) (hAstar : A.conjTranspose = A)
    (hU : U.conjTranspose * U = 1) :
    (symmetryTransmutingPart A U).conjTranspose *
        symmetryPreservingPart A U = 0 := by
  rw [symmetryPreservingPart, symmetryTransmutingPart, Matrix.conjTranspose_mul,
    involutionProjection_conjTranspose A hAstar]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc _ U.conjTranspose U, hU, mul_one]
  exact involutionRecord_mul_continuation A hA

/-- The final projections of the two parts are complementary. -/
theorem symmetryPreserving_final_add_transmuting_final
    (A U : Matrix n n ℂ)
    (hA : A * A = 1) (hAstar : A.conjTranspose = A)
    (hU : U * U.conjTranspose = 1) :
    symmetryPreservingPart A U *
          (symmetryPreservingPart A U).conjTranspose +
        symmetryTransmutingPart A U *
          (symmetryTransmutingPart A U).conjTranspose = 1 := by
  rw [symmetryPreservingPart, symmetryTransmutingPart,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    involutionContinuationProjection_conjTranspose A hAstar,
    involutionProjection_conjTranspose A hAstar]
  calc
    U * involutionContinuationProjection A *
          (involutionContinuationProjection A * U.conjTranspose) +
        U * involutionProjection A *
          (involutionProjection A * U.conjTranspose) =
        U * (involutionContinuationProjection A *
            involutionContinuationProjection A +
          involutionProjection A * involutionProjection A) *
            U.conjTranspose := by noncomm_ring
    _ = U * (involutionContinuationProjection A +
          involutionProjection A) * U.conjTranspose := by
      rw [involutionContinuation_isIdempotent A hA,
        (involutionProjection_isIdempotent A hA).eq]
    _ = 1 := by rw [involutionContinuation_add_record A, mul_one, hU]

/-- Initial defect of the preserving part is exactly the transmuting initial projection. -/
theorem symmetryPreserving_initial_defect_eq_transmuting_initial
    (A U : Matrix n n ℂ)
    (hA : A * A = 1) (hAstar : A.conjTranspose = A)
    (hU : U.conjTranspose * U = 1) :
    1 - (symmetryPreservingPart A U).conjTranspose *
          symmetryPreservingPart A U =
      (symmetryTransmutingPart A U).conjTranspose *
        symmetryTransmutingPart A U := by
  rw [symmetryPreserving_adjoint_mul_self A U hA hAstar hU,
    symmetryTransmuting_adjoint_mul_self A U hA hAstar hU]
  have hsum := involutionContinuation_add_record A
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hsum.symm)

/-- Final defect of the preserving part is exactly the transmuting final projection. -/
theorem symmetryPreserving_final_defect_eq_transmuting_final
    (A U : Matrix n n ℂ)
    (hA : A * A = 1) (hAstar : A.conjTranspose = A)
    (hU : U * U.conjTranspose = 1) :
    1 - symmetryPreservingPart A U *
          (symmetryPreservingPart A U).conjTranspose =
      symmetryTransmutingPart A U *
        (symmetryTransmutingPart A U).conjTranspose := by
  have hsum :=
    symmetryPreserving_final_add_transmuting_final A U hA hAstar hU
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hsum.symm)

/-- Directions erased by the preserving part are exactly the source record directions. -/
theorem symmetryPreserving_ker_eq_record_range
    (A U : Matrix n n ℂ)
    (hA : A * A = 1)
    (hUleft : U.conjTranspose * U = 1) :
    LinearMap.ker (symmetryPreservingPart A U).toLin' =
      LinearMap.range (involutionProjection A).toLin' := by
  apply le_antisymm
  · intro x hx
    rw [← involutionContinuation_ker_eq_record_range A hA, LinearMap.mem_ker]
    rw [LinearMap.mem_ker] at hx
    change (symmetryPreservingPart A U).mulVec x = 0 at hx
    calc
      (involutionContinuationProjection A).mulVec x =
          (U.conjTranspose * symmetryPreservingPart A U).mulVec x := by
            rw [symmetryPreservingPart, ← Matrix.mul_assoc, hUleft, one_mul]
      _ = U.conjTranspose.mulVec
          ((symmetryPreservingPart A U).mulVec x) := by
            rw [Matrix.mulVec_mulVec]
      _ = 0 := by simp [hx]
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    change (symmetryPreservingPart A U).mulVec
      ((involutionProjection A).mulVec x) = 0
    rw [symmetryPreservingPart,
      ← Matrix.mulVec_mulVec ((involutionProjection A).mulVec x)
        U (involutionContinuationProjection A),
      Matrix.mulVec_mulVec x (involutionContinuationProjection A)
        (involutionProjection A),
      involutionContinuation_mul_record A hA, zero_mulVec]
    simp

/-- The target range of the transmuting part is the adjoint kernel of the preserving part. -/
theorem symmetryTransmuting_range_eq_preservingAdjoint_ker
    (A U : Matrix n n ℂ)
    (hA : A * A = 1) (hAstar : A.conjTranspose = A)
    (hUleft : U.conjTranspose * U = 1)
    (hUright : U * U.conjTranspose = 1) :
    LinearMap.range (symmetryTransmutingPart A U).toLin' =
      LinearMap.ker (symmetryPreservingPart A U).conjTranspose.toLin' := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, ← Matrix.toLin'_mul_apply,
      symmetryPreserving_adjoint_mul_transmuting A U hA hAstar
        hUleft]
    simp
  · intro y hy
    rw [LinearMap.mem_ker] at hy
    have hcontinuation :
        (involutionContinuationProjection A).mulVec
            (U.conjTranspose.mulVec y) = 0 := by
      change ((symmetryPreservingPart A U).conjTranspose).mulVec y = 0 at hy
      rw [symmetryPreservingPart, Matrix.conjTranspose_mul,
        involutionContinuationProjection_conjTranspose A hAstar] at hy
      rw [← Matrix.mulVec_mulVec y
        (involutionContinuationProjection A) U.conjTranspose] at hy
      exact hy
    have hrecord :
        (involutionProjection A).mulVec (U.conjTranspose.mulVec y) =
          U.conjTranspose.mulVec y := by
      have hsum :=
        involutionContinuation_add_record_apply A (U.conjTranspose.mulVec y)
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hcontinuation, zero_add] at hsum
      exact hsum
    refine ⟨U.conjTranspose.mulVec y, ?_⟩
    change (symmetryTransmutingPart A U).mulVec
      (U.conjTranspose.mulVec y) = y
    rw [symmetryTransmutingPart,
      ← Matrix.mulVec_mulVec (U.conjTranspose.mulVec y)
        U (involutionProjection A),
      hrecord,
      Matrix.mulVec_mulVec y U U.conjTranspose, hUright, one_mulVec]

/-- Target reporter whose kernel is the transmitted range and whose values are source records. -/
def symmetryCreatedReporter
    (A U : Matrix n n ℂ) :
    (n → ℂ) →ₗ[ℂ] LinearMap.range (involutionProjection A).toLin' :=
  ((involutionProjection A).toLin'.comp U.conjTranspose.toLin').codRestrict _
    fun x => ⟨U.conjTranspose.toLin' x, rfl⟩

/-- The target reporter reaches every source record direction for a left-unitary complete map. -/
theorem symmetryCreatedReporter_surjective
    (A U : Matrix n n ℂ)
    (hA : A * A = 1) (hUleft : U.conjTranspose * U = 1) :
    Function.Surjective (symmetryCreatedReporter A U) := by
  rintro ⟨y, ⟨x, hx⟩⟩
  refine ⟨U.toLin' y, Subtype.ext ?_⟩
  change (involutionProjection A).mulVec
      (U.conjTranspose.mulVec (U.mulVec y)) = y
  rw [Matrix.mulVec_mulVec y U.conjTranspose U, hUleft, one_mulVec]
  rw [← hx]
  simp only [Matrix.toLin'_apply]
  rw [Matrix.mulVec_mulVec x (involutionProjection A) (involutionProjection A),
    (involutionProjection_isIdempotent A hA).eq]

/-- The target reporter erases exactly the symmetry-preserving transmitted range. -/
theorem symmetryCreatedReporter_ker_eq_preserving_range
    (A U : Matrix n n ℂ)
    (hA : A * A = 1)
    (hUleft : U.conjTranspose * U = 1)
    (hUright : U * U.conjTranspose = 1) :
    LinearMap.ker (symmetryCreatedReporter A U) =
      LinearMap.range (symmetryPreservingPart A U).toLin' := by
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_ker] at hy
    have hrecord :
        (involutionProjection A).toLin'
            (U.conjTranspose.toLin' y) = 0 := by
      exact congrArg Subtype.val hy
    have hcontinuation :
        U.conjTranspose.toLin' y ∈
          LinearMap.range (involutionContinuationProjection A).toLin' := by
      rw [← involutionRecord_ker_eq_continuation_range A hA]
      exact hrecord
    rcases hcontinuation with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change (involutionContinuationProjection A).mulVec x =
      U.conjTranspose.mulVec y at hx
    rw [symmetryPreservingPart, Matrix.toLin'_apply,
      ← Matrix.mulVec_mulVec, hx,
      Matrix.mulVec_mulVec y U U.conjTranspose, hUright, one_mulVec]
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change (involutionProjection A).mulVec
        (U.conjTranspose.mulVec
          ((symmetryPreservingPart A U).mulVec x)) = 0
    rw [symmetryPreservingPart,
      ← Matrix.mulVec_mulVec x U (involutionContinuationProjection A),
      Matrix.mulVec_mulVec ((involutionContinuationProjection A).mulVec x)
        U.conjTranspose U,
      hUleft, one_mulVec,
      Matrix.mulVec_mulVec x (involutionProjection A)
        (involutionContinuationProjection A),
      involutionRecord_mul_continuation A hA, zero_mulVec]

/--
The cokernel of the symmetry-preserving part is canonically the source record range once the
complete two-sided unitary is supplied.
-/
noncomputable def symmetryPreservingCokernelEquivRecordRange
    (A U : Matrix n n ℂ)
    (hA : A * A = 1)
    (hUleft : U.conjTranspose * U = 1)
    (hUright : U * U.conjTranspose = 1) :
    ((n → ℂ) ⧸ LinearMap.range (symmetryPreservingPart A U).toLin') ≃ₗ[ℂ]
      LinearMap.range (involutionProjection A).toLin' :=
  (Submodule.quotEquivOfEq _ _
    (symmetryCreatedReporter_ker_eq_preserving_range
      A U hA hUleft hUright).symm).trans
    ((symmetryCreatedReporter A U).quotKerEquivOfSurjective
      (symmetryCreatedReporter_surjective A U hA hUleft))

/-- The cokernel equivalence sends a target class to its source record reporter. -/
@[simp]
theorem symmetryPreservingCokernelEquivRecordRange_mk
    (A U : Matrix n n ℂ)
    (hA : A * A = 1)
    (hUleft : U.conjTranspose * U = 1)
    (hUright : U * U.conjTranspose = 1)
    (y : n → ℂ) :
    symmetryPreservingCokernelEquivRecordRange A U hA hUleft hUright
        (Submodule.Quotient.mk y) =
      symmetryCreatedReporter A U y := by
  rfl

/-- The target reporter sends the transmuting part back to the source record projection. -/
theorem symmetryCreatedReporter_transmuting
    (A U : Matrix n n ℂ)
    (hA : A * A = 1) (hUleft : U.conjTranspose * U = 1)
    (x : n → ℂ) :
    symmetryCreatedReporter A U
        ((symmetryTransmutingPart A U).toLin' x) =
      involutionRecordToRange A x := by
  apply Subtype.ext
  change (involutionProjection A).mulVec
      (U.conjTranspose.mulVec
        ((symmetryTransmutingPart A U).mulVec x)) =
    (involutionProjection A).mulVec x
  rw [symmetryTransmutingPart,
    ← Matrix.mulVec_mulVec x U (involutionProjection A),
    Matrix.mulVec_mulVec ((involutionProjection A).mulVec x)
      U.conjTranspose U,
    hUleft, one_mulVec,
    Matrix.mulVec_mulVec x (involutionProjection A) (involutionProjection A),
    (involutionProjection_isIdempotent A hA).eq]

/--
The transmuting part realizes the canonical lost-record to preserving-cokernel equivalence.
-/
theorem symmetryPreservingCokernelEquivRecordRange_transmuting
    (A U : Matrix n n ℂ)
    (hA : A * A = 1)
    (hUleft : U.conjTranspose * U = 1)
    (hUright : U * U.conjTranspose = 1)
    (x : n → ℂ) :
    symmetryPreservingCokernelEquivRecordRange A U hA hUleft hUright
        (Submodule.Quotient.mk
          ((symmetryTransmutingPart A U).toLin' x)) =
      involutionRecordToRange A x := by
  rw [symmetryPreservingCokernelEquivRecordRange_mk,
    symmetryCreatedReporter_transmuting A U hA hUleft x]

end GaloisForLFunctions.HTGeometry
