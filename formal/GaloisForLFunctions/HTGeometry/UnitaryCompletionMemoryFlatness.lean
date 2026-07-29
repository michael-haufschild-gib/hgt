import GaloisForLFunctions.HTGeometry.SymmetryFractureDefectConservation

/-!
# Fixed-carrier unitary completion memory is flat

Let a self-adjoint involution split a finite complex carrier into continuation and defect
projections. This file classifies two-sided unitary completions having the same continuation part.

Their relative completion memory is a two-sided unitary supported entirely on the defect block.
Relative memories satisfy a strict cocycle, so any triangular holonomy formed from globally supplied
completion matrices is the identity. Conversely, every two-sided defect gauge produces another
completion of the same visible event, and every such completion is obtained uniquely this way.

These are unconditional finite-dimensional matrix identities. They are standard
partial-isometry/unitary-completion and coboundary mathematics. No physical event, spacetime,
gravity, gauge force, connection, or global descent obstruction is constructed here.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Relative memory between two globally supplied unitary completion matrices. -/
def unitaryCompletionMemory (U V : Matrix n n ℂ) : Matrix n n ℂ :=
  U.conjTranspose * V

omit [DecidableEq n] in
/-- Adjoint of relative completion memory. -/
theorem unitaryCompletionMemory_conjTranspose
    (U V : Matrix n n ℂ) :
    (unitaryCompletionMemory U V).conjTranspose =
      V.conjTranspose * U := by
  simp [unitaryCompletionMemory, Matrix.conjTranspose_mul]

/-- Relative memory is left-unitary when its endpoints have the required unitary sides. -/
theorem unitaryCompletionMemory_leftUnitary
    (U V : Matrix n n ℂ)
    (hUright : U * U.conjTranspose = 1)
    (hVleft : V.conjTranspose * V = 1) :
    (unitaryCompletionMemory U V).conjTranspose *
        unitaryCompletionMemory U V = 1 := by
  rw [unitaryCompletionMemory_conjTranspose]
  simp only [unitaryCompletionMemory, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U U.conjTranspose V, hUright,
    one_mul, hVleft]

/-- Relative memory is right-unitary when its endpoints have the required unitary sides. -/
theorem unitaryCompletionMemory_rightUnitary
    (U V : Matrix n n ℂ)
    (hUleft : U.conjTranspose * U = 1)
    (hVright : V * V.conjTranspose = 1) :
    unitaryCompletionMemory U V *
        (unitaryCompletionMemory U V).conjTranspose = 1 := by
  rw [unitaryCompletionMemory_conjTranspose]
  simp only [unitaryCompletionMemory, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc V V.conjTranspose U, hVright,
    one_mul, hUleft]

/--
Completions with the same visible preserving part have relative memory fixing the continuation
projection on the right.
-/
theorem unitaryCompletionMemory_mul_continuation
    (A U V : Matrix n n ℂ)
    (hUleft : U.conjTranspose * U = 1)
    (hsame : symmetryPreservingPart A U =
      symmetryPreservingPart A V) :
    unitaryCompletionMemory U V *
        involutionContinuationProjection A =
      involutionContinuationProjection A := by
  unfold symmetryPreservingPart at hsame
  calc
    unitaryCompletionMemory U V * involutionContinuationProjection A =
        U.conjTranspose *
          (V * involutionContinuationProjection A) := by
            simp [unitaryCompletionMemory, Matrix.mul_assoc]
    _ = U.conjTranspose *
          (U * involutionContinuationProjection A) := by rw [hsame]
    _ = involutionContinuationProjection A := by
      rw [← Matrix.mul_assoc, hUleft, one_mul]

/--
Completions with the same visible preserving part have relative memory fixing the continuation
projection on the left.
-/
theorem continuation_mul_unitaryCompletionMemory
    (A U V : Matrix n n ℂ)
    (hAstar : A.conjTranspose = A)
    (hVleft : V.conjTranspose * V = 1)
    (hsame : symmetryPreservingPart A U =
      symmetryPreservingPart A V) :
    involutionContinuationProjection A *
        unitaryCompletionMemory U V =
      involutionContinuationProjection A := by
  have hsameStar :
      involutionContinuationProjection A * U.conjTranspose =
        involutionContinuationProjection A * V.conjTranspose := by
    have h := congrArg Matrix.conjTranspose hsame
    simpa [symmetryPreservingPart, Matrix.conjTranspose_mul,
      involutionContinuationProjection_conjTranspose A hAstar] using h
  calc
    involutionContinuationProjection A * unitaryCompletionMemory U V =
        (involutionContinuationProjection A * U.conjTranspose) * V := by
          simp [unitaryCompletionMemory, Matrix.mul_assoc]
    _ = (involutionContinuationProjection A * V.conjTranspose) * V := by
      rw [hsameStar]
    _ = involutionContinuationProjection A := by
      rw [Matrix.mul_assoc, hVleft, mul_one]

/--
The relative memory of two completions of one visible event is exactly identity on the continuation
sector plus one defect-supported block.
-/
theorem unitaryCompletionMemory_defect_block
    (A U V : Matrix n n ℂ)
    (hA : A * A = 1)
    (hAstar : A.conjTranspose = A)
    (hUleft : U.conjTranspose * U = 1)
    (hVleft : V.conjTranspose * V = 1)
    (hsame : symmetryPreservingPart A U =
      symmetryPreservingPart A V) :
    unitaryCompletionMemory U V =
      involutionContinuationProjection A +
        involutionProjection A * unitaryCompletionMemory U V *
          involutionProjection A := by
  have hright :=
    unitaryCompletionMemory_mul_continuation A U V hUleft hsame
  have hleft :=
    continuation_mul_unitaryCompletionMemory A U V hAstar hVleft hsame
  have hsum := involutionContinuation_add_record A
  have hPμQ :
      involutionProjection A * unitaryCompletionMemory U V *
          involutionContinuationProjection A = 0 := by
    rw [Matrix.mul_assoc, hright, involutionRecord_mul_continuation A hA]
  have hQμP :
      involutionContinuationProjection A * unitaryCompletionMemory U V *
          involutionProjection A = 0 := by
    rw [hleft, involutionContinuation_mul_record A hA]
  have hQμQ :
      involutionContinuationProjection A * unitaryCompletionMemory U V *
          involutionContinuationProjection A =
        involutionContinuationProjection A := by
    rw [hleft, involutionContinuation_isIdempotent A hA]
  calc
    unitaryCompletionMemory U V =
        (involutionContinuationProjection A + involutionProjection A) *
          unitaryCompletionMemory U V *
          (involutionContinuationProjection A + involutionProjection A) := by
            rw [hsum, one_mul, mul_one]
    _ = involutionContinuationProjection A +
          involutionProjection A * unitaryCompletionMemory U V *
            involutionProjection A := by
      rw [add_mul, add_mul, mul_add, mul_add]
      rw [hQμQ, hQμP, hPμQ]
      simp

/-- One completion and its relative memory reconstruct the other completion exactly. -/
theorem unitaryCompletionMemory_reconstruct
    (U V : Matrix n n ℂ)
    (hUright : U * U.conjTranspose = 1) :
    U * unitaryCompletionMemory U V = V := by
  simp [unitaryCompletionMemory, ← Matrix.mul_assoc, hUright]

/-- Relative completion memory changes only the transmuting part of the complete event. -/
theorem symmetryTransmutingPart_completionMemory
    (A U V : Matrix n n ℂ)
    (hA : A * A = 1)
    (hAstar : A.conjTranspose = A)
    (hUleft : U.conjTranspose * U = 1)
    (hUright : U * U.conjTranspose = 1)
    (hVleft : V.conjTranspose * V = 1)
    (hsame : symmetryPreservingPart A U =
      symmetryPreservingPart A V) :
    symmetryTransmutingPart A V =
      symmetryTransmutingPart A U * unitaryCompletionMemory U V := by
  have hblock :=
    unitaryCompletionMemory_defect_block A U V hA hAstar hUleft hVleft hsame
  have hreconstruct := unitaryCompletionMemory_reconstruct U V hUright
  have hcomm :
      unitaryCompletionMemory U V * involutionProjection A =
        involutionProjection A * unitaryCompletionMemory U V := by
    have hrightBlock :
        unitaryCompletionMemory U V * involutionProjection A =
          involutionProjection A * unitaryCompletionMemory U V *
            involutionProjection A := by
      calc
        unitaryCompletionMemory U V * involutionProjection A =
            (involutionContinuationProjection A +
                involutionProjection A * unitaryCompletionMemory U V *
                  involutionProjection A) *
              involutionProjection A :=
          congrArg (fun X => X * involutionProjection A) hblock
        _ = involutionProjection A * unitaryCompletionMemory U V *
              involutionProjection A := by
          simp [add_mul, involutionContinuation_mul_record A hA,
            Matrix.mul_assoc, (involutionProjection_isIdempotent A hA).eq]
    have hleftBlock :
        involutionProjection A * unitaryCompletionMemory U V =
          involutionProjection A * unitaryCompletionMemory U V *
            involutionProjection A := by
      calc
        involutionProjection A * unitaryCompletionMemory U V =
            involutionProjection A *
              (involutionContinuationProjection A +
                involutionProjection A * unitaryCompletionMemory U V *
                  involutionProjection A) :=
          congrArg (fun X => involutionProjection A * X) hblock
        _ = involutionProjection A * unitaryCompletionMemory U V *
              involutionProjection A := by
          simp [mul_add, involutionRecord_mul_continuation A hA,
            ← Matrix.mul_assoc,
            (involutionProjection_isIdempotent A hA).eq]
    exact hrightBlock.trans hleftBlock.symm
  unfold symmetryTransmutingPart
  calc
    V * involutionProjection A =
        U * unitaryCompletionMemory U V * involutionProjection A := by
          exact congrArg (fun X => X * involutionProjection A) hreconstruct.symm
    _ = U * (unitaryCompletionMemory U V * involutionProjection A) := by
      rw [Matrix.mul_assoc]
    _ = U * (involutionProjection A * unitaryCompletionMemory U V) := by
      rw [hcomm]
    _ = U * involutionProjection A * unitaryCompletionMemory U V := by
      rw [Matrix.mul_assoc]

/-- Globally supplied relative completion memories obey a strict cocycle law. -/
theorem unitaryCompletionMemory_cocycle
    (U V W : Matrix n n ℂ)
    (hVright : V * V.conjTranspose = 1) :
    unitaryCompletionMemory U V * unitaryCompletionMemory V W =
      unitaryCompletionMemory U W := by
  change (U.conjTranspose * V) * (V.conjTranspose * W) =
    U.conjTranspose * W
  calc
    (U.conjTranspose * V) * (V.conjTranspose * W) =
        U.conjTranspose * (V * (V.conjTranspose * W)) :=
      Matrix.mul_assoc _ _ _
    _ = U.conjTranspose * ((V * V.conjTranspose) * W) := by
      exact congrArg (fun X => U.conjTranspose * X)
        (Matrix.mul_assoc V V.conjTranspose W).symm
    _ = U.conjTranspose * W := by rw [hVright, one_mul]

/-- Every triangular holonomy of globally supplied unitary completion memories is identity. -/
theorem unitaryCompletionMemory_triangle
    (U V W : Matrix n n ℂ)
    (hUleft : U.conjTranspose * U = 1)
    (hVright : V * V.conjTranspose = 1)
    (hWright : W * W.conjTranspose = 1) :
    unitaryCompletionMemory U V *
        unitaryCompletionMemory V W *
        unitaryCompletionMemory W U = 1 := by
  rw [unitaryCompletionMemory_cocycle U V W hVright]
  change (U.conjTranspose * W) * (W.conjTranspose * U) = 1
  calc
    (U.conjTranspose * W) * (W.conjTranspose * U) =
        U.conjTranspose * (W * (W.conjTranspose * U)) :=
      Matrix.mul_assoc _ _ _
    _ = U.conjTranspose * ((W * W.conjTranspose) * U) := by
      exact congrArg (fun X => U.conjTranspose * X)
        (Matrix.mul_assoc W W.conjTranspose U).symm
    _ = 1 := by rw [hWright, one_mul, hUleft]

/--
Every two-sided unitary defect gauge produces a two-sided unitary completion of the same visible
event.
-/
theorem unitaryCompletion_same_visible_of_defectGauge
    (A U R : Matrix n n ℂ)
    (hUleft : U.conjTranspose * U = 1)
    (hUright : U * U.conjTranspose = 1)
    (hRleft : R.conjTranspose * R = 1)
    (hRright : R * R.conjTranspose = 1)
    (hRQ : R * involutionContinuationProjection A =
      involutionContinuationProjection A) :
    (U * R).conjTranspose * (U * R) = 1 ∧
      (U * R) * (U * R).conjTranspose = 1 ∧
      symmetryPreservingPart A (U * R) =
        symmetryPreservingPart A U := by
  constructor
  · rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U.conjTranspose U R,
      hUleft, one_mul, hRleft]
  constructor
  · rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R R.conjTranspose U.conjTranspose,
      hRright, one_mul, hUright]
  · simp [symmetryPreservingPart, Matrix.mul_assoc, hRQ]

/-- A relative completion memory is the unique defect gauge reconstructing its target completion. -/
theorem unitaryCompletionMemory_unique
    (U V R : Matrix n n ℂ)
    (hUleft : U.conjTranspose * U = 1)
    (hV : V = U * R) :
    R = unitaryCompletionMemory U V := by
  rw [hV]
  simp [unitaryCompletionMemory, ← Matrix.mul_assoc, hUleft]

/--
Exact completion-fiber classification: completions of one visible event are precisely right
translates by two-sided unitaries fixing the continuation projection on both sides.
-/
theorem unitaryCompletion_fiber_iff
    (A U V : Matrix n n ℂ)
    (hAstar : A.conjTranspose = A)
    (hUleft : U.conjTranspose * U = 1)
    (hUright : U * U.conjTranspose = 1) :
    (V.conjTranspose * V = 1 ∧
        V * V.conjTranspose = 1 ∧
        symmetryPreservingPart A U = symmetryPreservingPart A V) ↔
      ∃ R : Matrix n n ℂ,
        R.conjTranspose * R = 1 ∧
        R * R.conjTranspose = 1 ∧
        R * involutionContinuationProjection A =
          involutionContinuationProjection A ∧
        involutionContinuationProjection A * R =
          involutionContinuationProjection A ∧
        V = U * R := by
  constructor
  · rintro ⟨hVleft, hVright, hsame⟩
    refine ⟨unitaryCompletionMemory U V,
      unitaryCompletionMemory_leftUnitary U V hUright hVleft,
      unitaryCompletionMemory_rightUnitary U V hUleft hVright,
      unitaryCompletionMemory_mul_continuation A U V hUleft hsame,
      continuation_mul_unitaryCompletionMemory A U V hAstar hVleft hsame,
      (unitaryCompletionMemory_reconstruct U V hUright).symm⟩
  · rintro ⟨R, hRleft, hRright, hRQ, _hQR, rfl⟩
    have hcomplete :=
      unitaryCompletion_same_visible_of_defectGauge
        A U R hUleft hUright hRleft hRright hRQ
    exact ⟨hcomplete.1, hcomplete.2.1, hcomplete.2.2.symm⟩

end GaloisForLFunctions.HTGeometry
