import GaloisForLFunctions.HTGeometry.ConstraintIdealExcursion

/-!
# Reducing code subspaces and one-sided leakage discharge

Quantum error correction and decoherence-free subspace arguments separate a Hilbert space with a
code projector `P`.  Off-diagonal blocks then describe leakage out of the code and return from its
orthogonal complement.  Adjointness makes these two blocks paired rather than independent.

This file turns that observation into hypothesis-discharge lemmas for the existing constraint
excursion API.  For a self-adjoint compression `P`, no departure through an arbitrary operator `A`
is exactly no return through `A†`.  If `A` is itself self-adjoint and `P` is idempotent, the same
condition is equivalent to `P` commuting with `A`: an invariant code is automatically reducing.

The direct consumer is a Kraus-style sandwich.  A single no-departure condition kills
`P * (A† * C * A) * P`; when `C` is self-adjoint, only one of `P*C=0` and `C*P=0` must be supplied.
These are static subspace relations, not temporal propagation statements.
-/

namespace HTGeometry

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **Adjoint leakage pairing.**  For a self-adjoint compression, departure from the code through
`A` is equivalent to return through the adjoint channel `A†`. -/
theorem selfAdjointCompression_noDeparture_iff_adjoint_noReturn
    (P A : E →L[𝕜] E) (hP : IsSelfAdjoint P) :
    (1 - P) * A * P = 0 ↔ P * A.adjoint * (1 - P) = 0 := by
  have hPadj : P.adjoint = P := by
    simpa [ContinuousLinearMap.star_eq_adjoint] using hP.star_eq
  constructor <;> intro h
  · have hadj := congrArg ContinuousLinearMap.adjoint h
    simpa [ContinuousLinearMap.mul_def, hPadj] using hadj
  · have hadj := congrArg ContinuousLinearMap.adjoint h
    simpa [ContinuousLinearMap.mul_def, hPadj] using hadj

/-- For a self-adjoint observable, no departure and no return are the same condition. -/
theorem selfAdjointCompression_noDeparture_iff_noReturn
    (P A : E →L[𝕜] E) (hP : IsSelfAdjoint P) (hA : IsSelfAdjoint A) :
    (1 - P) * A * P = 0 ↔ P * A * (1 - P) = 0 := by
  constructor <;> intro h
  · have hadj := congrArg star h
    simpa [hP.star_eq, hA.star_eq] using hadj
  · have hadj := congrArg star h
    simpa [hP.star_eq, hA.star_eq] using hadj

/-- Left and right annihilation of a self-adjoint constraint by a self-adjoint compression are
equivalent.  A consumer need not supply both hypotheses. -/
theorem selfAdjointCompression_mul_eq_zero_iff_mul_selfAdjoint
    (P C : E →L[𝕜] E) (hP : IsSelfAdjoint P) (hC : IsSelfAdjoint C) :
    P * C = 0 ↔ C * P = 0 := by
  have hPadj : P.adjoint = P := by
    simpa [ContinuousLinearMap.star_eq_adjoint] using hP.star_eq
  have hCadj : C.adjoint = C := by
    simpa [ContinuousLinearMap.star_eq_adjoint] using hC.star_eq
  constructor <;> intro h
  · have hadj := congrArg ContinuousLinearMap.adjoint h
    simpa [ContinuousLinearMap.mul_def, hPadj, hCadj] using hadj
  · have hadj := congrArg ContinuousLinearMap.adjoint h
    simpa [ContinuousLinearMap.mul_def, hPadj, hCadj] using hadj

/-- **Invariant implies reducing.**  For an orthogonal projection and a self-adjoint operator,
one-sided invariance is equivalent to commutation with the projection. -/
theorem orthogonalProjection_noDeparture_iff_commutes_selfAdjoint
    (P A : E →L[𝕜] E) (hP2 : P * P = P)
    (hP : IsSelfAdjoint P) (hA : IsSelfAdjoint A) :
    (1 - P) * A * P = 0 ↔ P * A = A * P := by
  rw [selfAdjointCompression_noDeparture_iff_noReturn P A hP hA]
  constructor
  · intro hreturn
    have hdepart : (1 - P) * A * P = 0 :=
      (selfAdjointCompression_noDeparture_iff_noReturn P A hP hA).mpr hreturn
    calc
      P * A = P * A * P + P * A * (1 - P) := by noncomm_ring
      _ = P * A * P := by rw [hreturn]; simp
      _ = (1 - P) * A * P + P * A * P := by rw [hdepart]; simp
      _ = A * P := by noncomm_ring
  · intro hcomm
    noncomm_ring [hcomm, hP2]

/-- **One-sided leakage discharge for constraint sandwiches.**  If `A` does not take code vectors
into the complementary sector, adjointness supplies the no-return hypothesis needed by the
general constraint-excursion theorem. -/
theorem constraintAdjointSandwich_compression_eq_zero_of_noDeparture
    (P C A : E →L[𝕜] E) (hP : IsSelfAdjoint P)
    (hPC : P * C = 0) (hCP : C * P = 0)
    (hpreserve : (1 - P) * A * P = 0) :
    P * (A.adjoint * C * A) * P = 0 := by
  exact constraintSandwich_compression_eq_zero_of_noReturn
    P C A.adjoint A hPC hCP
      ((selfAdjointCompression_noDeparture_iff_adjoint_noReturn P A hP).mp hpreserve)

/-- **Self-adjoint constraint discharge.**  For a self-adjoint constraint, one annihilation
condition and one no-departure condition suffice to erase the full adjoint sandwich.  The missing
right-annihilation and no-return premises are consequences, not assumptions. -/
theorem selfAdjointConstraint_adjointSandwich_compression_eq_zero_of_noDeparture
    (P C A : E →L[𝕜] E)
    (hP : IsSelfAdjoint P) (hC : IsSelfAdjoint C)
    (hPC : P * C = 0) (hpreserve : (1 - P) * A * P = 0) :
    P * (A.adjoint * C * A) * P = 0 := by
  exact constraintAdjointSandwich_compression_eq_zero_of_noDeparture
    P C A hP hPC
      ((selfAdjointCompression_mul_eq_zero_iff_mul_selfAdjoint P C hP hC).mp hPC)
      hpreserve

end

end HTGeometry
