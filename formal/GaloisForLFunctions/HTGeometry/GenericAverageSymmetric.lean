import GaloisForLFunctions.HTGeometry.CenteredIsTaylorShift
import GaloisForLFunctions.HTGeometry.GenericPolynomialSplitting

/-!
# The average of the roots is symmetric, and shifts commute with base change

Permuting the roots does not change their average, so the average lies in the symmetric part.  And
a ring homomorphism carries a Taylor shift to the Taylor shift by the image of the amount.

So the shift that centers the generic polynomial can be performed over the coefficient field, and
reading the result in the rational function field gives the centered polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

omit [CharZero K] in
/-- **The average of the generic roots is symmetric.** -/
theorem genericAverage_mem_symmetricPart :
    genericAverage K d ∈ symmetricPart K d := fun e => smul_genericAverage e

/-- **A ring homomorphism carries a shift to a shift.** -/
theorem map_taylor' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R)
    (p : Polynomial R) :
    Polynomial.map f (Polynomial.taylor r p) =
      Polynomial.taylor (f r) (Polynomial.map f p) := by
  rw [Polynomial.taylor_apply, Polynomial.taylor_apply, Polynomial.map_comp,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]

/-- The average of the roots, as an element of the symmetric part. -/
noncomputable def genericAverageIn (K : Type*) [Field K] [CharZero K] (d : ℕ) :
    symmetricPart K d :=
  ⟨genericAverage K d, genericAverage_mem_symmetricPart⟩

/-- The centered polynomial, written over the coefficient field. -/
noncomputable def centeredMonicPart (K : Type*) [Field K] [CharZero K] (d : ℕ) :
    Polynomial (symmetricPart K d) :=
  Polynomial.taylor (genericAverageIn K d) (genericMonic K d)

/-- **Its image in the rational function field is the centered polynomial.** -/
theorem map_centeredMonicPart :
    Polynomial.map (algebraMap (symmetricPart K d) (SymmetricRationalField K d))
      (centeredMonicPart K d) = centeredMonicF K d := by
  rw [centeredMonicPart, map_taylor', map_genericMonic]
  exact taylor_genericMonicF

/-- **Shifting back recovers the generic polynomial.**  So its coefficients are expressions in the
average and the centered coefficients, and the two coefficient systems determine each other. -/
theorem taylor_neg_centeredMonicPart :
    Polynomial.taylor (-genericAverageIn K d) (centeredMonicPart K d) = genericMonic K d := by
  rw [centeredMonicPart, Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero]

end GaloisForLFunctions.HTGeometry
