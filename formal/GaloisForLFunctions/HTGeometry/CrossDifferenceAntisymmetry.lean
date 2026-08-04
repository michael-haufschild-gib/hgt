import GaloisForLFunctions.HTGeometry.DifferentialLurothCoefficient

/-!
# The cross-difference is antisymmetric in its arguments

Exchanging the two polynomials of a projective cross-difference negates it, and a cross-difference of a
polynomial with itself vanishes.

The corpus records the antisymmetry of the two-copy *block swap*; this is the companion antisymmetry in
the arguments, which is what lets a reciprocity argument compare the two orderings of a coefficient
pair without re-deriving the definition each time.
-/

namespace GaloisForLFunctions

noncomputable section

variable {F : Type*} [CommRing F]

/-- **Exchanging the two entries negates the cross-difference.** -/
theorem differentialPolynomialCrossDifference_swap_args (P Q : DifferentialPolynomial Unit F) :
    differentialPolynomialCrossDifference Q P
      = - differentialPolynomialCrossDifference P Q := by
  rw [differentialPolynomialCrossDifference, differentialPolynomialCrossDifference]
  ring

/-- **A cross-difference of a polynomial with itself vanishes.** -/
@[simp]
theorem differentialPolynomialCrossDifference_self (P : DifferentialPolynomial Unit F) :
    differentialPolynomialCrossDifference P P = 0 := by
  rw [differentialPolynomialCrossDifference]
  ring

/-- **Reciprocity.**  The block swap and the argument swap agree on the cross-difference: swapping the
two copies is the same as exchanging the two entries. -/
theorem differentialPolynomialTwoBlockSwap_crossDifference_eq_swap_args
    (P Q : DifferentialPolynomial Unit F) :
    differentialPolynomialTwoBlockSwap F (differentialPolynomialCrossDifference P Q)
      = differentialPolynomialCrossDifference Q P := by
  rw [differentialPolynomialTwoBlockSwap_crossDifference,
    differentialPolynomialCrossDifference_swap_args, neg_neg]

end

end GaloisForLFunctions
