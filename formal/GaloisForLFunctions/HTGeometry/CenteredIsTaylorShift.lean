import GaloisForLFunctions.HTGeometry.CenteredGenericPolynomial
import GaloisForLFunctions.HTGeometry.TaylorRoots

/-!
# The centered polynomial is a shift of the generic one

Centering the roots is translating them all by their average, and translating the roots of a monic
polynomial is shifting its variable.  So the centered generic polynomial is the Taylor shift of the
generic polynomial by the average of the roots.

Since a shift by a base-field element leaves the field the roots generate untouched, the two
polynomials have the same splitting field and the same Galois group.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

omit [CharZero K] in
/-- **The centered polynomial is the shift of the generic one by the average of the roots.** -/
theorem taylor_genericMonicF :
    Polynomial.taylor (genericAverage K d) (genericMonicF K d) = centeredMonicF K d := by
  rw [Polynomial.taylor_apply, genericMonicF, centeredMonicF, Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, centeredRoot, map_sub]
  ring

end GaloisForLFunctions.HTGeometry
