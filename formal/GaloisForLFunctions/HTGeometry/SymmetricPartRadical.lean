import GaloisForLFunctions.HTGeometry.SymmetricPartEsymmBridge
import GaloisForLFunctions.HTGeometry.SymmetricPartConstants

/-!
# The radical data over the symmetric part

The symmetric part and the intermediate field it defines have the same carrier, so an element of one
is an element of the other and a polynomial over one is a polynomial over the other.  The
irreducibility of the radical polynomial therefore holds verbatim over the symmetric part, which is
the field the generic polynomial is written over.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

variable {K : Type*} [Field K] {d : ℕ}

/-- The elementary symmetric function, read in the symmetric part. -/
noncomputable def esymmCoeffPart (K : Type*) [Field K] (d : ℕ) (i : Fin d) :
    symmetricPart K d :=
  esymmCoeffSymm K d i

/-- **The representative of the elementary symmetric function.** -/
theorem coe_esymmCoeffPart (i : Fin d) :
    ((esymmCoeffPart K d i : symmetricPart K d) : SymmetricRationalField K d) =
      esymmGen K d i := by
  show (((symmetricPartEquivEsymmField K d).symm (esymmCoeff K d i) :
    symmetricPartField K d) : SymmetricRationalField K d) = esymmGen K d i
  rw [coe_symmetricPartEquivEsymmField_symm]
  exact coe_esymmCoeff i

/-- **The radical polynomial over an elementary symmetric function is irreducible over the
symmetric part.** -/
theorem irreducible_X_pow_sub_C_esymmCoeffPart (i : Fin d) {n : ℕ} (hn : 0 < n) :
    Irreducible (Polynomial.X ^ n - Polynomial.C (esymmCoeffPart K d i) :
      Polynomial (symmetricPart K d)) :=
  irreducible_X_pow_sub_C_esymmCoeffSymm i hn

end GaloisForLFunctions.HTGeometry
