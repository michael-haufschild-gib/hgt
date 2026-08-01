import GaloisForLFunctions.HTGeometry.SymmetricPartEsymmBridge
import GaloisForLFunctions.HTGeometry.SymmetricPartConstants

/-!
# The radical data over the symmetric part

The symmetric part and the intermediate field it defines have the same carrier, so an element of one
is an element of the other and a polynomial over one is a polynomial over the other.  The
irreducibility of the radical polynomial and the degree of a root therefore hold verbatim over the
symmetric part, which is the field the generic polynomial is written over.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {K : Type*} [Field K] {d : ℕ}

/-- The elementary symmetric function, read in the symmetric part. -/
noncomputable def esymmCoeffPart (K : Type*) [Field K] (d : ℕ) (i : Fin d) :
    symmetricPart K d :=
  esymmCoeffSymm K d i

/-- **The radical polynomial over an elementary symmetric function is irreducible over the
symmetric part.** -/
theorem irreducible_X_pow_sub_C_esymmCoeffPart (i : Fin d) {n : ℕ} (hn : 0 < n) :
    Irreducible (Polynomial.X ^ n - Polynomial.C (esymmCoeffPart K d i) :
      Polynomial (symmetricPart K d)) :=
  irreducible_X_pow_sub_C_esymmCoeffSymm i hn

/-- **A root generates an extension of exactly that degree over the symmetric part.** -/
theorem finrank_adjoin_esymmCoeffPart_root {L : Type*} [Field L]
    [Algebra (symmetricPart K d) L] (i : Fin d) {n : ℕ} (hn : 0 < n) {α : L}
    (hα : α ^ n = algebraMap (symmetricPart K d) L (esymmCoeffPart K d i)) :
    Module.finrank (symmetricPart K d)
      (IntermediateField.adjoin (symmetricPart K d) {α}) = n :=
  finrank_adjoin_of_irreducible hn (irreducible_X_pow_sub_C_esymmCoeffPart i hn) hα

end GaloisForLFunctions.HTGeometry
