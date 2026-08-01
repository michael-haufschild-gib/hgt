import GaloisForLFunctions.HTGeometry.EsymmFieldEquiv
import GaloisForLFunctions.HTGeometry.IrreducibleRadicalTransport
import GaloisForLFunctions.HTGeometry.EisensteinRadical
import GaloisForLFunctions.HTGeometry.RadicalDegreeExact

/-!
# The radical polynomial over an elementary symmetric function is irreducible

Under the identification of the coefficient field with a rational function field, an elementary
symmetric function is a variable, hence prime.  A radical polynomial over a prime is irreducible at
every exponent, and irreducibility transports back along the identification.

So a root of it generates an extension of the coefficient field of exactly that degree, which is the
degree input of the base change step.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {K : Type*} [Field K] {d : ℕ}

/-- The elementary symmetric function as an element of the coefficient field. -/
noncomputable def esymmCoeff (K : Type*) [Field K] (d : ℕ) (i : Fin d) : esymmField K d :=
  esymmFieldEquiv K d
    (algebraMap (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K))
      (MvPolynomial.X i))

theorem coe_esymmCoeff (i : Fin d) :
    ((esymmCoeff K d i : esymmField K d) : SymmetricRationalField K d) = esymmGen K d i :=
  esymmFieldEquiv_X i

/-- **The radical polynomial over an elementary symmetric function is irreducible.** -/
theorem irreducible_X_pow_sub_C_esymmCoeff (i : Fin d) {n : ℕ} (hn : 0 < n) :
    Irreducible (Polynomial.X ^ n - Polynomial.C (esymmCoeff K d i) :
      Polynomial (esymmField K d)) :=
  irreducible_X_pow_sub_C_map (esymmFieldEquiv K d)
    (irreducible_X_pow_sub_C_of_prime (MvPolynomial.X_prime (i := i)) hn)

/-- **A root of it generates an extension of exactly that degree.** -/
theorem finrank_adjoin_esymmCoeff_root {L : Type*} [Field L] [Algebra (esymmField K d) L]
    (i : Fin d) {n : ℕ} (hn : 0 < n) {α : L}
    (hα : α ^ n = algebraMap (esymmField K d) L (esymmCoeff K d i)) :
    Module.finrank (esymmField K d) (esymmField K d)⟮α⟯ = n :=
  finrank_adjoin_of_irreducible hn (irreducible_X_pow_sub_C_esymmCoeff i hn) hα

end GaloisForLFunctions.HTGeometry
