import GaloisForLFunctions.HTGeometry.PaperIntegralSymmetricRetraction
import GaloisForLFunctions.HTGeometry.SymmetricDescentBaseChange

/-!
# Integral symmetric splitting commutes with every coefficient map

The divided antisymmetrization is uniquely characterized by multiplication
by the regular universal Vandermonde. Consequently it commutes with every
ring homomorphism, including noninjective maps and reduction to positive
characteristic. The native symmetric descent transfers the same identity
to the coefficient-linear retraction.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {K L : Type*} [CommRing K] [CommRing L] (n : ℕ) (f : K →+* L)

/-- The universal Vandermonde is unchanged by arbitrary change of coefficients. -/
theorem paperUniversalVandermonde_baseChange :
    MvPolynomial.map f (paperUniversalVandermonde K n) = paperUniversalVandermonde L n := by
  simp only [paperUniversalVandermonde, vandermondeProd, map_prod, map_sub, map_X]

/-- Integral antisymmetrization commutes with every coefficient homomorphism. -/
theorem paperIntegralAntisymmetrization_baseChange (p : MvPolynomial (Fin n) K) :
    MvPolynomial.map f (paperIntegralAntisymmetrization K n p) =
      paperIntegralAntisymmetrization L n (MvPolynomial.map f p) := by
  simp only [paperIntegralAntisymmetrization_apply, map_sum, map_zsmul, MvPolynomial.map_rename]

/-- The staircase normalization is integral and compatible with every coefficient map. -/
theorem paperSymmetricStaircase_baseChange :
    MvPolynomial.map f (paperSymmetricStaircase K n) = paperSymmetricStaircase L n := by
  simp only [paperSymmetricStaircase, map_prod, map_pow, map_X]

/-- The symmetric projection commutes with arbitrary base change, without a flatness premise. -/
theorem paperIntegralSymmetricProjection_baseChange (p : MvPolynomial (Fin n) K) :
    MvPolynomial.map f (paperIntegralSymmetricProjection K n p) =
      paperIntegralSymmetricProjection L n (MvPolynomial.map f p) := by
  apply (paperUniversalVandermonde_regular L n).left
  dsimp only
  calc
    paperUniversalVandermonde L n * MvPolynomial.map f (paperIntegralSymmetricProjection K n p) =
        MvPolynomial.map f
          (paperUniversalVandermonde K n * paperIntegralSymmetricProjection K n p) := by
      rw [map_mul, paperUniversalVandermonde_baseChange]
    _ = paperIntegralAntisymmetrization L n
        (paperSymmetricStaircase L n * MvPolynomial.map f p) := by
      rw [paperIntegralSymmetricProjection_spec, paperIntegralAntisymmetrization_baseChange,
        map_mul, paperSymmetricStaircase_baseChange]
    _ = paperUniversalVandermonde L n *
        paperIntegralSymmetricProjection L n (MvPolynomial.map f p) :=
      (paperIntegralSymmetricProjection_spec L n _).symm

/-- The coefficient retraction is natural even for noninjective coefficient maps. -/
theorem paperIntegralSymmetricCoefficientRetraction_baseChange (p : MvPolynomial (Fin n) K) :
    MvPolynomial.map f (paperIntegralSymmetricCoefficientRetraction K n p) =
      paperIntegralSymmetricCoefficientRetraction L n (MvPolynomial.map f p) := by
  apply (MvPolynomial.esymmAlgEquiv (Fin n) L (Fintype.card_fin n)).injective
  apply Subtype.ext
  simp only [MvPolynomial.esymmAlgEquiv_apply, esymmAlgHom_apply]
  have h := map_esymmAlgHom (σ := Fin n) f
  rw [Fintype.card_fin] at h
  simp only [esymmAlgHom_apply] at h
  rw [h (paperIntegralSymmetricCoefficientRetraction K n p),
    paperIntegralSymmetricCoefficientRetraction_spec,
    paperIntegralSymmetricCoefficientRetraction_spec,
    paperIntegralSymmetricProjection_baseChange]

end

end GaloisForLFunctions.HTGeometry
