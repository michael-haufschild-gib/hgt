import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.ChebyshevCharacteristicReduction
import GaloisForLFunctions.HTGeometry.Polynomial.AdjoinRootTranslation

/-!
# Artin–Schreier coordinate algebras under Frobenius reduction

The trace substitution identifies the entire coordinate algebras, not only
their rational points. Taking the coefficient ring to be a polynomial ring
gives an isomorphism over the base line for Chebyshev Artin–Schreier curves.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Polynomial
variable {A : Type*} [CommRing A] (p : ℕ) [Fact p.Prime] [CharP A p]

/-- The polynomial defining an Artin–Schreier root algebra. -/
def artinSchreierPolynomial (f : A) : A[X] := X ^ p - X - C f

/-- Translating the root changes the right-hand side by an Artin–Schreier difference. -/
theorem artinSchreierPolynomial_translate (f t : A) :
    (artinSchreierPolynomial p f).comp (X + C (-t)) =
      artinSchreierPolynomial p (f + (t ^ p - t)) := by
  simp only [artinSchreierPolynomial, sub_comp, pow_comp, X_comp, C_comp, C_neg,
    ← sub_eq_add_neg, sub_pow_char, ← C_pow, C_add, C_sub]
  ring

/-- Frobenius reduction is a literal change of variable in the defining polynomial. -/
theorem artinSchreierPolynomial_trace_comp (s : ℕ) (f : A) :
    (artinSchreierPolynomial p f).comp (X + C (-frobeniusTraceSum p 1 s f)) =
      artinSchreierPolynomial p (f ^ (p ^ s)) := by
  rw [artinSchreierPolynomial_translate]
  have ht := frobeniusTraceSum_sub_pow p 1 s f
  simp only [pow_one, one_mul] at ht
  congr 1
  linear_combination -ht

/-- The Frobenius reduction identifies the quotient algebras over the coefficient ring. -/
def artinSchreierCoordinateReduction (s : ℕ) (f : A) :
    AdjoinRoot (artinSchreierPolynomial p (f ^ (p ^ s))) ≃ₐ[A]
      AdjoinRoot (artinSchreierPolynomial p f) := by
  rw [← artinSchreierPolynomial_trace_comp p s f]
  exact HTGeometry.adjoinRootTranslationEquiv
    (artinSchreierPolynomial p f) (-frobeniusTraceSum p 1 s f)

/-- Chebyshev degree reduction is an isomorphism of affine coordinate algebras over `A[X]`. -/
def chebyshevArtinSchreierCoordinateReduction (s m : ℕ) :
    AdjoinRoot (artinSchreierPolynomial p (dickson 1 (1 : A) (p ^ s * m))) ≃ₐ[A[X]]
      AdjoinRoot (artinSchreierPolynomial p (dickson 1 (1 : A) m)) := by
  rw [dickson_characteristic_reduction]
  exact artinSchreierCoordinateReduction p s _

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
