import GaloisForLFunctions.HTGeometry.PolynomialFirstOrderActivationBoundary
import GaloisForLFunctions.HTGeometry.PrimeDirichletConstraintCarrier

/-!
# Signed-prime sources force hypertranscendental polynomial-activation inputs

Apply the general first-order observation boundary to every oriented signed-prime source.  If the
source obeys a polynomial first-order law whose coefficients come from the differential field of
an input `h`, then `h` must itself be hypertranscendental over `ℂ`.

Thus an exact neural, genomic, or physical observation architecture of this type cannot hide the
arithmetic source in a differentially algebraic latent variable.  The positive conclusion locates
an infinite differential source in that latent channel.  This does not prove RH and does not make
the source criterion independent of the already formalized signed-prime differential independence.
-/

open scoped Differential

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- Every oriented signed-prime source satisfying a polynomial first-order observation law forces
the input generating its coefficient field to be hypertranscendental. -/
theorem signedPrimeSource_polynomialFirstOrder_law_forces_HT_input
    (epsilon : Nat.Primes → Bool)
    {h : arithmeticFunctionRationalCoordinateField}
    (P : Polynomial (differentialAdjoin ℂ
      ({h} : Set arithmeticFunctionRationalCoordinateField)))
    (hrel : (signedPrimeNaturalShiftPalette epsilon 0)′ =
      Polynomial.eval₂
        (algebraMap
          (differentialAdjoin ℂ
            ({h} : Set arithmeticFunctionRationalCoordinateField))
          arithmeticFunctionRationalCoordinateField)
        (signedPrimeNaturalShiftPalette epsilon 0) P) :
    HypertranscendentalOver ℂ h := by
  letI : Differential ℂ := ⟨0⟩
  letI : DifferentialAlgebra ℂ arithmeticFunctionRationalCoordinateField :=
    ⟨fun c => by
      rw [arithmeticFunctionRationalCoordinateField_deriv_complexConstant]
      change 0 = algebraMap ℂ arithmeticFunctionRationalCoordinateField 0
      rw [map_zero]⟩
  letI : CharZero arithmeticFunctionRationalCoordinateField :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective ℂ arithmeticFunctionRationalCoordinateField)
  apply hypertranscendentalOver_input_of_polynomial_firstOrder_output _ P hrel
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  have hpalette := signedPrimeNaturalShiftPalette_differentialIndependent_complex epsilon
  have hsource := hpalette.comp (fun _ : Unit => 0) (by
    intro u v huv
    exact Subsingleton.elim u v)
  simpa only [Function.comp_apply] using hsource

/-- The canonical all-positive prime source is the unsigned specialization. -/
theorem allPositiveSignedPrimeSource_polynomialFirstOrder_law_forces_HT_input
    {h : arithmeticFunctionRationalCoordinateField}
    (P : Polynomial (differentialAdjoin ℂ
      ({h} : Set arithmeticFunctionRationalCoordinateField)))
    (hrel : (signedPrimeNaturalShiftPalette (fun _ : Nat.Primes => false) 0)′ =
      Polynomial.eval₂
        (algebraMap
          (differentialAdjoin ℂ
            ({h} : Set arithmeticFunctionRationalCoordinateField))
          arithmeticFunctionRationalCoordinateField)
        (signedPrimeNaturalShiftPalette (fun _ : Nat.Primes => false) 0) P) :
    HypertranscendentalOver ℂ h :=
  signedPrimeSource_polynomialFirstOrder_law_forces_HT_input
    (fun _ : Nat.Primes => false) P hrel

end

end RHTower
