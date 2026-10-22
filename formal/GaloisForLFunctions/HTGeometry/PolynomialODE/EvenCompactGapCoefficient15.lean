import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapSourceZeroSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReflectedTwoSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReflectedFourSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReflectedSixSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReflectedEightSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReflectedTenSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReflectedTwelveSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReversedDet
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapLowCoefficients
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCertifiedNormalizer

/-!
# Determinant coefficient at gap degree 15

Reversal at degree twenty sends coefficient `20-n` of the determinant to
coefficient `n` of the reversed determinant, here `n = 5`.
-/

namespace HTGeometry
noncomputable section
open GaloisForLFunctions.HTGeometry
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

attribute [local irreducible] evenCompactGapSourceZeroPolynomial evenCompactGapReflectedTwoPolynomial evenCompactGapReflectedFourPolynomial evenCompactGapReflectedSixPolynomial evenCompactGapReflectedEightPolynomial evenCompactGapReflectedTenPolynomial evenCompactGapReflectedTwelvePolynomial evenCompactGapCorrectionPolynomial

/-- Reversed coefficient 5, of the complete determinant. -/
def evenCompactGapReversedDetSlice5Certificate (u w : ℝ) :
    CompactGapNormalForm ((evenCompactGapReversedDetPolynomial u w).coeff 5) :=
  compactGapCertified% (
    norm_num [evenCompactGapCorrectionPolynomial_coeff_above,
      evenCompactGapReversedDetPolynomial,
      hankelFourDet,
      evenCompactGapCorrectionPolynomial_reflect_coeff,
      Polynomial.coeff_reflect,
      Polynomial.revAt,
      pow_succ,
      Polynomial.coeff_add,
      Polynomial.coeff_sub,
      Polynomial.coeff_neg,
      Polynomial.coeff_mul_C,
      Polynomial.coeff_C_mul,
      Polynomial.coeff_C,
      Polynomial.mul_coeff_zero,
      Polynomial.mul_coeff_one,
      evenCompactGapCoeff_mul_2,
      evenCompactGapCoeff_mul_3,
      evenCompactGapCoeff_mul_4,
      evenCompactGapCoeff_mul_5]
    norm_num [evenCompactGapSourceZeroPolynomial_coeff_slice0,
      evenCompactGapSourceZeroPolynomial_coeff_slice1,
      evenCompactGapSourceZeroPolynomial_coeff_above,
      evenCompactGapReflectedTwoPolynomial_coeff_slice0,
      evenCompactGapReflectedTwoPolynomial_coeff_slice1,
      evenCompactGapReflectedTwoPolynomial_coeff_slice2,
      evenCompactGapReflectedTwoPolynomial_coeff_slice3,
      evenCompactGapReflectedTwoPolynomial_coeff_above,
      evenCompactGapReflectedFourPolynomial_coeff_slice0,
      evenCompactGapReflectedFourPolynomial_coeff_slice1,
      evenCompactGapReflectedFourPolynomial_coeff_slice2,
      evenCompactGapReflectedFourPolynomial_coeff_slice3,
      evenCompactGapReflectedFourPolynomial_coeff_slice4,
      evenCompactGapReflectedFourPolynomial_coeff_above,
      evenCompactGapReflectedSixPolynomial_coeff_slice0,
      evenCompactGapReflectedSixPolynomial_coeff_slice1,
      evenCompactGapReflectedSixPolynomial_coeff_slice2,
      evenCompactGapReflectedSixPolynomial_coeff_slice3,
      evenCompactGapReflectedSixPolynomial_coeff_slice4,
      evenCompactGapReflectedSixPolynomial_coeff_slice5,
      evenCompactGapReflectedSixPolynomial_coeff_above,
      evenCompactGapReflectedEightPolynomial_coeff_slice0,
      evenCompactGapReflectedEightPolynomial_coeff_slice1,
      evenCompactGapReflectedEightPolynomial_coeff_slice2,
      evenCompactGapReflectedEightPolynomial_coeff_slice3,
      evenCompactGapReflectedEightPolynomial_coeff_slice4,
      evenCompactGapReflectedEightPolynomial_coeff_slice5,
      evenCompactGapReflectedEightPolynomial_coeff_slice6,
      evenCompactGapReflectedEightPolynomial_coeff_above,
      evenCompactGapReflectedTenPolynomial_coeff_slice0,
      evenCompactGapReflectedTenPolynomial_coeff_slice1,
      evenCompactGapReflectedTenPolynomial_coeff_slice2,
      evenCompactGapReflectedTenPolynomial_coeff_slice3,
      evenCompactGapReflectedTenPolynomial_coeff_slice4,
      evenCompactGapReflectedTenPolynomial_coeff_slice5,
      evenCompactGapReflectedTenPolynomial_coeff_slice6,
      evenCompactGapReflectedTenPolynomial_coeff_slice7,
      evenCompactGapReflectedTenPolynomial_coeff_above,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice0,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice1,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice2,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice3,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice4,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice5,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice6,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice7,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice8,
      evenCompactGapReflectedTwelvePolynomial_coeff_above]
    dsimp only [evenCompactGapSourceZeroSlice0,
      evenCompactGapSourceZeroSlice1,
      evenCompactGapReflectedTwoSlice0,
      evenCompactGapReflectedTwoSlice1,
      evenCompactGapReflectedTwoSlice2,
      evenCompactGapReflectedTwoSlice3,
      evenCompactGapReflectedFourSlice0,
      evenCompactGapReflectedFourSlice1,
      evenCompactGapReflectedFourSlice2,
      evenCompactGapReflectedFourSlice3,
      evenCompactGapReflectedFourSlice4,
      evenCompactGapReflectedSixSlice0,
      evenCompactGapReflectedSixSlice1,
      evenCompactGapReflectedSixSlice2,
      evenCompactGapReflectedSixSlice3,
      evenCompactGapReflectedSixSlice4,
      evenCompactGapReflectedSixSlice5,
      evenCompactGapReflectedEightSlice0,
      evenCompactGapReflectedEightSlice1,
      evenCompactGapReflectedEightSlice2,
      evenCompactGapReflectedEightSlice3,
      evenCompactGapReflectedEightSlice4,
      evenCompactGapReflectedEightSlice5,
      evenCompactGapReflectedEightSlice6,
      evenCompactGapReflectedTenSlice0,
      evenCompactGapReflectedTenSlice1,
      evenCompactGapReflectedTenSlice2,
      evenCompactGapReflectedTenSlice3,
      evenCompactGapReflectedTenSlice4,
      evenCompactGapReflectedTenSlice5,
      evenCompactGapReflectedTenSlice6,
      evenCompactGapReflectedTenSlice7,
      evenCompactGapReflectedTwelveSlice0,
      evenCompactGapReflectedTwelveSlice1,
      evenCompactGapReflectedTwelveSlice2,
      evenCompactGapReflectedTwelveSlice3,
      evenCompactGapReflectedTwelveSlice4,
      evenCompactGapReflectedTwelveSlice5,
      evenCompactGapReflectedTwelveSlice6,
      evenCompactGapReflectedTwelveSlice7,
      evenCompactGapReflectedTwelveSlice8]
    ) => ((evenCompactGapReversedDetPolynomial u w).coeff 5)

/-- The reversed determinant coefficient at index 5. -/
def evenCompactGapReversedDetSlice5 (u w : ℝ) : ℝ :=
  (evenCompactGapReversedDetSlice5Certificate u w).value

/-- The reversed coefficient equals its normalized scalar. -/
theorem evenCompactGapReversedDetPolynomial_coeff_slice5 (u w : ℝ) :
    (evenCompactGapReversedDetPolynomial u w).coeff 5 = evenCompactGapReversedDetSlice5 u w :=
  (evenCompactGapReversedDetSlice5Certificate u w).eq_value

/-- Exact degree-15 identity, retaining the full correction. -/
theorem evenCompactGapDetPolynomial_coeff_fifteen (u w : ℝ) :
    (evenCompactGapDetPolynomial u w).coeff 15 = evenCompactRawGapGrade15 u w := by
  change (evenCompactGapDetPolynomial u w).coeff (20-5) = _
  rw [evenCompactGapDetPolynomial_coeff_from_reverse u w 5 (by omega),
    evenCompactGapReversedDetPolynomial_coeff_slice5]
  unfold evenCompactGapReversedDetSlice5 evenCompactRawGapGrade15
  dsimp only [evenCompactGapReversedDetSlice5Certificate]
  ring1

end
end HTGeometry
