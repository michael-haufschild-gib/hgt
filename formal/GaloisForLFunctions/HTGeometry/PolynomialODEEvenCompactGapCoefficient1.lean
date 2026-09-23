import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapSourceZeroSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedTwoSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedFourSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedSixSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedEightSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedTenSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedTwelveSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapConvolution

namespace HTGeometry
noncomputable section
open GaloisForLFunctions.HTGeometry
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

attribute [local irreducible] evenCompactGapSourceZeroPolynomial evenCompactGapReflectedTwoPolynomial evenCompactGapReflectedFourPolynomial evenCompactGapReflectedSixPolynomial evenCompactGapReflectedEightPolynomial evenCompactGapReflectedTenPolynomial evenCompactGapReflectedTwelvePolynomial

/-- The first nonconstant gap coefficient retains the complete source convolution. -/
theorem evenCompactGapDetPolynomial_coeff_one (u w : ℝ) :
    (evenCompactGapDetPolynomial u w).coeff 1 = evenCompactRawGapGrade1 u w := by
  norm_num [evenCompactGapDetPolynomial, hankelFourDet,
    pow_succ,
    Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg,
    Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, Polynomial.coeff_C,
    Polynomial.mul_coeff_zero, Polynomial.mul_coeff_one]
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
  unfold evenCompactRawGapGrade1
  ring1

end
end HTGeometry
