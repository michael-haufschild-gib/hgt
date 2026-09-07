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
  norm_num [evenCompactGapSourceZeroPolynomial_coeff, evenCompactGapReflectedTwoPolynomial_coeff, evenCompactGapReflectedFourPolynomial_coeff, evenCompactGapReflectedSixPolynomial_coeff, evenCompactGapReflectedEightPolynomial_coeff, evenCompactGapReflectedTenPolynomial_coeff, evenCompactGapReflectedTwelvePolynomial_coeff,
    evenCompactGapSourceZeroCoeff, evenCompactGapReflectedTwoCoeff, evenCompactGapReflectedFourCoeff, evenCompactGapReflectedSixCoeff, evenCompactGapReflectedEightCoeff, evenCompactGapReflectedTenCoeff, evenCompactGapReflectedTwelveCoeff]
  unfold evenCompactRawGapGrade1
  ring1

end
end HTGeometry
