import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapLowCoefficients

namespace HTGeometry
noncomputable section
open GaloisForLFunctions.HTGeometry
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

attribute [local irreducible] evenCompactGapSourceZeroPolynomial evenCompactGapReflectedTwoPolynomial evenCompactGapReflectedFourPolynomial evenCompactGapReflectedSixPolynomial evenCompactGapReflectedEightPolynomial evenCompactGapReflectedTenPolynomial evenCompactGapReflectedTwelvePolynomial

/-- Exact degree-3 identity with every source and correction coefficient retained. -/
theorem evenCompactGapDetPolynomial_coeff_three (u w : ℝ) :
    (evenCompactGapDetPolynomial u w).coeff 3 = evenCompactRawGapGrade3 u w := by
  norm_num [evenCompactGapDetPolynomial, hankelFourDet,
    pow_succ,
    Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg,
    Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, Polynomial.coeff_C,
    Polynomial.mul_coeff_zero, Polynomial.mul_coeff_one,
    evenCompactGapCoeff_mul_2, evenCompactGapCoeff_mul_3]
  norm_num [evenCompactGapSourceZeroPolynomial_coeff, evenCompactGapReflectedTwoPolynomial_coeff, evenCompactGapReflectedFourPolynomial_coeff, evenCompactGapReflectedSixPolynomial_coeff, evenCompactGapReflectedEightPolynomial_coeff, evenCompactGapReflectedTenPolynomial_coeff, evenCompactGapReflectedTwelvePolynomial_coeff,
    evenCompactGapSourceZeroCoeff, evenCompactGapReflectedTwoCoeff, evenCompactGapReflectedFourCoeff, evenCompactGapReflectedSixCoeff, evenCompactGapReflectedEightCoeff, evenCompactGapReflectedTenCoeff, evenCompactGapReflectedTwelveCoeff]
  unfold evenCompactRawGapGrade3
  ring1

end
end HTGeometry
