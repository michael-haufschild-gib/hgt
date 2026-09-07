import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReversedDet
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapLowCoefficients

namespace HTGeometry
noncomputable section
open GaloisForLFunctions.HTGeometry
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

attribute [local irreducible] evenCompactGapSourceZeroPolynomial evenCompactGapReflectedTwoPolynomial evenCompactGapReflectedFourPolynomial evenCompactGapReflectedSixPolynomial evenCompactGapReflectedEightPolynomial evenCompactGapReflectedTenPolynomial evenCompactGapReflectedTwelvePolynomial evenCompactGapCorrectionPolynomial

/-- Exact degree-15 identity, checked as reversed coefficient 5. -/
theorem evenCompactGapDetPolynomial_coeff_fifteen (u w : ℝ) :
    (evenCompactGapDetPolynomial u w).coeff 15 = evenCompactRawGapGrade15 u w := by
  have hcorr (n : ℕ) (hn : 2 < n) :
      (evenCompactGapCorrectionPolynomial u).coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      ((evenCompactGapCorrectionPolynomial_degree u).trans_lt hn)
  change (evenCompactGapDetPolynomial u w).coeff (20-5) = _
  rw [evenCompactGapDetPolynomial_coeff_from_reverse u w 5 (by omega)]
  norm_num [hcorr, evenCompactGapReversedDetPolynomial, hankelFourDet,
    evenCompactGapCorrectionPolynomial_reflect_coeff, Polynomial.coeff_reflect, Polynomial.revAt,
    pow_succ,
    Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg,
    Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, Polynomial.coeff_C,
    Polynomial.mul_coeff_zero, Polynomial.mul_coeff_one,
    evenCompactGapCoeff_mul_2, evenCompactGapCoeff_mul_3, evenCompactGapCoeff_mul_4, evenCompactGapCoeff_mul_5]
  norm_num [evenCompactGapSourceZeroPolynomial_coeff, evenCompactGapReflectedTwoPolynomial_coeff, evenCompactGapReflectedFourPolynomial_coeff, evenCompactGapReflectedSixPolynomial_coeff, evenCompactGapReflectedEightPolynomial_coeff, evenCompactGapReflectedTenPolynomial_coeff, evenCompactGapReflectedTwelvePolynomial_coeff,
    evenCompactGapSourceZeroCoeff, evenCompactGapReflectedTwoCoeff, evenCompactGapReflectedFourCoeff, evenCompactGapReflectedSixCoeff, evenCompactGapReflectedEightCoeff, evenCompactGapReflectedTenCoeff, evenCompactGapReflectedTwelveCoeff]
  unfold evenCompactRawGapGrade15
  ring1

end
end HTGeometry
