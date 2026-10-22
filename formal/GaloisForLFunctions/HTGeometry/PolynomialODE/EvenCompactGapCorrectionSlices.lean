import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReversedDet
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapSourceZeroSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapLowCoefficients

namespace HTGeometry
noncomputable section
set_option maxRecDepth 10000

/-- Constant coefficient of the complete fixed correction. -/
def evenCompactGapCorrectionSlice0 (u : ℝ) : ℝ :=
  1000000000000 * evenCompactGapSourceZeroSlice0 u *
    (3 * evenCompactGapSourceZeroSlice0 u - 6/19)

/-- Linear coefficient of the complete fixed correction. -/
def evenCompactGapCorrectionSlice1 (u : ℝ) : ℝ :=
  1000000000000 * (evenCompactGapSourceZeroSlice0 u * (3 * evenCompactGapSourceZeroSlice1 u) +
    evenCompactGapSourceZeroSlice1 u * (3 * evenCompactGapSourceZeroSlice0 u - 6/19))

/-- Quadratic coefficient of the complete fixed correction. -/
def evenCompactGapCorrectionSlice2 (u : ℝ) : ℝ :=
  1000000000000 * evenCompactGapSourceZeroSlice1 u * (3 * evenCompactGapSourceZeroSlice1 u)

attribute [local irreducible] evenCompactGapSourceZeroPolynomial

theorem evenCompactGapCorrectionPolynomial_coeff_slice0 (u : ℝ) :
    (evenCompactGapCorrectionPolynomial u).coeff 0 = evenCompactGapCorrectionSlice0 u := by
  norm_num [evenCompactGapCorrectionPolynomial, Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_sub,
    Polynomial.mul_coeff_zero, evenCompactGapSourceZeroPolynomial_coeff_slice0,
    evenCompactGapCorrectionSlice0]

theorem evenCompactGapCorrectionPolynomial_coeff_slice1 (u : ℝ) :
    (evenCompactGapCorrectionPolynomial u).coeff 1 = evenCompactGapCorrectionSlice1 u := by
  norm_num [evenCompactGapCorrectionPolynomial, Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_sub,
    Polynomial.mul_coeff_zero, Polynomial.mul_coeff_one,
    evenCompactGapSourceZeroPolynomial_coeff_slice0,
    evenCompactGapSourceZeroPolynomial_coeff_slice1, evenCompactGapCorrectionSlice1]
  ring1

theorem evenCompactGapCorrectionPolynomial_coeff_slice2 (u : ℝ) :
    (evenCompactGapCorrectionPolynomial u).coeff 2 = evenCompactGapCorrectionSlice2 u := by
  norm_num [evenCompactGapCorrectionPolynomial, Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_sub,
    Polynomial.mul_coeff_zero, Polynomial.mul_coeff_one, evenCompactGapCoeff_mul_2,
    evenCompactGapSourceZeroPolynomial_coeff_slice0,
    evenCompactGapSourceZeroPolynomial_coeff_slice1,
    evenCompactGapSourceZeroPolynomial_coeff_above, evenCompactGapCorrectionSlice2]

end
end HTGeometry
