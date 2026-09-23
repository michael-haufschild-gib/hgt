import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient0
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient1
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient2
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient3
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient4
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient5
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient6
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient7
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient8
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient9
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient10
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient11
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient12
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient13
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient14
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient15
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient16
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient17
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient18
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient19
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCoefficient20
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapTableCoefficients

/-! # Exact equality of the compact gap determinant and its graded coefficient table -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

/-- The lifted compact determinant equals the stored raw coefficient table as a polynomial. -/
theorem evenCompactGapDetPolynomial_eq_table (u w : ℝ) :
    evenCompactGapDetPolynomial u w = evenCompactGapTablePolynomial u w := by
  ext n
  rcases le_or_lt n 20 with h | h
  · interval_cases n <;>
      simp only [evenCompactGapDetPolynomial_coeff_zero,
    evenCompactGapDetPolynomial_coeff_one,
    evenCompactGapDetPolynomial_coeff_two,
    evenCompactGapDetPolynomial_coeff_three,
    evenCompactGapDetPolynomial_coeff_four,
    evenCompactGapDetPolynomial_coeff_five,
    evenCompactGapDetPolynomial_coeff_six,
    evenCompactGapDetPolynomial_coeff_seven,
    evenCompactGapDetPolynomial_coeff_eight,
    evenCompactGapDetPolynomial_coeff_nine,
    evenCompactGapDetPolynomial_coeff_ten,
    evenCompactGapDetPolynomial_coeff_eleven,
    evenCompactGapDetPolynomial_coeff_twelve,
    evenCompactGapDetPolynomial_coeff_thirteen,
    evenCompactGapDetPolynomial_coeff_fourteen,
    evenCompactGapDetPolynomial_coeff_fifteen,
    evenCompactGapDetPolynomial_coeff_sixteen,
    evenCompactGapDetPolynomial_coeff_seventeen,
    evenCompactGapDetPolynomial_coeff_eighteen,
    evenCompactGapDetPolynomial_coeff_nineteen,
    evenCompactGapDetPolynomial_coeff_twenty,
        evenCompactGapTablePolynomial_coeff_0,
    evenCompactGapTablePolynomial_coeff_1,
    evenCompactGapTablePolynomial_coeff_2,
    evenCompactGapTablePolynomial_coeff_3,
    evenCompactGapTablePolynomial_coeff_4,
    evenCompactGapTablePolynomial_coeff_5,
    evenCompactGapTablePolynomial_coeff_6,
    evenCompactGapTablePolynomial_coeff_7,
    evenCompactGapTablePolynomial_coeff_8,
    evenCompactGapTablePolynomial_coeff_9,
    evenCompactGapTablePolynomial_coeff_10,
    evenCompactGapTablePolynomial_coeff_11,
    evenCompactGapTablePolynomial_coeff_12,
    evenCompactGapTablePolynomial_coeff_13,
    evenCompactGapTablePolynomial_coeff_14,
    evenCompactGapTablePolynomial_coeff_15,
    evenCompactGapTablePolynomial_coeff_16,
    evenCompactGapTablePolynomial_coeff_17,
    evenCompactGapTablePolynomial_coeff_18,
    evenCompactGapTablePolynomial_coeff_19,
    evenCompactGapTablePolynomial_coeff_20]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (evenCompactGapDetPolynomial_degree u w) h),
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (evenCompactGapTablePolynomial_degree u w) h)]

/-- The complete signed four-by-four source determinant equals its raw graded polynomial. -/
theorem evenCompactRawDet_eq_polynomial (u a w : ℝ) :
    evenCompactRawDet u a w = evenCompactRawPolynomial u a w := by
  rw [← evenCompactGapDetPolynomial_eval, evenCompactGapDetPolynomial_eq_table,
    evenCompactGapTablePolynomial_eval]

end
end HTGeometry
