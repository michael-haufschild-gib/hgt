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
set_option maxHeartbeats 800000
set_option maxRecDepth 20000

/-- The lifted compact determinant equals the stored raw coefficient table as a polynomial. -/
theorem evenCompactGapDetPolynomial_eq_table (u w : ℝ) :
    evenCompactGapDetPolynomial u w = evenCompactGapTablePolynomial u w := by
  ext n
  by_cases h : n ≤ 20
  · interval_cases n
    · rw [evenCompactGapDetPolynomial_coeff_zero, evenCompactGapTablePolynomial_coeff_0]
    · rw [evenCompactGapDetPolynomial_coeff_one, evenCompactGapTablePolynomial_coeff_1]
    · rw [evenCompactGapDetPolynomial_coeff_two, evenCompactGapTablePolynomial_coeff_2]
    · rw [evenCompactGapDetPolynomial_coeff_three, evenCompactGapTablePolynomial_coeff_3]
    · rw [evenCompactGapDetPolynomial_coeff_four, evenCompactGapTablePolynomial_coeff_4]
    · rw [evenCompactGapDetPolynomial_coeff_five, evenCompactGapTablePolynomial_coeff_5]
    · rw [evenCompactGapDetPolynomial_coeff_six, evenCompactGapTablePolynomial_coeff_6]
    · rw [evenCompactGapDetPolynomial_coeff_seven, evenCompactGapTablePolynomial_coeff_7]
    · rw [evenCompactGapDetPolynomial_coeff_eight, evenCompactGapTablePolynomial_coeff_8]
    · rw [evenCompactGapDetPolynomial_coeff_nine, evenCompactGapTablePolynomial_coeff_9]
    · rw [evenCompactGapDetPolynomial_coeff_ten, evenCompactGapTablePolynomial_coeff_10]
    · rw [evenCompactGapDetPolynomial_coeff_eleven, evenCompactGapTablePolynomial_coeff_11]
    · rw [evenCompactGapDetPolynomial_coeff_twelve, evenCompactGapTablePolynomial_coeff_12]
    · rw [evenCompactGapDetPolynomial_coeff_thirteen, evenCompactGapTablePolynomial_coeff_13]
    · rw [evenCompactGapDetPolynomial_coeff_fourteen, evenCompactGapTablePolynomial_coeff_14]
    · rw [evenCompactGapDetPolynomial_coeff_fifteen, evenCompactGapTablePolynomial_coeff_15]
    · rw [evenCompactGapDetPolynomial_coeff_sixteen, evenCompactGapTablePolynomial_coeff_16]
    · rw [evenCompactGapDetPolynomial_coeff_seventeen, evenCompactGapTablePolynomial_coeff_17]
    · rw [evenCompactGapDetPolynomial_coeff_eighteen, evenCompactGapTablePolynomial_coeff_18]
    · rw [evenCompactGapDetPolynomial_coeff_nineteen, evenCompactGapTablePolynomial_coeff_19]
    · rw [evenCompactGapDetPolynomial_coeff_twenty, evenCompactGapTablePolynomial_coeff_20]
  · have h' : 20 < n := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (evenCompactGapDetPolynomial_degree u w) h'),
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (evenCompactGapTablePolynomial_degree u w) h')]

/-- The complete signed four-by-four source determinant equals its raw graded polynomial. -/
theorem evenCompactRawDet_eq_polynomial (u a w : ℝ) :
    evenCompactRawDet u a w = evenCompactRawPolynomial u a w := by
  rw [← evenCompactGapDetPolynomial_eval, evenCompactGapDetPolynomial_eq_table,
    evenCompactGapTablePolynomial_eval]

end
end HTGeometry
