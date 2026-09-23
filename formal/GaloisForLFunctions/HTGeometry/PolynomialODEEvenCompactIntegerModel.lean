import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentZeroInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentOneInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentTwoInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentThreeInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentFourInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentFiveInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentSixInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactModel

/-! # Grouped integer determinant with exact source scaling -/
namespace HTGeometry
noncomputable section
open GaloisForLFunctions.HTGeometry
set_option maxHeartbeats 1000000

/-- Integer correction numerator, retaining the factored full-source lower comparison. -/
def evenCompactIntegerCorrection (r t : ℝ) : ℝ :=
  (501530650214400000000000000000000/230400 : ℝ)*
    (393-52*r+3*t+32*r*t)*(57*(393-52*r+3*t+32*r*t)-2880)

/-- The common-denominator determinant retains its cofactor grouping. -/
def evenCompactIntegerDet (r t v : ℝ) : ℝ :=
  hankelFourDet ((19*501530650214400000000000000000000 : ℝ)/230400*evenCompactUnitMomentZeroNumerator r t v)
    ((19*501530650214400000000000000000000 : ℝ)/8294400000*evenCompactUnitMomentOneNumerator r t v)
    ((19*501530650214400000000000000000000 : ℝ)/298598400000000*evenCompactUnitMomentTwoNumerator r t v)
    ((19*501530650214400000000000000000000 : ℝ)/10749542400000000000*evenCompactUnitMomentThreeNumerator r t v)
    ((19*501530650214400000000000000000000 : ℝ)/128994508800000000000000*evenCompactUnitMomentFourNumerator r t v)
    ((19*501530650214400000000000000000000 : ℝ)/13931406950400000000000000000*evenCompactUnitMomentFiveNumerator r t v)
    (((19*501530650214400000000000000000000 : ℝ)/501530650214400000000000000000000*evenCompactUnitMomentSixNumerator r t v)+evenCompactIntegerCorrection r t)

/-- Exact grouped integer normalization, without expanding any moment numerator. -/
theorem evenCompactUnitDet_eq_integer_ratio (r t v : ℝ) :
    evenCompactUnitDet r t v = evenCompactIntegerDet r t v /
      (19*501530650214400000000000000000000 : ℝ)^(4 : ℕ) := by
  change hankelFourDet (evenCompactUnitMomentZero r t v) (evenCompactUnitMomentOne r t v)
    (evenCompactUnitMomentTwo r t v) (evenCompactUnitMomentThree r t v)
    (evenCompactUnitMomentFour r t v) (evenCompactUnitMomentFive r t v)
    (evenCompactUnitMomentSix r t v+evenCompactUnitCorrection r t) = _
  rw [evenCompactUnitMomentZero_eq_numerator, evenCompactUnitMomentOne_eq_numerator, evenCompactUnitMomentTwo_eq_numerator, evenCompactUnitMomentThree_eq_numerator, evenCompactUnitMomentFour_eq_numerator, evenCompactUnitMomentFive_eq_numerator, evenCompactUnitMomentSix_eq_numerator]
  unfold evenCompactIntegerDet hankelFourDet evenCompactIntegerCorrection
    evenCompactUnitCorrection evenCompactUnitSourceZero evenCompactUnitGap
  field_simp
  ring

end
end HTGeometry
