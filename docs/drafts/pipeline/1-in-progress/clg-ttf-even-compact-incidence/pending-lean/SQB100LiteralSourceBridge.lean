import SQB100GroupedNumerators
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentZeroInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentOneInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentTwoInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentThreeInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentFourInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentFiveInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentSixInteger

namespace SQBCompactRow

theorem literalNumerator0_eq_source (r t v : ℝ) :
  literalNumerator0 r t v = HTGeometry.evenCompactUnitMomentZeroNumerator r t v := by
  rfl

theorem literalNumerator1_eq_source (r t v : ℝ) :
  literalNumerator1 r t v = HTGeometry.evenCompactUnitMomentOneNumerator r t v := by
  rfl

theorem literalNumerator2_eq_source (r t v : ℝ) :
  literalNumerator2 r t v = HTGeometry.evenCompactUnitMomentTwoNumerator r t v := by
  rfl

theorem literalNumerator3_eq_source (r t v : ℝ) :
  literalNumerator3 r t v = HTGeometry.evenCompactUnitMomentThreeNumerator r t v := by
  rfl

theorem literalNumerator4_eq_source (r t v : ℝ) :
  literalNumerator4 r t v = HTGeometry.evenCompactUnitMomentFourNumerator r t v := by
  rfl

theorem literalNumerator5_eq_source (r t v : ℝ) :
  literalNumerator5 r t v = HTGeometry.evenCompactUnitMomentFiveNumerator r t v := by
  rfl

theorem literalNumerator6_eq_source (r t v : ℝ) :
  literalNumerator6 r t v = HTGeometry.evenCompactUnitMomentSixNumerator r t v := by
  rfl

theorem nativeSourceNumerator0_at_one (t v : ℝ) :
  HTGeometry.evenCompactUnitMomentZeroNumerator 1 t v = groupedNumerator0 t v := by
  rw [← literalNumerator0_eq_source]
  exact sourceNumerator0_at_one t v

theorem nativeSourceNumerator1_at_one (t v : ℝ) :
  HTGeometry.evenCompactUnitMomentOneNumerator 1 t v = groupedNumerator1 t v := by
  rw [← literalNumerator1_eq_source]
  exact sourceNumerator1_at_one t v

theorem nativeSourceNumerator2_at_one (t v : ℝ) :
  HTGeometry.evenCompactUnitMomentTwoNumerator 1 t v = groupedNumerator2 t v := by
  rw [← literalNumerator2_eq_source]
  exact sourceNumerator2_at_one t v

theorem nativeSourceNumerator3_at_one (t v : ℝ) :
  HTGeometry.evenCompactUnitMomentThreeNumerator 1 t v = groupedNumerator3 t v := by
  rw [← literalNumerator3_eq_source]
  exact sourceNumerator3_at_one t v

theorem nativeSourceNumerator4_at_one (t v : ℝ) :
  HTGeometry.evenCompactUnitMomentFourNumerator 1 t v = groupedNumerator4 t v := by
  rw [← literalNumerator4_eq_source]
  exact sourceNumerator4_at_one t v

theorem nativeSourceNumerator5_at_one (t v : ℝ) :
  HTGeometry.evenCompactUnitMomentFiveNumerator 1 t v = groupedNumerator5 t v := by
  rw [← literalNumerator5_eq_source]
  exact sourceNumerator5_at_one t v

theorem nativeSourceNumerator6_at_one (t v : ℝ) :
  HTGeometry.evenCompactUnitMomentSixNumerator 1 t v = groupedNumerator6 t v := by
  rw [← literalNumerator6_eq_source]
  exact sourceNumerator6_at_one t v

end SQBCompactRow
