import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBernstein.PositiveRow
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactMomentZeroInteger
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactMomentOneInteger
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactMomentTwoInteger
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactMomentThreeInteger
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactMomentFourInteger
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactMomentFiveInteger
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactMomentSixInteger

/-!
# A compensated compact last-row margin at drift square one

The complete literal moment combination in the selected signed row has margin `1/100`
on the unit square. Every coefficient sign and source reconstruction is proved in Lean.
This is one signed row at one drift face; it does not assert compact matrix positivity
or propagation to every rank.
-/

namespace HTGeometry.EvenCompactBernstein

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

end HTGeometry.EvenCompactBernstein

namespace HTGeometry
open HTGeometry.EvenCompactBernstein
noncomputable section

theorem evenCompactUnitLastRow_at_one_eq_grouped (t v : ℝ) :
    evenCompactUnitMomentSix 1 t v - 3*evenCompactUnitMomentFive 1 t v -
      evenCompactUnitMomentFour 1 t v + 8*evenCompactUnitMomentThree 1 t v -
      (31/8)*evenCompactUnitMomentTwo 1 t v - (3/8)*evenCompactUnitMomentOne 1 t v +
      (15/64)*evenCompactUnitMomentZero 1 t v + evenCompactUnitCorrection 1 t - 1/100 =
        groupedSourceRow t v := by
  rw [evenCompactUnitMomentZero_eq_numerator, evenCompactUnitMomentOne_eq_numerator,
    evenCompactUnitMomentTwo_eq_numerator, evenCompactUnitMomentThree_eq_numerator,
    evenCompactUnitMomentFour_eq_numerator, evenCompactUnitMomentFive_eq_numerator,
    evenCompactUnitMomentSix_eq_numerator]
  rw [nativeSourceNumerator0_at_one, nativeSourceNumerator1_at_one,
    nativeSourceNumerator2_at_one, nativeSourceNumerator3_at_one,
    nativeSourceNumerator4_at_one, nativeSourceNumerator5_at_one,
    nativeSourceNumerator6_at_one]
  unfold groupedSourceRow evenCompactUnitCorrection evenCompactUnitSourceZero evenCompactUnitGap
  ring

theorem evenCompactUnitLastRow_at_one_ge {t v : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (1/100 : ℝ) ≤
      evenCompactUnitMomentSix 1 t v - 3*evenCompactUnitMomentFive 1 t v -
      evenCompactUnitMomentFour 1 t v + 8*evenCompactUnitMomentThree 1 t v -
      (31/8)*evenCompactUnitMomentTwo 1 t v - (3/8)*evenCompactUnitMomentOne 1 t v +
      (15/64)*evenCompactUnitMomentZero 1 t v + evenCompactUnitCorrection 1 t := by
  have h := groupedSourceRow_nonneg ht0 ht1 hv0 hv1
  rw [← evenCompactUnitLastRow_at_one_eq_grouped] at h
  exact sub_nonneg.mp h

end
end HTGeometry
