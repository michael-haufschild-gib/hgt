import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactGradeBalance0
import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactScalarExpansion
import Mathlib.Tactic.LinearCombination

/-!
# Fixed positive compact reserve for the corrected odd determinant

The substituted determinant plus the weighted head product equals the cubic
minorant plus the nonnegative remainder at every drift degree. The cubic
minorant is at least `10^14` on the cube, and the remainder is nonnegative.
-/

namespace HTGeometry
noncomputable section
set_option maxRecDepth 4000

/-- Exact decomposition on the normalized unit cube. -/
theorem oddCompactScalarDet_lower_decomposition {u t w : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    oddCompactScalarDet u (17+3*t) w +
      1000000000*oddCompactScalarHead u (17+3*t) w*oddCompactLowerSource u (17+3*t) w =
      oddCompactCubicMinorant u t w + oddCompactRemainder u t w := by
  unfold oddCompactScalarDet oddCompactScalarHead oddCompactRemainder
  linear_combination
    (oddCompactScalarDetPart0_shift u t w +
    oddCompactScalarDetPart1_shift u t w +
    oddCompactScalarDetPart2_shift u t w +
    oddCompactScalarDetPart3_shift u t w +
    oddCompactScalarDetPart4_shift u t w +
    oddCompactScalarDetPart5_shift u t w +
    oddCompactScalarDetPart6_shift u t w +
    oddCompactScalarDetPart7_shift u t w +
    oddCompactScalarDetPart8_shift u t w +
    oddCompactScalarDetPart9_shift u t w +
    oddCompactScalarDetPart10_shift u t w +
    oddCompactScalarDetPart11_shift u t w +
    oddCompactScalarDetPart12_shift u t w +
    oddCompactScalarDetPart13_shift u t w +
    oddCompactScalarDetPart14_shift u t w +
    oddCompactScalarDetPart15_shift u t w +
    oddCompactScalarDetPart16_shift u t w +
    oddCompactScalarDetPart17_shift u t w +
    oddCompactScalarDetPart18_shift u t w +
    oddCompactScalarDetPart19_shift u t w +
    oddCompactScalarDetPart20_shift u t w +
    oddCompactScalarDetPart21_shift u t w +
    oddCompactScalarDetPart22_shift u t w +
    oddCompactScalarDetPart23_shift u t w +
    oddCompactScalarDetPart24_shift u t w +
    oddCompactScalarDetPart25_shift u t w +
    oddCompactScalarDetPart26_shift u t w +
    oddCompactScalarDetPart27_shift u t w +
    oddCompactScalarDetPart28_shift u t w +
    oddCompactScalarDetPart29_shift u t w +
    oddCompactScalarDetPart30_shift u t w +
    oddCompactScalarDetPart31_shift u t w +
    oddCompactScalarDetPart32_shift u t w +
    oddCompactScalarDetPart33_shift u t w) +
    1000000000*(oddCompactShiftedHeadLowPart0_eq u t w +
    oddCompactShiftedHeadLowPart1_eq u t w +
    oddCompactShiftedHeadLowPart2_eq u t w +
    oddCompactShiftedHeadLowPart3_eq u t w +
    oddCompactShiftedHeadLowPart4_eq u t w +
    oddCompactShiftedHeadLowPart5_eq u t w) +
    1000000000*(oddCompactScalarHeadPart0 u (17+3*t) w +
      oddCompactScalarHeadPart1 u (17+3*t) w +
      oddCompactScalarHeadPart2 u (17+3*t) w +
      oddCompactScalarHeadPart3 u (17+3*t) w +
      oddCompactScalarHeadPart4 u (17+3*t) w +
      oddCompactScalarHeadPart5 u (17+3*t) w)*oddCompactShiftedLowerSource_eq u t w +
    (oddCompactGradeBalance0 u t w +
    oddCompactGradeBalance1 u t w +
    oddCompactGradeBalance2 u t w +
    oddCompactGradeBalance3 u t w +
    oddCompactGradeBalance4 u t w +
    oddCompactGradeBalance5 u t w +
    oddCompactGradeBalance6 u t w +
    oddCompactGradeBalance7 u t w +
    oddCompactGradeBalance8 u t w +
    oddCompactGradeBalance9 u t w +
    oddCompactGradeBalance10 u t w +
    oddCompactGradeBalance11 u t w +
    oddCompactGradeBalance12 u t w +
    oddCompactGradeBalance13 u t w +
    oddCompactGradeBalance14 u t w +
    oddCompactGradeBalance15 u t w +
    oddCompactGradeBalance16 u t w +
    oddCompactGradeBalance17 u t w +
    oddCompactGradeBalance18 u t w +
    oddCompactGradeBalance19 u t w +
    oddCompactGradeBalance20 u t w +
    oddCompactGradeBalance21 u t w +
    oddCompactGradeBalance22 u t w +
    oddCompactGradeBalance23 u t w +
    oddCompactGradeBalance24 u t w +
    oddCompactGradeBalance25 u t w +
    oddCompactGradeBalance26 u t w +
    oddCompactGradeBalance27 u t w +
    oddCompactGradeBalance28 u t w +
    oddCompactGradeBalance30 u t w) -
    oddCompactCubicMinorant_grades u t w -
    (oddCompactRemainderPart0_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart1_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart2_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart3_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart4_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart5_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart6_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart7_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart8_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart9_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart10_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart11_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart12_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart13_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart14_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart15_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart16_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart17_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart18_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart19_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart20_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart21_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart22_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart23_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart24_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart25_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart26_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart27_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart28_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart29_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart30_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart31_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart32_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart33_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart34_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart35_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart36_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart37_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart38_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart39_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart40_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart41_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart42_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart43_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart44_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart45_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart46_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart47_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart48_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart49_grades hu0 hu1 ht0 ht1 hw0 hw1 +
    oddCompactRemainderPart50_grades hu0 hu1 ht0 ht1 hw0 hw1)

/-- Exact normalized determinant decomposition on the unit cube. -/
theorem oddCompactDet_lower_decomposition {u t w : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    oddCompactDet u (17+3*t) w +
      1000000000*oddCompactHead u (17+3*t) w*oddCompactLowerSource u (17+3*t) w =
      oddCompactCubicMinorant u t w + oddCompactRemainder u t w := by
  rw [oddCompactDet_eq_scalarPolynomial, oddCompactHead_eq_scalarPolynomial]
  exact oddCompactScalarDet_lower_decomposition hu0 hu1 ht0 ht1 hw0 hw1

/-- Fixed arithmetic reserve throughout the complete compact modular box. -/
theorem oddCompactDet_corrected_lower {u a w : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ha0 : 17 ≤ a) (ha1 : a ≤ 20)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    100000000000000 ≤ oddCompactDet u a w +
      1000000000*oddCompactHead u a w*oddCompactLowerSource u a w := by
  let t := (a-17)/3
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have ha : a = 17+3*t := by dsimp [t]; ring
  rw [ha, oddCompactDet_lower_decomposition hu0 hu1 ht0 ht1 hw0 hw1]
  exact (oddCompactCubicMinorant_lower hu0 hu1 ht0 ht1 hw0 hw1).trans
    (le_add_of_nonneg_right (oddCompactRemainder_nonneg hu0 ht0 hw0))

end
end HTGeometry
