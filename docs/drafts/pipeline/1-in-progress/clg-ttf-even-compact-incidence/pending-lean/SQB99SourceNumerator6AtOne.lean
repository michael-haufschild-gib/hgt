import SQB99CoefficientCore
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentZeroInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentOneInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentTwoInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentThreeInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentFourInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentFiveInteger
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentSixInteger
import Mathlib.Tactic.Ring
namespace SQBCompactRow
noncomputable section
set_option maxHeartbeats 400000

def groupedNumerator6 (t v : ℝ) : ℝ :=
  (((((((n6_0_0 : ℝ)*t^(0 : ℕ)*v^(0 : ℕ) +
  (n6_1_0 : ℝ)*t^(1 : ℕ)*v^(0 : ℕ)) +
  ((n6_2_0 : ℝ)*t^(2 : ℕ)*v^(0 : ℕ) +
  (n6_3_0 : ℝ)*t^(3 : ℕ)*v^(0 : ℕ))) +
  (((n6_4_0 : ℝ)*t^(4 : ℕ)*v^(0 : ℕ) +
  (n6_5_0 : ℝ)*t^(5 : ℕ)*v^(0 : ℕ)) +
  ((n6_6_0 : ℝ)*t^(6 : ℕ)*v^(0 : ℕ) +
  ((n6_7_0 : ℝ)*t^(7 : ℕ)*v^(0 : ℕ) +
  (n6_8_0 : ℝ)*t^(8 : ℕ)*v^(0 : ℕ))))) +
  ((((n6_0_1 : ℝ)*t^(0 : ℕ)*v^(1 : ℕ) +
  (n6_0_2 : ℝ)*t^(0 : ℕ)*v^(2 : ℕ)) +
  ((n6_1_1 : ℝ)*t^(1 : ℕ)*v^(1 : ℕ) +
  (n6_1_2 : ℝ)*t^(1 : ℕ)*v^(2 : ℕ))) +
  (((n6_2_1 : ℝ)*t^(2 : ℕ)*v^(1 : ℕ) +
  (n6_2_2 : ℝ)*t^(2 : ℕ)*v^(2 : ℕ)) +
  ((n6_3_1 : ℝ)*t^(3 : ℕ)*v^(1 : ℕ) +
  ((n6_3_2 : ℝ)*t^(3 : ℕ)*v^(2 : ℕ) +
  (n6_4_1 : ℝ)*t^(4 : ℕ)*v^(1 : ℕ)))))) +
  (((((n6_4_2 : ℝ)*t^(4 : ℕ)*v^(2 : ℕ) +
  (n6_5_1 : ℝ)*t^(5 : ℕ)*v^(1 : ℕ)) +
  ((n6_5_2 : ℝ)*t^(5 : ℕ)*v^(2 : ℕ) +
  (n6_6_1 : ℝ)*t^(6 : ℕ)*v^(1 : ℕ))) +
  (((n6_6_2 : ℝ)*t^(6 : ℕ)*v^(2 : ℕ) +
  (n6_7_1 : ℝ)*t^(7 : ℕ)*v^(1 : ℕ)) +
  ((n6_7_2 : ℝ)*t^(7 : ℕ)*v^(2 : ℕ) +
  ((n6_0_3 : ℝ)*t^(0 : ℕ)*v^(3 : ℕ) +
  (n6_0_4 : ℝ)*t^(0 : ℕ)*v^(4 : ℕ))))) +
  ((((n6_1_3 : ℝ)*t^(1 : ℕ)*v^(3 : ℕ) +
  (n6_1_4 : ℝ)*t^(1 : ℕ)*v^(4 : ℕ)) +
  ((n6_2_3 : ℝ)*t^(2 : ℕ)*v^(3 : ℕ) +
  ((n6_2_4 : ℝ)*t^(2 : ℕ)*v^(4 : ℕ) +
  (n6_3_3 : ℝ)*t^(3 : ℕ)*v^(3 : ℕ)))) +
  (((n6_3_4 : ℝ)*t^(3 : ℕ)*v^(4 : ℕ) +
  (n6_4_3 : ℝ)*t^(4 : ℕ)*v^(3 : ℕ)) +
  ((n6_4_4 : ℝ)*t^(4 : ℕ)*v^(4 : ℕ) +
  ((n6_5_3 : ℝ)*t^(5 : ℕ)*v^(3 : ℕ) +
  (n6_5_4 : ℝ)*t^(5 : ℕ)*v^(4 : ℕ))))))) +
  ((((((n6_6_3 : ℝ)*t^(6 : ℕ)*v^(3 : ℕ) +
  (n6_6_4 : ℝ)*t^(6 : ℕ)*v^(4 : ℕ)) +
  ((n6_0_5 : ℝ)*t^(0 : ℕ)*v^(5 : ℕ) +
  (n6_0_6 : ℝ)*t^(0 : ℕ)*v^(6 : ℕ))) +
  (((n6_1_5 : ℝ)*t^(1 : ℕ)*v^(5 : ℕ) +
  (n6_1_6 : ℝ)*t^(1 : ℕ)*v^(6 : ℕ)) +
  ((n6_2_5 : ℝ)*t^(2 : ℕ)*v^(5 : ℕ) +
  ((n6_2_6 : ℝ)*t^(2 : ℕ)*v^(6 : ℕ) +
  (n6_3_5 : ℝ)*t^(3 : ℕ)*v^(5 : ℕ))))) +
  ((((n6_3_6 : ℝ)*t^(3 : ℕ)*v^(6 : ℕ) +
  (n6_4_5 : ℝ)*t^(4 : ℕ)*v^(5 : ℕ)) +
  ((n6_4_6 : ℝ)*t^(4 : ℕ)*v^(6 : ℕ) +
  (n6_5_5 : ℝ)*t^(5 : ℕ)*v^(5 : ℕ))) +
  (((n6_5_6 : ℝ)*t^(5 : ℕ)*v^(6 : ℕ) +
  (n6_0_7 : ℝ)*t^(0 : ℕ)*v^(7 : ℕ)) +
  ((n6_0_8 : ℝ)*t^(0 : ℕ)*v^(8 : ℕ) +
  ((n6_1_7 : ℝ)*t^(1 : ℕ)*v^(7 : ℕ) +
  (n6_1_8 : ℝ)*t^(1 : ℕ)*v^(8 : ℕ)))))) +
  (((((n6_2_7 : ℝ)*t^(2 : ℕ)*v^(7 : ℕ) +
  (n6_2_8 : ℝ)*t^(2 : ℕ)*v^(8 : ℕ)) +
  ((n6_3_7 : ℝ)*t^(3 : ℕ)*v^(7 : ℕ) +
  (n6_3_8 : ℝ)*t^(3 : ℕ)*v^(8 : ℕ))) +
  (((n6_4_7 : ℝ)*t^(4 : ℕ)*v^(7 : ℕ) +
  (n6_4_8 : ℝ)*t^(4 : ℕ)*v^(8 : ℕ)) +
  ((n6_0_9 : ℝ)*t^(0 : ℕ)*v^(9 : ℕ) +
  ((n6_0_10 : ℝ)*t^(0 : ℕ)*v^(10 : ℕ) +
  (n6_1_9 : ℝ)*t^(1 : ℕ)*v^(9 : ℕ))))) +
  ((((n6_1_10 : ℝ)*t^(1 : ℕ)*v^(10 : ℕ) +
  (n6_2_9 : ℝ)*t^(2 : ℕ)*v^(9 : ℕ)) +
  ((n6_2_10 : ℝ)*t^(2 : ℕ)*v^(10 : ℕ) +
  ((n6_3_9 : ℝ)*t^(3 : ℕ)*v^(9 : ℕ) +
  (n6_3_10 : ℝ)*t^(3 : ℕ)*v^(10 : ℕ)))) +
  (((n6_0_11 : ℝ)*t^(0 : ℕ)*v^(11 : ℕ) +
  (n6_0_12 : ℝ)*t^(0 : ℕ)*v^(12 : ℕ)) +
  ((n6_1_11 : ℝ)*t^(1 : ℕ)*v^(11 : ℕ) +
  ((n6_1_12 : ℝ)*t^(1 : ℕ)*v^(12 : ℕ) +
  (n6_2_11 : ℝ)*t^(2 : ℕ)*v^(11 : ℕ))))))))

theorem sourceNumerator6_at_one (t v : ℝ) :
  HTGeometry.evenCompactUnitMomentSixNumerator 1 t v = groupedNumerator6 t v := by
  unfold HTGeometry.evenCompactUnitMomentSixNumerator groupedNumerator6
  norm_num only [one_pow, mul_one, n6_0_0, n6_1_0, n6_2_0, n6_3_0, n6_4_0, n6_5_0, n6_6_0, n6_7_0, n6_8_0, n6_0_1, n6_0_2, n6_1_1, n6_1_2, n6_2_1, n6_2_2, n6_3_1, n6_3_2, n6_4_1, n6_4_2, n6_5_1, n6_5_2, n6_6_1, n6_6_2, n6_7_1, n6_7_2, n6_0_3, n6_0_4, n6_1_3, n6_1_4, n6_2_3, n6_2_4, n6_3_3, n6_3_4, n6_4_3, n6_4_4, n6_5_3, n6_5_4, n6_6_3, n6_6_4, n6_0_5, n6_0_6, n6_1_5, n6_1_6, n6_2_5, n6_2_6, n6_3_5, n6_3_6, n6_4_5, n6_4_6, n6_5_5, n6_5_6, n6_0_7, n6_0_8, n6_1_7, n6_1_8, n6_2_7, n6_2_8, n6_3_7, n6_3_8, n6_4_7, n6_4_8, n6_0_9, n6_0_10, n6_1_9, n6_1_10, n6_2_9, n6_2_10, n6_3_9, n6_3_10, n6_0_11, n6_0_12, n6_1_11, n6_1_12, n6_2_11, Int.cast_add, Int.cast_neg, Int.cast_ofNat]
  ring
end
end SQBCompactRow
