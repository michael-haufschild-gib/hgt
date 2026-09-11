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

def groupedNumerator4 (t v : ℝ) : ℝ :=
  ((((((n4_0_0 : ℝ)*t^(0 : ℕ)*v^(0 : ℕ) +
  (n4_1_0 : ℝ)*t^(1 : ℕ)*v^(0 : ℕ)) +
  ((n4_2_0 : ℝ)*t^(2 : ℕ)*v^(0 : ℕ) +
  ((n4_3_0 : ℝ)*t^(3 : ℕ)*v^(0 : ℕ) +
  (n4_4_0 : ℝ)*t^(4 : ℕ)*v^(0 : ℕ)))) +
  (((n4_5_0 : ℝ)*t^(5 : ℕ)*v^(0 : ℕ) +
  (n4_6_0 : ℝ)*t^(6 : ℕ)*v^(0 : ℕ)) +
  ((n4_0_1 : ℝ)*t^(0 : ℕ)*v^(1 : ℕ) +
  ((n4_0_2 : ℝ)*t^(0 : ℕ)*v^(2 : ℕ) +
  (n4_1_1 : ℝ)*t^(1 : ℕ)*v^(1 : ℕ))))) +
  ((((n4_1_2 : ℝ)*t^(1 : ℕ)*v^(2 : ℕ) +
  (n4_2_1 : ℝ)*t^(2 : ℕ)*v^(1 : ℕ)) +
  ((n4_2_2 : ℝ)*t^(2 : ℕ)*v^(2 : ℕ) +
  ((n4_3_1 : ℝ)*t^(3 : ℕ)*v^(1 : ℕ) +
  (n4_3_2 : ℝ)*t^(3 : ℕ)*v^(2 : ℕ)))) +
  (((n4_4_1 : ℝ)*t^(4 : ℕ)*v^(1 : ℕ) +
  ((n4_4_2 : ℝ)*t^(4 : ℕ)*v^(2 : ℕ) +
  (n4_5_1 : ℝ)*t^(5 : ℕ)*v^(1 : ℕ))) +
  ((n4_5_2 : ℝ)*t^(5 : ℕ)*v^(2 : ℕ) +
  ((n4_0_3 : ℝ)*t^(0 : ℕ)*v^(3 : ℕ) +
  (n4_0_4 : ℝ)*t^(0 : ℕ)*v^(4 : ℕ)))))) +
  (((((n4_1_3 : ℝ)*t^(1 : ℕ)*v^(3 : ℕ) +
  (n4_1_4 : ℝ)*t^(1 : ℕ)*v^(4 : ℕ)) +
  ((n4_2_3 : ℝ)*t^(2 : ℕ)*v^(3 : ℕ) +
  ((n4_2_4 : ℝ)*t^(2 : ℕ)*v^(4 : ℕ) +
  (n4_3_3 : ℝ)*t^(3 : ℕ)*v^(3 : ℕ)))) +
  (((n4_3_4 : ℝ)*t^(3 : ℕ)*v^(4 : ℕ) +
  (n4_4_3 : ℝ)*t^(4 : ℕ)*v^(3 : ℕ)) +
  ((n4_4_4 : ℝ)*t^(4 : ℕ)*v^(4 : ℕ) +
  ((n4_0_5 : ℝ)*t^(0 : ℕ)*v^(5 : ℕ) +
  (n4_0_6 : ℝ)*t^(0 : ℕ)*v^(6 : ℕ))))) +
  ((((n4_1_5 : ℝ)*t^(1 : ℕ)*v^(5 : ℕ) +
  (n4_1_6 : ℝ)*t^(1 : ℕ)*v^(6 : ℕ)) +
  ((n4_2_5 : ℝ)*t^(2 : ℕ)*v^(5 : ℕ) +
  ((n4_2_6 : ℝ)*t^(2 : ℕ)*v^(6 : ℕ) +
  (n4_3_5 : ℝ)*t^(3 : ℕ)*v^(5 : ℕ)))) +
  (((n4_3_6 : ℝ)*t^(3 : ℕ)*v^(6 : ℕ) +
  ((n4_0_7 : ℝ)*t^(0 : ℕ)*v^(7 : ℕ) +
  (n4_0_8 : ℝ)*t^(0 : ℕ)*v^(8 : ℕ))) +
  ((n4_1_7 : ℝ)*t^(1 : ℕ)*v^(7 : ℕ) +
  ((n4_1_8 : ℝ)*t^(1 : ℕ)*v^(8 : ℕ) +
  (n4_2_7 : ℝ)*t^(2 : ℕ)*v^(7 : ℕ)))))))

theorem sourceNumerator4_at_one (t v : ℝ) :
  HTGeometry.evenCompactUnitMomentFourNumerator 1 t v = groupedNumerator4 t v := by
  unfold HTGeometry.evenCompactUnitMomentFourNumerator groupedNumerator4
  norm_num only [one_pow, mul_one, n4_0_0, n4_1_0, n4_2_0, n4_3_0, n4_4_0, n4_5_0, n4_6_0, n4_0_1, n4_0_2, n4_1_1, n4_1_2, n4_2_1, n4_2_2, n4_3_1, n4_3_2, n4_4_1, n4_4_2, n4_5_1, n4_5_2, n4_0_3, n4_0_4, n4_1_3, n4_1_4, n4_2_3, n4_2_4, n4_3_3, n4_3_4, n4_4_3, n4_4_4, n4_0_5, n4_0_6, n4_1_5, n4_1_6, n4_2_5, n4_2_6, n4_3_5, n4_3_6, n4_0_7, n4_0_8, n4_1_7, n4_1_8, n4_2_7, Int.cast_add, Int.cast_neg, Int.cast_ofNat]
  ring

end
end SQBCompactRow
