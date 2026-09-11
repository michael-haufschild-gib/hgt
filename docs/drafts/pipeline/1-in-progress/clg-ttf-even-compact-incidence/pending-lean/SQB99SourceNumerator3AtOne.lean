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

def groupedNumerator3 (t v : ℝ) : ℝ :=
  (((((n3_0_0 : ℝ)*t^(0 : ℕ)*v^(0 : ℕ) +
  ((n3_1_0 : ℝ)*t^(1 : ℕ)*v^(0 : ℕ) +
  (n3_2_0 : ℝ)*t^(2 : ℕ)*v^(0 : ℕ))) +
  (((n3_3_0 : ℝ)*t^(3 : ℕ)*v^(0 : ℕ) +
  (n3_4_0 : ℝ)*t^(4 : ℕ)*v^(0 : ℕ)) +
  ((n3_5_0 : ℝ)*t^(5 : ℕ)*v^(0 : ℕ) +
  (n3_0_1 : ℝ)*t^(0 : ℕ)*v^(1 : ℕ)))) +
  (((n3_0_2 : ℝ)*t^(0 : ℕ)*v^(2 : ℕ) +
  ((n3_1_1 : ℝ)*t^(1 : ℕ)*v^(1 : ℕ) +
  (n3_1_2 : ℝ)*t^(1 : ℕ)*v^(2 : ℕ))) +
  (((n3_2_1 : ℝ)*t^(2 : ℕ)*v^(1 : ℕ) +
  (n3_2_2 : ℝ)*t^(2 : ℕ)*v^(2 : ℕ)) +
  ((n3_3_1 : ℝ)*t^(3 : ℕ)*v^(1 : ℕ) +
  (n3_3_2 : ℝ)*t^(3 : ℕ)*v^(2 : ℕ))))) +
  ((((n3_4_1 : ℝ)*t^(4 : ℕ)*v^(1 : ℕ) +
  ((n3_4_2 : ℝ)*t^(4 : ℕ)*v^(2 : ℕ) +
  (n3_0_3 : ℝ)*t^(0 : ℕ)*v^(3 : ℕ))) +
  (((n3_0_4 : ℝ)*t^(0 : ℕ)*v^(4 : ℕ) +
  (n3_1_3 : ℝ)*t^(1 : ℕ)*v^(3 : ℕ)) +
  ((n3_1_4 : ℝ)*t^(1 : ℕ)*v^(4 : ℕ) +
  (n3_2_3 : ℝ)*t^(2 : ℕ)*v^(3 : ℕ)))) +
  ((((n3_2_4 : ℝ)*t^(2 : ℕ)*v^(4 : ℕ) +
  (n3_3_3 : ℝ)*t^(3 : ℕ)*v^(3 : ℕ)) +
  ((n3_3_4 : ℝ)*t^(3 : ℕ)*v^(4 : ℕ) +
  (n3_0_5 : ℝ)*t^(0 : ℕ)*v^(5 : ℕ))) +
  (((n3_0_6 : ℝ)*t^(0 : ℕ)*v^(6 : ℕ) +
  (n3_1_5 : ℝ)*t^(1 : ℕ)*v^(5 : ℕ)) +
  ((n3_1_6 : ℝ)*t^(1 : ℕ)*v^(6 : ℕ) +
  (n3_2_5 : ℝ)*t^(2 : ℕ)*v^(5 : ℕ))))))

theorem sourceNumerator3_at_one (t v : ℝ) :
  HTGeometry.evenCompactUnitMomentThreeNumerator 1 t v = groupedNumerator3 t v := by
  unfold HTGeometry.evenCompactUnitMomentThreeNumerator groupedNumerator3
  norm_num only [one_pow, mul_one, n3_0_0, n3_1_0, n3_2_0, n3_3_0, n3_4_0, n3_5_0, n3_0_1, n3_0_2, n3_1_1, n3_1_2, n3_2_1, n3_2_2, n3_3_1, n3_3_2, n3_4_1, n3_4_2, n3_0_3, n3_0_4, n3_1_3, n3_1_4, n3_2_3, n3_2_4, n3_3_3, n3_3_4, n3_0_5, n3_0_6, n3_1_5, n3_1_6, n3_2_5, Int.cast_add, Int.cast_neg, Int.cast_ofNat]
  ring

end
end SQBCompactRow
