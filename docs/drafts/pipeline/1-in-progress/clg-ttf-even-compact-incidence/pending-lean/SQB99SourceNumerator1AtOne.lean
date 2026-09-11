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

def groupedNumerator1 (t v : ℝ) : ℝ :=
  ((((n1_0_0 : ℝ)*t^(0 : ℕ)*v^(0 : ℕ) +
  (n1_1_0 : ℝ)*t^(1 : ℕ)*v^(0 : ℕ)) +
  ((n1_2_0 : ℝ)*t^(2 : ℕ)*v^(0 : ℕ) +
  (n1_3_0 : ℝ)*t^(3 : ℕ)*v^(0 : ℕ))) +
  (((n1_0_1 : ℝ)*t^(0 : ℕ)*v^(1 : ℕ) +
  (n1_0_2 : ℝ)*t^(0 : ℕ)*v^(2 : ℕ)) +
  ((n1_1_1 : ℝ)*t^(1 : ℕ)*v^(1 : ℕ) +
  ((n1_1_2 : ℝ)*t^(1 : ℕ)*v^(2 : ℕ) +
  (n1_2_1 : ℝ)*t^(2 : ℕ)*v^(1 : ℕ)))))

theorem sourceNumerator1_at_one (t v : ℝ) :
  HTGeometry.evenCompactUnitMomentOneNumerator 1 t v = groupedNumerator1 t v := by
  unfold HTGeometry.evenCompactUnitMomentOneNumerator groupedNumerator1
  norm_num only [one_pow, mul_one, n1_0_0, n1_1_0, n1_2_0, n1_3_0, n1_0_1, n1_0_2, n1_1_1, n1_1_2, n1_2_1, Int.cast_add, Int.cast_neg, Int.cast_ofNat]
  ring

end
end SQBCompactRow
