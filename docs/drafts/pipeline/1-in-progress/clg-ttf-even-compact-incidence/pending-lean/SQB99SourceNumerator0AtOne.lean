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

def groupedNumerator0 (t v : ℝ) : ℝ :=
  ((n0_0_0 : ℝ)*t^(0 : ℕ)*v^(0 : ℕ) +
  ((n0_1_0 : ℝ)*t^(1 : ℕ)*v^(0 : ℕ) +
  (n0_2_0 : ℝ)*t^(2 : ℕ)*v^(0 : ℕ)))

theorem sourceNumerator0_at_one (t v : ℝ) :
  HTGeometry.evenCompactUnitMomentZeroNumerator 1 t v = groupedNumerator0 t v := by
  unfold HTGeometry.evenCompactUnitMomentZeroNumerator groupedNumerator0
  norm_num only [one_pow, mul_one, n0_0_0, n0_1_0, n0_2_0, Int.cast_add, Int.cast_neg, Int.cast_ofNat]
  ring

end
end SQBCompactRow
