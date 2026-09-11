import SQB99CoefficientPublicCore
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentTwoInteger
import Mathlib.Tactic.Ring
namespace SQBCompactRow
noncomputable section
set_option maxHeartbeats 400000

def groupedNumerator2 (t v : ℝ) : ℝ :=
  (((((n2_0_0 : ℝ)*t^(0 : ℕ)*v^(0 : ℕ) +
  (n2_1_0 : ℝ)*t^(1 : ℕ)*v^(0 : ℕ)) +
  ((n2_2_0 : ℝ)*t^(2 : ℕ)*v^(0 : ℕ) +
  (n2_3_0 : ℝ)*t^(3 : ℕ)*v^(0 : ℕ))) +
  (((n2_4_0 : ℝ)*t^(4 : ℕ)*v^(0 : ℕ) +
  (n2_0_1 : ℝ)*t^(0 : ℕ)*v^(1 : ℕ)) +
  ((n2_0_2 : ℝ)*t^(0 : ℕ)*v^(2 : ℕ) +
  ((n2_1_1 : ℝ)*t^(1 : ℕ)*v^(1 : ℕ) +
  (n2_1_2 : ℝ)*t^(1 : ℕ)*v^(2 : ℕ))))) +
  ((((n2_2_1 : ℝ)*t^(2 : ℕ)*v^(1 : ℕ) +
  (n2_2_2 : ℝ)*t^(2 : ℕ)*v^(2 : ℕ)) +
  ((n2_3_1 : ℝ)*t^(3 : ℕ)*v^(1 : ℕ) +
  (n2_3_2 : ℝ)*t^(3 : ℕ)*v^(2 : ℕ))) +
  (((n2_0_3 : ℝ)*t^(0 : ℕ)*v^(3 : ℕ) +
  (n2_0_4 : ℝ)*t^(0 : ℕ)*v^(4 : ℕ)) +
  ((n2_1_3 : ℝ)*t^(1 : ℕ)*v^(3 : ℕ) +
  ((n2_1_4 : ℝ)*t^(1 : ℕ)*v^(4 : ℕ) +
  (n2_2_3 : ℝ)*t^(2 : ℕ)*v^(3 : ℕ))))))

theorem sourceNumerator2_at_one (t v : ℝ) :
  HTGeometry.evenCompactUnitMomentTwoNumerator 1 t v = groupedNumerator2 t v := by
  unfold HTGeometry.evenCompactUnitMomentTwoNumerator groupedNumerator2
  norm_num only [one_pow, mul_one, n2_0_0, n2_1_0, n2_2_0, n2_3_0, n2_4_0, n2_0_1, n2_0_2, n2_1_1, n2_1_2, n2_2_1, n2_2_2, n2_3_1, n2_3_2, n2_0_3, n2_0_4, n2_1_3, n2_1_4, n2_2_3, Int.cast_add, Int.cast_neg, Int.cast_ofNat]
  ring

end
end SQBCompactRow
