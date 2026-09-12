module
public import SQB100CoefficientCore
public import SQB100GroupedNumerators
public import SQB100BernsteinTransform

@[expose] public section
namespace SQBCompactRow
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem numeratorCoefficient3_reconstruction (t v : ℝ) :
    bernsteinTransform (fun a b => (numeratorCoefficient3 a b : ℝ)) t v =
      groupedNumerator3 t v := by
  change bernsteinTransform (fun a b => (((((((tensorIntegerCoefficient n3_0_0Certificate.value 0 0 a b) +
    ((tensorIntegerCoefficient n3_1_0Certificate.value 1 0 a b) +
    (tensorIntegerCoefficient n3_2_0Certificate.value 2 0 a b))) +
    (((tensorIntegerCoefficient n3_3_0Certificate.value 3 0 a b) +
    (tensorIntegerCoefficient n3_4_0Certificate.value 4 0 a b)) +
    ((tensorIntegerCoefficient n3_5_0Certificate.value 5 0 a b) +
    (tensorIntegerCoefficient n3_0_1Certificate.value 0 1 a b)))) +
    (((tensorIntegerCoefficient n3_0_2Certificate.value 0 2 a b) +
    ((tensorIntegerCoefficient n3_1_1Certificate.value 1 1 a b) +
    (tensorIntegerCoefficient n3_1_2Certificate.value 1 2 a b))) +
    (((tensorIntegerCoefficient n3_2_1Certificate.value 2 1 a b) +
    (tensorIntegerCoefficient n3_2_2Certificate.value 2 2 a b)) +
    ((tensorIntegerCoefficient n3_3_1Certificate.value 3 1 a b) +
    (tensorIntegerCoefficient n3_3_2Certificate.value 3 2 a b))))) +
    ((((tensorIntegerCoefficient n3_4_1Certificate.value 4 1 a b) +
    ((tensorIntegerCoefficient n3_4_2Certificate.value 4 2 a b) +
    (tensorIntegerCoefficient n3_0_3Certificate.value 0 3 a b))) +
    (((tensorIntegerCoefficient n3_0_4Certificate.value 0 4 a b) +
    (tensorIntegerCoefficient n3_1_3Certificate.value 1 3 a b)) +
    ((tensorIntegerCoefficient n3_1_4Certificate.value 1 4 a b) +
    (tensorIntegerCoefficient n3_2_3Certificate.value 2 3 a b)))) +
    ((((tensorIntegerCoefficient n3_2_4Certificate.value 2 4 a b) +
    (tensorIntegerCoefficient n3_3_3Certificate.value 3 3 a b)) +
    ((tensorIntegerCoefficient n3_3_4Certificate.value 3 4 a b) +
    (tensorIntegerCoefficient n3_0_5Certificate.value 0 5 a b))) +
    (((tensorIntegerCoefficient n3_0_6Certificate.value 0 6 a b) +
    (tensorIntegerCoefficient n3_1_5Certificate.value 1 5 a b)) +
    ((tensorIntegerCoefficient n3_1_6Certificate.value 1 6 a b) +
    (tensorIntegerCoefficient n3_2_5Certificate.value 2 5 a b)))))) : ℤ) : ℝ)) t v = _
  simp only [bernsteinTransform_integer_add]
  rw [tensorIntegerCoefficient_reconstruction n3_0_0Certificate.value 0 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_1_0Certificate.value 1 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_2_0Certificate.value 2 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_3_0Certificate.value 3 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_4_0Certificate.value 4 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_5_0Certificate.value 5 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_0_1Certificate.value 0 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_0_2Certificate.value 0 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_1_1Certificate.value 1 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_1_2Certificate.value 1 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_2_1Certificate.value 2 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_2_2Certificate.value 2 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_3_1Certificate.value 3 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_3_2Certificate.value 3 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_4_1Certificate.value 4 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_4_2Certificate.value 4 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_0_3Certificate.value 0 3 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_0_4Certificate.value 0 4 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_1_3Certificate.value 1 3 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_1_4Certificate.value 1 4 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_2_3Certificate.value 2 3 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_2_4Certificate.value 2 4 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_3_3Certificate.value 3 3 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_3_4Certificate.value 3 4 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_0_5Certificate.value 0 5 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_0_6Certificate.value 0 6 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_1_5Certificate.value 1 5 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_1_6Certificate.value 1 6 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n3_2_5Certificate.value 2 5 (by omega) (by omega)]
  rw [← n3_0_0Certificate.eq_value, ← n3_1_0Certificate.eq_value, ← n3_2_0Certificate.eq_value, ← n3_3_0Certificate.eq_value, ← n3_4_0Certificate.eq_value, ← n3_5_0Certificate.eq_value, ← n3_0_1Certificate.eq_value, ← n3_0_2Certificate.eq_value, ← n3_1_1Certificate.eq_value, ← n3_1_2Certificate.eq_value, ← n3_2_1Certificate.eq_value, ← n3_2_2Certificate.eq_value, ← n3_3_1Certificate.eq_value, ← n3_3_2Certificate.eq_value, ← n3_4_1Certificate.eq_value, ← n3_4_2Certificate.eq_value, ← n3_0_3Certificate.eq_value, ← n3_0_4Certificate.eq_value, ← n3_1_3Certificate.eq_value, ← n3_1_4Certificate.eq_value, ← n3_2_3Certificate.eq_value, ← n3_2_4Certificate.eq_value, ← n3_3_3Certificate.eq_value, ← n3_3_4Certificate.eq_value, ← n3_0_5Certificate.eq_value, ← n3_0_6Certificate.eq_value, ← n3_1_5Certificate.eq_value, ← n3_1_6Certificate.eq_value, ← n3_2_5Certificate.eq_value]
  rfl

end
end SQBCompactRow
