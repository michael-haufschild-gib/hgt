module
public import SQB100CoefficientCore
public import SQB100GroupedNumerators
public import SQB100BernsteinTransform

@[expose] public section
namespace SQBCompactRow
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem numeratorCoefficient4_reconstruction (t v : ℝ) :
    bernsteinTransform (fun a b => (numeratorCoefficient4 a b : ℝ)) t v =
      groupedNumerator4 t v := by
  change bernsteinTransform (fun a b => ((((((((tensorIntegerCoefficient n4_0_0Certificate.value 0 0 a b) +
    (tensorIntegerCoefficient n4_1_0Certificate.value 1 0 a b)) +
    ((tensorIntegerCoefficient n4_2_0Certificate.value 2 0 a b) +
    ((tensorIntegerCoefficient n4_3_0Certificate.value 3 0 a b) +
    (tensorIntegerCoefficient n4_4_0Certificate.value 4 0 a b)))) +
    (((tensorIntegerCoefficient n4_5_0Certificate.value 5 0 a b) +
    (tensorIntegerCoefficient n4_6_0Certificate.value 6 0 a b)) +
    ((tensorIntegerCoefficient n4_0_1Certificate.value 0 1 a b) +
    ((tensorIntegerCoefficient n4_0_2Certificate.value 0 2 a b) +
    (tensorIntegerCoefficient n4_1_1Certificate.value 1 1 a b))))) +
    ((((tensorIntegerCoefficient n4_1_2Certificate.value 1 2 a b) +
    (tensorIntegerCoefficient n4_2_1Certificate.value 2 1 a b)) +
    ((tensorIntegerCoefficient n4_2_2Certificate.value 2 2 a b) +
    ((tensorIntegerCoefficient n4_3_1Certificate.value 3 1 a b) +
    (tensorIntegerCoefficient n4_3_2Certificate.value 3 2 a b)))) +
    (((tensorIntegerCoefficient n4_4_1Certificate.value 4 1 a b) +
    ((tensorIntegerCoefficient n4_4_2Certificate.value 4 2 a b) +
    (tensorIntegerCoefficient n4_5_1Certificate.value 5 1 a b))) +
    ((tensorIntegerCoefficient n4_5_2Certificate.value 5 2 a b) +
    ((tensorIntegerCoefficient n4_0_3Certificate.value 0 3 a b) +
    (tensorIntegerCoefficient n4_0_4Certificate.value 0 4 a b)))))) +
    (((((tensorIntegerCoefficient n4_1_3Certificate.value 1 3 a b) +
    (tensorIntegerCoefficient n4_1_4Certificate.value 1 4 a b)) +
    ((tensorIntegerCoefficient n4_2_3Certificate.value 2 3 a b) +
    ((tensorIntegerCoefficient n4_2_4Certificate.value 2 4 a b) +
    (tensorIntegerCoefficient n4_3_3Certificate.value 3 3 a b)))) +
    (((tensorIntegerCoefficient n4_3_4Certificate.value 3 4 a b) +
    (tensorIntegerCoefficient n4_4_3Certificate.value 4 3 a b)) +
    ((tensorIntegerCoefficient n4_4_4Certificate.value 4 4 a b) +
    ((tensorIntegerCoefficient n4_0_5Certificate.value 0 5 a b) +
    (tensorIntegerCoefficient n4_0_6Certificate.value 0 6 a b))))) +
    ((((tensorIntegerCoefficient n4_1_5Certificate.value 1 5 a b) +
    (tensorIntegerCoefficient n4_1_6Certificate.value 1 6 a b)) +
    ((tensorIntegerCoefficient n4_2_5Certificate.value 2 5 a b) +
    ((tensorIntegerCoefficient n4_2_6Certificate.value 2 6 a b) +
    (tensorIntegerCoefficient n4_3_5Certificate.value 3 5 a b)))) +
    (((tensorIntegerCoefficient n4_3_6Certificate.value 3 6 a b) +
    ((tensorIntegerCoefficient n4_0_7Certificate.value 0 7 a b) +
    (tensorIntegerCoefficient n4_0_8Certificate.value 0 8 a b))) +
    ((tensorIntegerCoefficient n4_1_7Certificate.value 1 7 a b) +
    ((tensorIntegerCoefficient n4_1_8Certificate.value 1 8 a b) +
    (tensorIntegerCoefficient n4_2_7Certificate.value 2 7 a b))))))) : ℤ) : ℝ)) t v = _
  simp only [bernsteinTransform_integer_add]
  rw [tensorIntegerCoefficient_reconstruction n4_0_0Certificate.value 0 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_1_0Certificate.value 1 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_2_0Certificate.value 2 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_3_0Certificate.value 3 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_4_0Certificate.value 4 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_5_0Certificate.value 5 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_6_0Certificate.value 6 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_0_1Certificate.value 0 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_0_2Certificate.value 0 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_1_1Certificate.value 1 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_1_2Certificate.value 1 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_2_1Certificate.value 2 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_2_2Certificate.value 2 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_3_1Certificate.value 3 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_3_2Certificate.value 3 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_4_1Certificate.value 4 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_4_2Certificate.value 4 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_5_1Certificate.value 5 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_5_2Certificate.value 5 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_0_3Certificate.value 0 3 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_0_4Certificate.value 0 4 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_1_3Certificate.value 1 3 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_1_4Certificate.value 1 4 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_2_3Certificate.value 2 3 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_2_4Certificate.value 2 4 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_3_3Certificate.value 3 3 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_3_4Certificate.value 3 4 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_4_3Certificate.value 4 3 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_4_4Certificate.value 4 4 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_0_5Certificate.value 0 5 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_0_6Certificate.value 0 6 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_1_5Certificate.value 1 5 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_1_6Certificate.value 1 6 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_2_5Certificate.value 2 5 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_2_6Certificate.value 2 6 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_3_5Certificate.value 3 5 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_3_6Certificate.value 3 6 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_0_7Certificate.value 0 7 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_0_8Certificate.value 0 8 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_1_7Certificate.value 1 7 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_1_8Certificate.value 1 8 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n4_2_7Certificate.value 2 7 (by omega) (by omega)]
  rw [← n4_0_0Certificate.eq_value, ← n4_1_0Certificate.eq_value, ← n4_2_0Certificate.eq_value, ← n4_3_0Certificate.eq_value, ← n4_4_0Certificate.eq_value, ← n4_5_0Certificate.eq_value, ← n4_6_0Certificate.eq_value, ← n4_0_1Certificate.eq_value, ← n4_0_2Certificate.eq_value, ← n4_1_1Certificate.eq_value, ← n4_1_2Certificate.eq_value, ← n4_2_1Certificate.eq_value, ← n4_2_2Certificate.eq_value, ← n4_3_1Certificate.eq_value, ← n4_3_2Certificate.eq_value, ← n4_4_1Certificate.eq_value, ← n4_4_2Certificate.eq_value, ← n4_5_1Certificate.eq_value, ← n4_5_2Certificate.eq_value, ← n4_0_3Certificate.eq_value, ← n4_0_4Certificate.eq_value, ← n4_1_3Certificate.eq_value, ← n4_1_4Certificate.eq_value, ← n4_2_3Certificate.eq_value, ← n4_2_4Certificate.eq_value, ← n4_3_3Certificate.eq_value, ← n4_3_4Certificate.eq_value, ← n4_4_3Certificate.eq_value, ← n4_4_4Certificate.eq_value, ← n4_0_5Certificate.eq_value, ← n4_0_6Certificate.eq_value, ← n4_1_5Certificate.eq_value, ← n4_1_6Certificate.eq_value, ← n4_2_5Certificate.eq_value, ← n4_2_6Certificate.eq_value, ← n4_3_5Certificate.eq_value, ← n4_3_6Certificate.eq_value, ← n4_0_7Certificate.eq_value, ← n4_0_8Certificate.eq_value, ← n4_1_7Certificate.eq_value, ← n4_1_8Certificate.eq_value, ← n4_2_7Certificate.eq_value]
  rfl

end
end SQBCompactRow
