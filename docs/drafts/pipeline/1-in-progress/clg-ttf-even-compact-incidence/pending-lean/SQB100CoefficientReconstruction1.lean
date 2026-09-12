module
public import SQB100CoefficientCore
public import SQB100GroupedNumerators
public import SQB100BernsteinTransform

@[expose] public section
namespace SQBCompactRow
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem numeratorCoefficient1_reconstruction (t v : ℝ) :
    bernsteinTransform (fun a b => (numeratorCoefficient1 a b : ℝ)) t v =
      groupedNumerator1 t v := by
  change bernsteinTransform (fun a b => ((((((tensorIntegerCoefficient n1_0_0Certificate.value 0 0 a b) +
    (tensorIntegerCoefficient n1_1_0Certificate.value 1 0 a b)) +
    ((tensorIntegerCoefficient n1_2_0Certificate.value 2 0 a b) +
    (tensorIntegerCoefficient n1_3_0Certificate.value 3 0 a b))) +
    (((tensorIntegerCoefficient n1_0_1Certificate.value 0 1 a b) +
    (tensorIntegerCoefficient n1_0_2Certificate.value 0 2 a b)) +
    ((tensorIntegerCoefficient n1_1_1Certificate.value 1 1 a b) +
    ((tensorIntegerCoefficient n1_1_2Certificate.value 1 2 a b) +
    (tensorIntegerCoefficient n1_2_1Certificate.value 2 1 a b))))) : ℤ) : ℝ)) t v = _
  simp only [bernsteinTransform_integer_add]
  rw [tensorIntegerCoefficient_reconstruction n1_0_0Certificate.value 0 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n1_1_0Certificate.value 1 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n1_2_0Certificate.value 2 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n1_3_0Certificate.value 3 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n1_0_1Certificate.value 0 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n1_0_2Certificate.value 0 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n1_1_1Certificate.value 1 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n1_1_2Certificate.value 1 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n1_2_1Certificate.value 2 1 (by omega) (by omega)]
  rw [← n1_0_0Certificate.eq_value, ← n1_1_0Certificate.eq_value, ← n1_2_0Certificate.eq_value, ← n1_3_0Certificate.eq_value, ← n1_0_1Certificate.eq_value, ← n1_0_2Certificate.eq_value, ← n1_1_1Certificate.eq_value, ← n1_1_2Certificate.eq_value, ← n1_2_1Certificate.eq_value]
  rfl

end
end SQBCompactRow
