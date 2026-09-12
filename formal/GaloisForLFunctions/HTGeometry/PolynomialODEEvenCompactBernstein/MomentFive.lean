module
public import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBernstein.Coefficients
public import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBernstein.GroupedNumerators
public import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBernstein.Basis

/-! Exact coefficient and reconstruction component for the compensated compact last-row margin. -/

@[expose] public section
namespace HTGeometry.EvenCompactBernstein
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem numeratorCoefficient5_reconstruction (t v : ℝ) :
    bernsteinTransform (fun a b => (numeratorCoefficient5 a b : ℝ)) t v =
      groupedNumerator5 t v := by
  change bernsteinTransform (fun a b => ((((((((tensorIntegerCoefficient n5_0_0Certificate.value 0 0 a b) +
    ((tensorIntegerCoefficient n5_1_0Certificate.value 1 0 a b) +
    (tensorIntegerCoefficient n5_2_0Certificate.value 2 0 a b))) +
    (((tensorIntegerCoefficient n5_3_0Certificate.value 3 0 a b) +
    (tensorIntegerCoefficient n5_4_0Certificate.value 4 0 a b)) +
    ((tensorIntegerCoefficient n5_5_0Certificate.value 5 0 a b) +
    (tensorIntegerCoefficient n5_6_0Certificate.value 6 0 a b)))) +
    (((tensorIntegerCoefficient n5_7_0Certificate.value 7 0 a b) +
    ((tensorIntegerCoefficient n5_0_1Certificate.value 0 1 a b) +
    (tensorIntegerCoefficient n5_0_2Certificate.value 0 2 a b))) +
    (((tensorIntegerCoefficient n5_1_1Certificate.value 1 1 a b) +
    (tensorIntegerCoefficient n5_1_2Certificate.value 1 2 a b)) +
    ((tensorIntegerCoefficient n5_2_1Certificate.value 2 1 a b) +
    (tensorIntegerCoefficient n5_2_2Certificate.value 2 2 a b))))) +
    ((((tensorIntegerCoefficient n5_3_1Certificate.value 3 1 a b) +
    ((tensorIntegerCoefficient n5_3_2Certificate.value 3 2 a b) +
    (tensorIntegerCoefficient n5_4_1Certificate.value 4 1 a b))) +
    (((tensorIntegerCoefficient n5_4_2Certificate.value 4 2 a b) +
    (tensorIntegerCoefficient n5_5_1Certificate.value 5 1 a b)) +
    ((tensorIntegerCoefficient n5_5_2Certificate.value 5 2 a b) +
    (tensorIntegerCoefficient n5_6_1Certificate.value 6 1 a b)))) +
    (((tensorIntegerCoefficient n5_6_2Certificate.value 6 2 a b) +
    ((tensorIntegerCoefficient n5_0_3Certificate.value 0 3 a b) +
    (tensorIntegerCoefficient n5_0_4Certificate.value 0 4 a b))) +
    (((tensorIntegerCoefficient n5_1_3Certificate.value 1 3 a b) +
    (tensorIntegerCoefficient n5_1_4Certificate.value 1 4 a b)) +
    ((tensorIntegerCoefficient n5_2_3Certificate.value 2 3 a b) +
    (tensorIntegerCoefficient n5_2_4Certificate.value 2 4 a b)))))) +
    (((((tensorIntegerCoefficient n5_3_3Certificate.value 3 3 a b) +
    ((tensorIntegerCoefficient n5_3_4Certificate.value 3 4 a b) +
    (tensorIntegerCoefficient n5_4_3Certificate.value 4 3 a b))) +
    (((tensorIntegerCoefficient n5_4_4Certificate.value 4 4 a b) +
    (tensorIntegerCoefficient n5_5_3Certificate.value 5 3 a b)) +
    ((tensorIntegerCoefficient n5_5_4Certificate.value 5 4 a b) +
    (tensorIntegerCoefficient n5_0_5Certificate.value 0 5 a b)))) +
    (((tensorIntegerCoefficient n5_0_6Certificate.value 0 6 a b) +
    ((tensorIntegerCoefficient n5_1_5Certificate.value 1 5 a b) +
    (tensorIntegerCoefficient n5_1_6Certificate.value 1 6 a b))) +
    (((tensorIntegerCoefficient n5_2_5Certificate.value 2 5 a b) +
    (tensorIntegerCoefficient n5_2_6Certificate.value 2 6 a b)) +
    ((tensorIntegerCoefficient n5_3_5Certificate.value 3 5 a b) +
    (tensorIntegerCoefficient n5_3_6Certificate.value 3 6 a b))))) +
    ((((tensorIntegerCoefficient n5_4_5Certificate.value 4 5 a b) +
    ((tensorIntegerCoefficient n5_4_6Certificate.value 4 6 a b) +
    (tensorIntegerCoefficient n5_0_7Certificate.value 0 7 a b))) +
    (((tensorIntegerCoefficient n5_0_8Certificate.value 0 8 a b) +
    (tensorIntegerCoefficient n5_1_7Certificate.value 1 7 a b)) +
    ((tensorIntegerCoefficient n5_1_8Certificate.value 1 8 a b) +
    (tensorIntegerCoefficient n5_2_7Certificate.value 2 7 a b)))) +
    ((((tensorIntegerCoefficient n5_2_8Certificate.value 2 8 a b) +
    (tensorIntegerCoefficient n5_3_7Certificate.value 3 7 a b)) +
    ((tensorIntegerCoefficient n5_3_8Certificate.value 3 8 a b) +
    (tensorIntegerCoefficient n5_0_9Certificate.value 0 9 a b))) +
    (((tensorIntegerCoefficient n5_0_10Certificate.value 0 10 a b) +
    (tensorIntegerCoefficient n5_1_9Certificate.value 1 9 a b)) +
    ((tensorIntegerCoefficient n5_1_10Certificate.value 1 10 a b) +
    (tensorIntegerCoefficient n5_2_9Certificate.value 2 9 a b))))))) : ℤ) : ℝ)) t v = _
  simp only [bernsteinTransform_integer_add]
  rw [tensorIntegerCoefficient_reconstruction n5_0_0Certificate.value 0 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_1_0Certificate.value 1 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_2_0Certificate.value 2 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_3_0Certificate.value 3 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_4_0Certificate.value 4 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_5_0Certificate.value 5 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_6_0Certificate.value 6 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_7_0Certificate.value 7 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_0_1Certificate.value 0 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_0_2Certificate.value 0 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_1_1Certificate.value 1 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_1_2Certificate.value 1 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_2_1Certificate.value 2 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_2_2Certificate.value 2 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_3_1Certificate.value 3 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_3_2Certificate.value 3 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_4_1Certificate.value 4 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_4_2Certificate.value 4 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_5_1Certificate.value 5 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_5_2Certificate.value 5 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_6_1Certificate.value 6 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_6_2Certificate.value 6 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_0_3Certificate.value 0 3 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_0_4Certificate.value 0 4 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_1_3Certificate.value 1 3 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_1_4Certificate.value 1 4 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_2_3Certificate.value 2 3 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_2_4Certificate.value 2 4 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_3_3Certificate.value 3 3 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_3_4Certificate.value 3 4 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_4_3Certificate.value 4 3 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_4_4Certificate.value 4 4 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_5_3Certificate.value 5 3 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_5_4Certificate.value 5 4 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_0_5Certificate.value 0 5 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_0_6Certificate.value 0 6 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_1_5Certificate.value 1 5 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_1_6Certificate.value 1 6 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_2_5Certificate.value 2 5 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_2_6Certificate.value 2 6 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_3_5Certificate.value 3 5 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_3_6Certificate.value 3 6 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_4_5Certificate.value 4 5 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_4_6Certificate.value 4 6 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_0_7Certificate.value 0 7 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_0_8Certificate.value 0 8 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_1_7Certificate.value 1 7 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_1_8Certificate.value 1 8 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_2_7Certificate.value 2 7 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_2_8Certificate.value 2 8 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_3_7Certificate.value 3 7 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_3_8Certificate.value 3 8 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_0_9Certificate.value 0 9 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_0_10Certificate.value 0 10 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_1_9Certificate.value 1 9 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_1_10Certificate.value 1 10 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n5_2_9Certificate.value 2 9 (by omega) (by omega)]
  rw [← n5_0_0Certificate.eq_value, ← n5_1_0Certificate.eq_value, ← n5_2_0Certificate.eq_value, ← n5_3_0Certificate.eq_value, ← n5_4_0Certificate.eq_value, ← n5_5_0Certificate.eq_value, ← n5_6_0Certificate.eq_value, ← n5_7_0Certificate.eq_value, ← n5_0_1Certificate.eq_value, ← n5_0_2Certificate.eq_value, ← n5_1_1Certificate.eq_value, ← n5_1_2Certificate.eq_value, ← n5_2_1Certificate.eq_value, ← n5_2_2Certificate.eq_value, ← n5_3_1Certificate.eq_value, ← n5_3_2Certificate.eq_value, ← n5_4_1Certificate.eq_value, ← n5_4_2Certificate.eq_value, ← n5_5_1Certificate.eq_value, ← n5_5_2Certificate.eq_value, ← n5_6_1Certificate.eq_value, ← n5_6_2Certificate.eq_value, ← n5_0_3Certificate.eq_value, ← n5_0_4Certificate.eq_value, ← n5_1_3Certificate.eq_value, ← n5_1_4Certificate.eq_value, ← n5_2_3Certificate.eq_value, ← n5_2_4Certificate.eq_value, ← n5_3_3Certificate.eq_value, ← n5_3_4Certificate.eq_value, ← n5_4_3Certificate.eq_value, ← n5_4_4Certificate.eq_value, ← n5_5_3Certificate.eq_value, ← n5_5_4Certificate.eq_value, ← n5_0_5Certificate.eq_value, ← n5_0_6Certificate.eq_value, ← n5_1_5Certificate.eq_value, ← n5_1_6Certificate.eq_value, ← n5_2_5Certificate.eq_value, ← n5_2_6Certificate.eq_value, ← n5_3_5Certificate.eq_value, ← n5_3_6Certificate.eq_value, ← n5_4_5Certificate.eq_value, ← n5_4_6Certificate.eq_value, ← n5_0_7Certificate.eq_value, ← n5_0_8Certificate.eq_value, ← n5_1_7Certificate.eq_value, ← n5_1_8Certificate.eq_value, ← n5_2_7Certificate.eq_value, ← n5_2_8Certificate.eq_value, ← n5_3_7Certificate.eq_value, ← n5_3_8Certificate.eq_value, ← n5_0_9Certificate.eq_value, ← n5_0_10Certificate.eq_value, ← n5_1_9Certificate.eq_value, ← n5_1_10Certificate.eq_value, ← n5_2_9Certificate.eq_value]
  rfl

end
end HTGeometry.EvenCompactBernstein
