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

theorem numeratorCoefficient2_reconstruction (t v : ℝ) :
    bernsteinTransform (fun a b => (numeratorCoefficient2 a b : ℝ)) t v =
      groupedNumerator2 t v := by
  change bernsteinTransform (fun a b => (((((((tensorIntegerCoefficient n2_0_0Certificate.value 0 0 a b) +
    (tensorIntegerCoefficient n2_1_0Certificate.value 1 0 a b)) +
    ((tensorIntegerCoefficient n2_2_0Certificate.value 2 0 a b) +
    (tensorIntegerCoefficient n2_3_0Certificate.value 3 0 a b))) +
    (((tensorIntegerCoefficient n2_4_0Certificate.value 4 0 a b) +
    (tensorIntegerCoefficient n2_0_1Certificate.value 0 1 a b)) +
    ((tensorIntegerCoefficient n2_0_2Certificate.value 0 2 a b) +
    ((tensorIntegerCoefficient n2_1_1Certificate.value 1 1 a b) +
    (tensorIntegerCoefficient n2_1_2Certificate.value 1 2 a b))))) +
    ((((tensorIntegerCoefficient n2_2_1Certificate.value 2 1 a b) +
    (tensorIntegerCoefficient n2_2_2Certificate.value 2 2 a b)) +
    ((tensorIntegerCoefficient n2_3_1Certificate.value 3 1 a b) +
    (tensorIntegerCoefficient n2_3_2Certificate.value 3 2 a b))) +
    (((tensorIntegerCoefficient n2_0_3Certificate.value 0 3 a b) +
    (tensorIntegerCoefficient n2_0_4Certificate.value 0 4 a b)) +
    ((tensorIntegerCoefficient n2_1_3Certificate.value 1 3 a b) +
    ((tensorIntegerCoefficient n2_1_4Certificate.value 1 4 a b) +
    (tensorIntegerCoefficient n2_2_3Certificate.value 2 3 a b)))))) : ℤ) : ℝ)) t v = _
  simp only [bernsteinTransform_integer_add]
  rw [tensorIntegerCoefficient_reconstruction n2_0_0Certificate.value 0 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n2_1_0Certificate.value 1 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n2_2_0Certificate.value 2 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n2_3_0Certificate.value 3 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n2_4_0Certificate.value 4 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n2_0_1Certificate.value 0 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n2_0_2Certificate.value 0 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n2_1_1Certificate.value 1 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n2_1_2Certificate.value 1 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n2_2_1Certificate.value 2 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n2_2_2Certificate.value 2 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n2_3_1Certificate.value 3 1 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n2_3_2Certificate.value 3 2 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n2_0_3Certificate.value 0 3 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n2_0_4Certificate.value 0 4 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n2_1_3Certificate.value 1 3 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n2_1_4Certificate.value 1 4 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n2_2_3Certificate.value 2 3 (by omega) (by omega)]
  rw [← n2_0_0Certificate.eq_value, ← n2_1_0Certificate.eq_value, ← n2_2_0Certificate.eq_value, ← n2_3_0Certificate.eq_value, ← n2_4_0Certificate.eq_value, ← n2_0_1Certificate.eq_value, ← n2_0_2Certificate.eq_value, ← n2_1_1Certificate.eq_value, ← n2_1_2Certificate.eq_value, ← n2_2_1Certificate.eq_value, ← n2_2_2Certificate.eq_value, ← n2_3_1Certificate.eq_value, ← n2_3_2Certificate.eq_value, ← n2_0_3Certificate.eq_value, ← n2_0_4Certificate.eq_value, ← n2_1_3Certificate.eq_value, ← n2_1_4Certificate.eq_value, ← n2_2_3Certificate.eq_value]
  rfl

end
end HTGeometry.EvenCompactBernstein
