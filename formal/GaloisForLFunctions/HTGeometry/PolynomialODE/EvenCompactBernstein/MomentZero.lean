module
public import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBernstein.Coefficients
public import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBernstein.GroupedNumerators
public import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBernstein.Basis

/-! Exact coefficient and reconstruction component for the compensated compact last-row margin. -/

@[expose] public section
namespace HTGeometry.EvenCompactBernstein
noncomputable section
set_option maxRecDepth 2048

theorem numeratorCoefficient0_reconstruction (t v : ℝ) :
    bernsteinTransform (fun a b => (numeratorCoefficient0 a b : ℝ)) t v =
      groupedNumerator0 t v := by
  change bernsteinTransform (fun a b => ((((tensorIntegerCoefficient n0_0_0Certificate.value 0 0 a b) +
    ((tensorIntegerCoefficient n0_1_0Certificate.value 1 0 a b) +
    (tensorIntegerCoefficient n0_2_0Certificate.value 2 0 a b))) : ℤ) : ℝ)) t v = _
  simp only [bernsteinTransform_integer_add]
  rw [tensorIntegerCoefficient_reconstruction n0_0_0Certificate.value 0 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n0_1_0Certificate.value 1 0 (by omega) (by omega)]
  rw [tensorIntegerCoefficient_reconstruction n0_2_0Certificate.value 2 0 (by omega) (by omega)]
  rw [← n0_0_0Certificate.eq_value, ← n0_1_0Certificate.eq_value, ← n0_2_0Certificate.eq_value]
  rfl

end
end HTGeometry.EvenCompactBernstein
