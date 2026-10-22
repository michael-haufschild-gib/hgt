import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactMomentZero

/-! # Exact integer numerator for compact even moment zero -/
namespace HTGeometry
noncomputable section
set_option maxRecDepth 100000

/-- One positive common denominator separates scalar arithmetic from polynomial expansion. -/
def evenCompactUnitMomentZeroNumerator (r t _v : ℝ) : ℝ :=
  ((((154449 : ℝ) +
    (2358 : ℝ)*t^(1 : ℕ) : ℝ) +
    ((9 : ℝ)*t^(2 : ℕ) +
    (-40872 : ℝ)*r^(1 : ℕ) : ℝ) : ℝ) +
    (((24840 : ℝ)*r^(1 : ℕ)*t^(1 : ℕ) +
    (192 : ℝ)*r^(1 : ℕ)*t^(2 : ℕ) : ℝ) +
    ((2704 : ℝ)*r^(2 : ℕ) +
    ((-3328 : ℝ)*r^(2 : ℕ)*t^(1 : ℕ) +
    (1024 : ℝ)*r^(2 : ℕ)*t^(2 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ)

/-- Exact symbolic equality with the previously proved normalized source moment. -/
theorem evenCompactUnitMomentZero_eq_numerator (r t v : ℝ) :
    evenCompactUnitMomentZero r t v = evenCompactUnitMomentZeroNumerator r t v / (230400 : ℝ) := by
  unfold evenCompactUnitMomentZero evenCompactUnitMomentZeroNumerator
  ring

end
end HTGeometry
