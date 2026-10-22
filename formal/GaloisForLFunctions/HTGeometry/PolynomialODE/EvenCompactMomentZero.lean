import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactUnitCoordinates
import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactModel

/-! # Exact coupled-coordinate signed even moment 0 -/
namespace HTGeometry
noncomputable section
set_option maxRecDepth 100000

/-- The signed even moment in fixed units, retaining the actual coupled source parameters. -/
def evenCompactUnitMomentZero (r t _v : ℝ) : ℝ :=
  ((((17161/25600 : ℝ) +
    (131/12800 : ℝ)*t^(1 : ℕ)) +
    ((1/25600 : ℝ)*t^(2 : ℕ) +
    (-1703/9600 : ℝ)*r^(1 : ℕ))) +
    (((69/640 : ℝ)*r^(1 : ℕ)*t^(1 : ℕ) +
    (1/1200 : ℝ)*r^(1 : ℕ)*t^(2 : ℕ)) +
    ((169/14400 : ℝ)*r^(2 : ℕ) +
    ((-13/900 : ℝ)*r^(2 : ℕ)*t^(1 : ℕ) +
    (1/225 : ℝ)*r^(2 : ℕ)*t^(2 : ℕ)))))

/-- Exact drift-square substitution; this identity assumes no sign or approximation. -/
theorem evenCompactUnitMomentZero_eq (u t v : ℝ) :
    (-1 : ℝ)^(0 : ℕ)*(oddCompactSourceZero u (evenCompactUnitGap (u^(2 : ℕ)) t)^(2 : ℕ))/(100 : ℝ)^(0 : ℕ) = evenCompactUnitMomentZero (u^(2 : ℕ)) t v := by
  unfold oddCompactSourceZero evenCompactUnitGap evenCompactUnitMomentZero
  ring

end
end HTGeometry
