import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactUnitCoordinates
import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactModel

/-! # Exact coupled-coordinate signed even moment 0 -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The signed even moment in fixed units, retaining the actual coupled source parameters. -/
def evenCompactUnitMomentZero (r t _v : ℝ) : ℝ :=
  ((((17161/25600 : ℝ) +
    (131/12800 : ℝ)*t^1) +
    ((1/25600 : ℝ)*t^2 +
    (-1703/9600 : ℝ)*r^1)) +
    (((69/640 : ℝ)*r^1*t^1 +
    (1/1200 : ℝ)*r^1*t^2) +
    ((169/14400 : ℝ)*r^2 +
    ((-13/900 : ℝ)*r^2*t^1 +
    (1/225 : ℝ)*r^2*t^2))))

/-- Exact drift-square substitution; this identity assumes no sign or approximation. -/
theorem evenCompactUnitMomentZero_eq (u t v : ℝ) :
    (-1 : ℝ)^0*(oddCompactSourceZero u (evenCompactUnitGap (u^2) t)^2)/(100 : ℝ)^0 = evenCompactUnitMomentZero (u^2) t v := by
  unfold oddCompactSourceZero evenCompactUnitGap evenCompactUnitMomentZero
  ring

end
end HTGeometry
