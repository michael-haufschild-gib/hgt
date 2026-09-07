import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactUnitCoordinates
import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactReflected2

/-! # Exact coupled-coordinate signed even moment 1 -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The signed even moment in fixed units, retaining the actual coupled source parameters. -/
def evenCompactUnitMomentOne (r t v : ℝ) : ℝ :=
  (((((25725911/102400000 : ℝ) +
    ((364323/102400000 : ℝ)*t^1 +
    (1413/102400000 : ℝ)*t^2)) +
    (((1/102400000 : ℝ)*t^3 +
    (-1667419/28800000 : ℝ)*r^1) +
    ((89579/7680000 : ℝ)*r^1*v^1 +
    (573/256000 : ℝ)*r^1*v^2))) +
    ((((537883/14400000 : ℝ)*r^1*t^1 +
    (139/3840000 : ℝ)*r^1*t^1*v^1) +
    ((3/256000 : ℝ)*r^1*t^1*v^2 +
    (2111/7200000 : ℝ)*r^1*t^2)) +
    (((-1/7680000 : ℝ)*r^1*t^2*v^1 +
    (1/3200000 : ℝ)*r^1*t^3) +
    ((18673/6400000 : ℝ)*r^2 +
    (-15509/5760000 : ℝ)*r^2*v^1)))) +
    (((((-407/768000 : ℝ)*r^2*v^2 +
    (-1097491/172800000 : ℝ)*r^2*t^1) +
    ((49/128000 : ℝ)*r^2*t^1*v^1 +
    (19/153600 : ℝ)*r^2*t^1*v^2)) +
    (((4171/2700000 : ℝ)*r^2*t^2 +
    (-1/360000 : ℝ)*r^2*t^2*v^1) +
    ((1/300000 : ℝ)*r^2*t^3 +
    (1591/32400000 : ℝ)*r^3))) +
    ((((37/240000 : ℝ)*r^3*v^1 +
    (1/32000 : ℝ)*r^3*v^2) +
    ((389/1800000 : ℝ)*r^3*t^1 +
    (-19/540000 : ℝ)*r^3*t^1*v^1)) +
    (((-1/72000 : ℝ)*r^3*t^1*v^2 +
    (-34/253125 : ℝ)*r^3*t^2) +
    ((-1/67500 : ℝ)*r^3*t^2*v^1 +
    (1/84375 : ℝ)*r^3*t^3)))))

/-- Exact drift-square substitution; this identity assumes no sign or approximation. -/
theorem evenCompactUnitMomentOne_eq (u t v : ℝ) :
    (-1 : ℝ)^1*(oddCompactReflectedScalar2 u (evenCompactUnitGap (u^2) t) (u*(1+v/4)))/(100 : ℝ)^1 = evenCompactUnitMomentOne (u^2) t v := by
  unfold oddCompactReflectedScalar2 evenCompactUnitGap evenCompactUnitMomentOne
  ring

end
end HTGeometry
