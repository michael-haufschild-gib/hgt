import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactUnitCoordinates
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapPowers
import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactReflected2

/-! # Exact coupled-coordinate signed even moment 1 -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The signed even moment in fixed units, retaining the actual coupled source parameters. -/
def evenCompactUnitMomentOne (r t v : ℝ) : ℝ :=
  (((((25725911/102400000 : ℝ) +
    ((364323/102400000 : ℝ)*t^(1 : ℕ) +
    (1413/102400000 : ℝ)*t^(2 : ℕ))) +
    (((1/102400000 : ℝ)*t^(3 : ℕ) +
    (-1667419/28800000 : ℝ)*r^(1 : ℕ)) +
    ((89579/7680000 : ℝ)*r^(1 : ℕ)*v^(1 : ℕ) +
    (573/256000 : ℝ)*r^(1 : ℕ)*v^(2 : ℕ)))) +
    ((((537883/14400000 : ℝ)*r^(1 : ℕ)*t^(1 : ℕ) +
    (139/3840000 : ℝ)*r^(1 : ℕ)*t^(1 : ℕ)*v^(1 : ℕ)) +
    ((3/256000 : ℝ)*r^(1 : ℕ)*t^(1 : ℕ)*v^(2 : ℕ) +
    (2111/7200000 : ℝ)*r^(1 : ℕ)*t^(2 : ℕ))) +
    (((-1/7680000 : ℝ)*r^(1 : ℕ)*t^(2 : ℕ)*v^(1 : ℕ) +
    (1/3200000 : ℝ)*r^(1 : ℕ)*t^(3 : ℕ)) +
    ((18673/6400000 : ℝ)*r^(2 : ℕ) +
    (-15509/5760000 : ℝ)*r^(2 : ℕ)*v^(1 : ℕ))))) +
    (((((-407/768000 : ℝ)*r^(2 : ℕ)*v^(2 : ℕ) +
    (-1097491/172800000 : ℝ)*r^(2 : ℕ)*t^(1 : ℕ)) +
    ((49/128000 : ℝ)*r^(2 : ℕ)*t^(1 : ℕ)*v^(1 : ℕ) +
    (19/153600 : ℝ)*r^(2 : ℕ)*t^(1 : ℕ)*v^(2 : ℕ))) +
    (((4171/2700000 : ℝ)*r^(2 : ℕ)*t^(2 : ℕ) +
    (-1/360000 : ℝ)*r^(2 : ℕ)*t^(2 : ℕ)*v^(1 : ℕ)) +
    ((1/300000 : ℝ)*r^(2 : ℕ)*t^(3 : ℕ) +
    (1591/32400000 : ℝ)*r^(3 : ℕ)))) +
    ((((37/240000 : ℝ)*r^(3 : ℕ)*v^(1 : ℕ) +
    (1/32000 : ℝ)*r^(3 : ℕ)*v^(2 : ℕ)) +
    ((389/1800000 : ℝ)*r^(3 : ℕ)*t^(1 : ℕ) +
    (-19/540000 : ℝ)*r^(3 : ℕ)*t^(1 : ℕ)*v^(1 : ℕ))) +
    (((-1/72000 : ℝ)*r^(3 : ℕ)*t^(1 : ℕ)*v^(2 : ℕ) +
    (-34/253125 : ℝ)*r^(3 : ℕ)*t^(2 : ℕ)) +
    ((-1/67500 : ℝ)*r^(3 : ℕ)*t^(2 : ℕ)*v^(1 : ℕ) +
    (1/84375 : ℝ)*r^(3 : ℕ)*t^(3 : ℕ))))))

/-- Exact drift-square substitution; this identity assumes no sign or approximation. -/
theorem evenCompactUnitMomentOne_eq (u t v : ℝ) :
    (-1 : ℝ)^(1 : ℕ)*(oddCompactReflectedScalar2 u (evenCompactUnitGap (u^(2 : ℕ)) t) (u*(1+v/4)))/(100 : ℝ)^(1 : ℕ) = evenCompactUnitMomentOne (u^(2 : ℕ)) t v := by
  unfold oddCompactReflectedScalar2
  rw [evenCompactUnitGap_pow_two, evenCompactUnitGap_pow_three]
  unfold evenCompactUnitGap evenCompactUnitGapPow2 evenCompactUnitGapPow3 evenCompactUnitMomentOne
  ring

end
end HTGeometry
