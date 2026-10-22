import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactMomentOne

/-! # Exact integer numerator for compact even moment one -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

/-- One positive common denominator separates scalar arithmetic from polynomial expansion. -/
def evenCompactUnitMomentOneNumerator (r t v : ℝ) : ℝ :=
  (((((2083798791 : ℝ) +
    ((29510163 : ℝ)*t^(1 : ℕ) +
    (114453 : ℝ)*t^(2 : ℕ) : ℝ) : ℝ) +
    (((81 : ℝ)*t^(3 : ℕ) +
    (-480216672 : ℝ)*r^(1 : ℕ) : ℝ) +
    ((96745320 : ℝ)*r^(1 : ℕ)*v^(1 : ℕ) +
    (18565200 : ℝ)*r^(1 : ℕ)*v^(2 : ℕ) : ℝ) : ℝ) : ℝ) +
    ((((309820608 : ℝ)*r^(1 : ℕ)*t^(1 : ℕ) +
    (300240 : ℝ)*r^(1 : ℕ)*t^(1 : ℕ)*v^(1 : ℕ) : ℝ) +
    ((97200 : ℝ)*r^(1 : ℕ)*t^(1 : ℕ)*v^(2 : ℕ) +
    (2431872 : ℝ)*r^(1 : ℕ)*t^(2 : ℕ) : ℝ) : ℝ) +
    (((-1080 : ℝ)*r^(1 : ℕ)*t^(2 : ℕ)*v^(1 : ℕ) +
    (2592 : ℝ)*r^(1 : ℕ)*t^(3 : ℕ) : ℝ) +
    ((24200208 : ℝ)*r^(2 : ℕ) +
    (-22332960 : ℝ)*r^(2 : ℕ)*v^(1 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ) +
    (((((-4395600 : ℝ)*r^(2 : ℕ)*v^(2 : ℕ) +
    (-52679568 : ℝ)*r^(2 : ℕ)*t^(1 : ℕ) : ℝ) +
    ((3175200 : ℝ)*r^(2 : ℕ)*t^(1 : ℕ)*v^(1 : ℕ) +
    (1026000 : ℝ)*r^(2 : ℕ)*t^(1 : ℕ)*v^(2 : ℕ) : ℝ) : ℝ) +
    (((12813312 : ℝ)*r^(2 : ℕ)*t^(2 : ℕ) +
    (-23040 : ℝ)*r^(2 : ℕ)*t^(2 : ℕ)*v^(1 : ℕ) : ℝ) +
    ((27648 : ℝ)*r^(2 : ℕ)*t^(3 : ℕ) +
    (407296 : ℝ)*r^(3 : ℕ) : ℝ) : ℝ) : ℝ) +
    ((((1278720 : ℝ)*r^(3 : ℕ)*v^(1 : ℕ) +
    (259200 : ℝ)*r^(3 : ℕ)*v^(2 : ℕ) : ℝ) +
    ((1792512 : ℝ)*r^(3 : ℕ)*t^(1 : ℕ) +
    (-291840 : ℝ)*r^(3 : ℕ)*t^(1 : ℕ)*v^(1 : ℕ) : ℝ) : ℝ) +
    (((-115200 : ℝ)*r^(3 : ℕ)*t^(1 : ℕ)*v^(2 : ℕ) +
    (-1114112 : ℝ)*r^(3 : ℕ)*t^(2 : ℕ) : ℝ) +
    ((-122880 : ℝ)*r^(3 : ℕ)*t^(2 : ℕ)*v^(1 : ℕ) +
    (98304 : ℝ)*r^(3 : ℕ)*t^(3 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ) : ℝ)

/-- Exact symbolic equality with the previously proved normalized source moment. -/
theorem evenCompactUnitMomentOne_eq_numerator (r t v : ℝ) :
    evenCompactUnitMomentOne r t v = evenCompactUnitMomentOneNumerator r t v / (8294400000 : ℝ) := by
  unfold evenCompactUnitMomentOne evenCompactUnitMomentOneNumerator
  ring

end
end HTGeometry
