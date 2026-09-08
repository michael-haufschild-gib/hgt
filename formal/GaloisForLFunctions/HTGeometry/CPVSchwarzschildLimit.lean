import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge
import Mathlib

/-!
# Exact near-horizon error from the corpus Schwarzschild metric

The first-order Hamiltonian in arXiv:2601.07437, equations (9)--(11),
is obtained directly from the existing Schwarzschild metric in units `G=c=1`.
An exact rational remainder replaces the informal near-horizon approximation.
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV

/-- Radial potential of a positive-mass Schwarzschild source and test particle. -/
def schwarzschildPotential (mu nu q : ℝ) : ℝ :=
  Real.exp mu / 2 * (1 - 2 * Real.exp nu / (2 * Real.exp nu + q))

/-- First-order potential with acceleration `1/(4M)`. -/
def horizonLinearPotential (mu nu q : ℝ) : ℝ :=
  Real.exp mu / (4 * Real.exp nu) * q

/-- Direct attachment to the time-time component of the actual corpus metric. -/
theorem schwarzschildPotential_metric (mu nu x polar : ℝ) :
    schwarzschildPotential mu nu (Real.exp x) =
      -Real.exp mu / 2 *
        schwarzschildBoyerLindquistMetric (Real.exp nu)
          (2 * Real.exp nu + Real.exp x) polar 0 0 := by
  rw [schwarzschildBoyerLindquistMetric_explicit]
  change schwarzschildPotential mu nu (Real.exp x) =
    -Real.exp mu / 2 * (-((2 * Real.exp nu + Real.exp x)^2 -
      2 * Real.exp nu * (2 * Real.exp nu + Real.exp x)) / (2 * Real.exp nu + Real.exp x)^2)
  unfold schwarzschildPotential
  have hr : 2 * Real.exp nu + Real.exp x ≠ 0 := by positivity
  field_simp

/-- Exact first-order error, strictly quadratic in horizon distance. -/
theorem schwarzschildPotential_remainder (mu nu x : ℝ) :
    horizonLinearPotential mu nu (Real.exp x) - schwarzschildPotential mu nu (Real.exp x) =
      Real.exp mu * Real.exp x ^ 2 /
        (4 * Real.exp nu * (2 * Real.exp nu + Real.exp x)) := by
  unfold horizonLinearPotential schwarzschildPotential
  have hr : 2 * Real.exp nu + Real.exp x ≠ 0 := by positivity
  field_simp
  ring

/-- The linear approximation strictly overestimates the exterior potential. -/
theorem schwarzschildPotential_lt_linear (mu nu x : ℝ) :
    schwarzschildPotential mu nu (Real.exp x) < horizonLinearPotential mu nu (Real.exp x) := by
  have h := schwarzschildPotential_remainder mu nu x
  have hp : 0 < Real.exp mu * Real.exp x ^ 2 /
      (4 * Real.exp nu * (2 * Real.exp nu + Real.exp x)) := by positivity
  linarith

/-- Exact lapse factor at every positive horizon distance. -/
theorem schwarzschildPotential_ratio (mu nu x : ℝ) :
    schwarzschildPotential mu nu (Real.exp x) =
      horizonLinearPotential mu nu (Real.exp x) *
        (2 * Real.exp nu / (2 * Real.exp nu + Real.exp x)) := by
  unfold horizonLinearPotential schwarzschildPotential
  have hr : 2 * Real.exp nu + Real.exp x ≠ 0 := by positivity
  field_simp
  ring

/-- The exact exterior potential is positive. -/
theorem schwarzschildPotential_pos (mu nu x : ℝ) :
    0 < schwarzschildPotential mu nu (Real.exp x) := by
  rw [schwarzschildPotential_ratio]
  unfold horizonLinearPotential
  positivity

/-- Explicit uniform quadratic error bound throughout the exterior. -/
theorem schwarzschildPotential_error_bound (mu nu x : ℝ) :
    horizonLinearPotential mu nu (Real.exp x) - schwarzschildPotential mu nu (Real.exp x) ≤
      Real.exp mu * Real.exp x ^ 2 / (8 * Real.exp nu ^ 2) := by
  rw [schwarzschildPotential_remainder]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith [Real.exp_pos nu, Real.exp_pos x, mul_pos (Real.exp_pos nu) (Real.exp_pos x)]

/-- Relative error is exactly the horizon-distance fraction. -/
theorem schwarzschildPotential_relative_error (mu nu x : ℝ) :
    (horizonLinearPotential mu nu (Real.exp x) - schwarzschildPotential mu nu (Real.exp x)) /
      horizonLinearPotential mu nu (Real.exp x) =
        Real.exp x / (2 * Real.exp nu + Real.exp x) := by
  rw [schwarzschildPotential_remainder]
  unfold horizonLinearPotential
  have hr : 2 * Real.exp nu + Real.exp x ≠ 0 := by positivity
  field_simp

/-- Near-horizon scaling removes the complete relative approximation error. -/
theorem schwarzschildPotential_relative_error_tendsto (mu nu : ℝ) :
    Filter.Tendsto (fun t : ℝ =>
      (horizonLinearPotential mu nu (Real.exp (-t)) -
        schwarzschildPotential mu nu (Real.exp (-t))) /
          horizonLinearPotential mu nu (Real.exp (-t))) Filter.atTop (nhds 0) := by
  simp only [schwarzschildPotential_relative_error]
  have h := Real.tendsto_exp_neg_atTop_nhds_zero
  convert! h.div (tendsto_const_nhds.add h) (by positivity : (2 * Real.exp nu + 0) ≠ 0) using 1
  simp

/-- The horizon slope is the test mass times Schwarzschild surface gravity. -/
theorem schwarzschildPotential_hasDerivAt_zero (mu nu : ℝ) :
    HasDerivAt (schwarzschildPotential mu nu) (Real.exp mu / (4 * Real.exp nu)) 0 := by
  have hd : (2 * Real.exp nu + (0 : ℝ)) ≠ 0 := by positivity
  convert! ((hasDerivAt_const 0 (1 : ℝ)).sub
    ((hasDerivAt_const 0 (2 * Real.exp nu)).div
      ((hasDerivAt_id (0 : ℝ)).const_add (2 * Real.exp nu)) hd)).const_mul
        (Real.exp mu / 2) using 1
  dsimp
  field_simp
  ring

end GaloisForLFunctions.HTGeometry.CPV
