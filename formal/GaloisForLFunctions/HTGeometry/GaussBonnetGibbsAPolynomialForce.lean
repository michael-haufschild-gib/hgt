import GaloisForLFunctions.HTGeometry.GaussBonnetGibbsAGauge

/-!
# Exact polynomial numerator of the physical Gibbs force

The logarithmic entropy derivative cancels the extra thermal denominator.
The resulting quartic controls the actual radial Gibbs derivative for
both signs of electric charge and coupling-root data.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

def egbOffShellGibbsARadialNumerator (P T Q a r : ℝ) : ℝ :=
  8 * Real.pi * P * r ^ (4 : ℕ) - 4 * Real.pi * T * r ^ (3 : ℕ) + r ^ (2 : ℕ) -
    8 * Real.pi * T * a ^ (2 : ℕ) * r - (Q ^ (2 : ℕ) + a ^ (2 : ℕ))

theorem egbOffShellGibbsA_polynomial_derivative (P T Q a l u : ℝ) :
    HasDerivAt (egbOffShellGibbsA P T Q a l)
      (egbOffShellGibbsARadialNumerator P T Q a (exp u) / (2 * exp u ^ (2 : ℕ))) (exp u) := by
  have hu := exp_pos u
  have hpi := Real.pi_pos
  have hD : 0 < exp u ^ (2 : ℕ) + 2 * a ^ (2 : ℕ) := by positivity
  have h := egbOffShellGibbsA_radius_derivative P T Q a l u
  apply h.congr_deriv
  unfold egbTemperatureA egbOffShellGibbsARadialNumerator
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry
