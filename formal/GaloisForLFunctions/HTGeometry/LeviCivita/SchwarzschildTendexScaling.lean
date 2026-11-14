import GaloisForLFunctions.HilbertMetric.Geometry.PlanarTendex
import GaloisForLFunctions.HTGeometry.SchwarzschildInformationScaling

/-!
# Point-mass tendex geometry and Schwarzschild lapse scaling

The inverse-cube point-mass coefficient in arXiv:2611.16083 agrees with half
of the corpus's spherical-lapse expression extracted from the Schwarzschild
metric. This identifies its radial eigenvalue, planar trace, determinant, and
mass-independent null directions. At the horizon the entropy-normalized
planar determinant is the universal constant `-π²/2`.

The comparison concerns the explicit point-mass tensor and the metric-derived
lapse expression; it does not supply a Riemann-tensor construction.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Real GaloisForLFunctions.HilbertMetric
open _root_.HTGeometry.NomologicalHomotopyGeometry.FlatCartanHolonomy

/-- Positive inverse-cube point-mass coefficient in logarithmic mass and radius. -/
def schwarzschildTendexCoefficient (m r : ℝ) : ℝ := exp m / exp r ^ 3

theorem schwarzschildTendexCoefficient_pos (m r : ℝ) :
    0 < schwarzschildTendexCoefficient m r := by
  unfold schwarzschildTendexCoefficient
  positivity

/-- Radial stretching equals the spherical-lapse inverse-cube expression. -/
theorem schwarzschildTendex_radial (m r polar : ℝ) :
    (planarTendex (schwarzschildTendexCoefficient m r) (1, 0)).1 =
      schwarzschildInformationCurvature (exp m) (exp r) polar := by
  rw [schwarzschildInformationCurvature_eq]
  unfold planarTendex schwarzschildTendexCoefficient
  dsimp
  ring

/-- The planar trace is half the radial stretching coefficient. -/
theorem schwarzschildTendex_trace (m r polar : ℝ) :
    (planarTendex (schwarzschildTendexCoefficient m r) (1, 0)).1 +
      (planarTendex (schwarzschildTendexCoefficient m r) (0, 1)).2 =
        schwarzschildInformationCurvature (exp m) (exp r) polar / 2 := by
  rw [schwarzschildInformationCurvature_eq]
  unfold planarTendex schwarzschildTendexCoefficient
  dsimp
  ring

/-- Its negative determinant records Lorentzian planar signature. -/
theorem schwarzschildTendex_determinant (m r polar : ℝ) :
    (planarTendex (schwarzschildTendexCoefficient m r) (1, 0)).1 *
      (planarTendex (schwarzschildTendexCoefficient m r) (0, 1)).2 =
        -(schwarzschildInformationCurvature (exp m) (exp r) polar) ^ 2 / 2 := by
  rw [schwarzschildInformationCurvature_eq]
  unfold planarTendex schwarzschildTendexCoefficient
  dsimp
  ring

/-- Positive mass and radius do not change the two null directions. -/
theorem schwarzschildTendex_null_iff (m r : ℝ) (v : ℝ × ℝ) :
    planarTendexForm (schwarzschildTendexCoefficient m r) v v = 0 ↔
      v.2 = sqrt 2 * v.1 ∨ v.2 = -(sqrt 2 * v.1) := by
  have he : schwarzschildTendexCoefficient m r = exp (m - 3 * r) := by
    rw [schwarzschildTendexCoefficient, exp_sub, exp_nat_mul r 3]
  rw [he]
  exact planarTendexForm_null_iff _ v

/-- Entropy removes all mass dependence from the horizon planar determinant. -/
theorem schwarzschildTendex_horizon_entropy_determinant (m polar : ℝ) :
    RHTower.schwarzschildBekensteinHawkingEntropy (exp m) ^ 2 *
      ((planarTendex (schwarzschildTendexCoefficient m (log 2 + m)) (1, 0)).1 *
       (planarTendex (schwarzschildTendexCoefficient m (log 2 + m)) (0, 1)).2) =
        -Real.pi ^ 2 / 2 := by
  rw [schwarzschildTendex_determinant m (log 2 + m) polar]
  have he : exp (log 2 + m) = 2 * exp m := by
    rw [exp_add, exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [he]
  have h := schwarzschildInformationCurvature_entropy_product m polar
  calc
    _ = -(RHTower.schwarzschildBekensteinHawkingEntropy (exp m) *
        schwarzschildInformationCurvature (exp m) (2 * exp m) polar) ^ 2 / 2 := by ring
    _ = _ := by rw [h]

end GaloisForLFunctions.HTGeometry

-- BEGIN PAPER AXIOM AUDIT
#print axioms GaloisForLFunctions.HTGeometry.schwarzschildTendexCoefficient_pos
#print axioms GaloisForLFunctions.HTGeometry.schwarzschildTendex_radial
#print axioms GaloisForLFunctions.HTGeometry.schwarzschildTendex_trace
#print axioms GaloisForLFunctions.HTGeometry.schwarzschildTendex_determinant
#print axioms GaloisForLFunctions.HTGeometry.schwarzschildTendex_null_iff
#print axioms GaloisForLFunctions.HTGeometry.schwarzschildTendex_horizon_entropy_determinant
-- END PAPER AXIOM AUDIT
