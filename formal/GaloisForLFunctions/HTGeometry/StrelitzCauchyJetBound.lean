import GaloisForLFunctions.HTGeometry.StrelitzEnlargedSet
import GaloisForLFunctions.HTGeometry.SphereMaxModulus

/-!
# Cauchy bounds for the Strelitz enlarged-set jet

The exact circle maximum dominates the entire enclosed disc.  Applying Cauchy's estimate on the
unit disc centered at `z` bounds the second derivative by twice the exact maximum at radius
`‖z‖ + 1`.  This is the analytic input used by the source to control the second Euler logarithmic
jet throughout the enlarged set, rather than only at selected Wiman points.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric

noncomputable section

/-- The exact maximum on a positive centered circle dominates every value in its closed disc. -/
theorem norm_coeffFun_le_coeffCircleMaximumNorm_of_norm_le
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {z : ℂ} {R : ℝ}
    (hR : 0 < R) (hz : ‖z‖ ≤ R) :
    ‖coeffFun a z‖ ≤ coeffCircleMaximumNorm a R := by
  obtain ⟨w, hwR, hzw⟩ := exists_sphere_norm_ge (differentiable_coeffFun ha) hR hz
  exact hzw.trans (norm_coeffFun_le_coeffCircleMaximumNorm_of_norm_eq ha hR hwR)

/-- Cauchy's estimate at unit distance bounds the second derivative by twice the exact circle
maximum one radial unit farther out. -/
theorem norm_iteratedDeriv_two_coeffFun_le_circleMaximumNorm_add_one
    {a : ℕ → ℂ} (ha : EntireCoeffs a) (z : ℂ) :
    ‖iteratedDeriv 2 (coeffFun a) z‖ ≤
      2 * coeffCircleMaximumNorm a (‖z‖ + 1) := by
  have hR : 0 < ‖z‖ + 1 := by positivity
  have hC : ∀ w ∈ sphere z 1,
      ‖coeffFun a w‖ ≤ coeffCircleMaximumNorm a (‖z‖ + 1) := by
    intro w hw
    have hdist : ‖w - z‖ = 1 := by simpa [dist_eq] using (mem_sphere.mp hw)
    have hwle : ‖w‖ ≤ ‖z‖ + 1 := by
      calc
        ‖w‖ = ‖(w - z) + z‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ = ‖z‖ + 1 := by rw [hdist]; ring
    exact norm_coeffFun_le_coeffCircleMaximumNorm_of_norm_le ha hR hwle
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    2 (by norm_num : (0 : ℝ) < 1) (differentiable_coeffFun ha).diffContOnCl hC
  simpa using h

/-- Derivative-of-derivative form of the same second-order Cauchy estimate. -/
theorem norm_deriv_deriv_coeffFun_le_circleMaximumNorm_add_one
    {a : ℕ → ℂ} (ha : EntireCoeffs a) (z : ℂ) :
    ‖deriv (deriv (coeffFun a)) z‖ ≤
      2 * coeffCircleMaximumNorm a (‖z‖ + 1) := by
  simpa [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_zero] using
    norm_iteratedDeriv_two_coeffFun_le_circleMaximumNorm_add_one ha z

end

end GaloisForLFunctions.HTGeometry
