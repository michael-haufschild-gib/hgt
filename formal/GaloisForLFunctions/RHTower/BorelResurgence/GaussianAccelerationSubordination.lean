import GaloisForLFunctions.RHTower.BurnolGlasserIntegral
import GaloisForLFunctions.HTGeometry.BorelResurgence.GaussianAcceleration

/-!
# Gaussian acceleration and Poisson subordination

The negative spatial derivative of the acceleration kernel is the positive first-passage
kernel. Its Laplace transform in acceleration time is exactly the Poisson square-root
semigroup. This identifies the Borel acceleration kernel with the existing Glasser
subordination calculus, including genuine integrability.
-/

open MeasureTheory Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The spatial derivative of the acceleration kernel is its first-passage density. -/
theorem hasDerivAt_gaussianAccelerationKernel (t x : ℝ) :
    HasDerivAt (gaussianAccelerationKernel t)
      (-(x / (2 * t)) * gaussianAccelerationKernel t x) x := by
  have h := (((hasDerivAt_pow 2 x).const_mul (-(4 * t)⁻¹)).exp).const_mul
    (Real.sqrt (Real.pi * t))⁻¹
  convert h using 1
  simp only [gaussianAccelerationKernel, mul_inv, inv_pow]
  norm_num
  ring

/-- Laplace transforming the first-passage density gives the square-root semigroup. -/
theorem gaussianAcceleration_firstPassage_laplace (u s : ℝ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(t * Real.exp s)) *
      (Real.exp u / (2 * t) * gaussianAccelerationKernel t (Real.exp u))) =
        Real.exp (-(Real.exp u * Real.sqrt (Real.exp s))) := by
  have hp : Real.sqrt Real.pi ≠ 0 := by positivity
  have hpoint (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      Real.exp (-(t * Real.exp s)) *
        (Real.exp u / (2 * t) * gaussianAccelerationKernel t (Real.exp u)) =
      Real.exp u / (2 * Real.sqrt Real.pi) *
        burnolSubordinationIntegrand (Real.exp u) (Real.exp s) t := by
    have ht0 : 0 < t := ht
    have hs : Real.sqrt t ≠ 0 := by positivity
    have hnormal : Real.exp u / (2 * t) * (Real.sqrt (Real.pi * t))⁻¹ =
        Real.exp u / (2 * Real.sqrt Real.pi) * t ^ (-(3 : ℝ) / 2) := by
      rw [Real.sqrt_mul Real.pi_pos.le, burnolRpow_neg_three_halves ht0]
      generalize hr : Real.sqrt t = r at *
      have hr2 : r ^ 2 = t := by rw [← hr, Real.sq_sqrt ht0.le]
      rw [← hr2]
      field_simp [hp, hs]
      <;> ring
    rw [gaussianAccelerationKernel, ← mul_assoc (Real.exp u / (2 * t)), hnormal]
    unfold burnolSubordinationIntegrand
    rw [show -(4 * t)⁻¹ * Real.exp u ^ 2 = -(Real.exp u ^ 2 / (4 * t)) by ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul]
  exact (burnolPoissonSubordination (Real.exp_pos u) (Real.exp_pos s)).symm

/-- The first-passage Laplace integral is genuinely integrable, since its evaluated value is nonzero. -/
theorem integrableOn_gaussianAcceleration_firstPassage (u s : ℝ) :
    IntegrableOn (fun t => Real.exp (-(t * Real.exp s)) *
      (Real.exp u / (2 * t) * gaussianAccelerationKernel t (Real.exp u))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussianAcceleration_firstPassage_laplace]
  exact Real.exp_ne_zero _

/-- The same identity in differential form connects the two existing kernel calculi. -/
theorem gaussianAcceleration_negative_derivative_laplace (u s : ℝ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(t * Real.exp s)) *
      (-deriv (gaussianAccelerationKernel t) (Real.exp u))) =
        Real.exp (-(Real.exp u * Real.sqrt (Real.exp s))) := by
  simp_rw [(hasDerivAt_gaussianAccelerationKernel _ _).deriv, neg_mul, neg_neg]
  exact gaussianAcceleration_firstPassage_laplace u s

end

end RHTower

#print axioms RHTower.hasDerivAt_gaussianAccelerationKernel
#print axioms RHTower.gaussianAcceleration_firstPassage_laplace
#print axioms RHTower.integrableOn_gaussianAcceleration_firstPassage
#print axioms RHTower.gaussianAcceleration_negative_derivative_laplace
