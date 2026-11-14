import GaloisForLFunctions.HTGeometry.BorelResurgence.GaussianAccelerationStep
import GaloisForLFunctions.HTGeometry.BorelSeriesConvolution
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Acceleration of exponential Borel data

Completing the square evaluates acceleration of every real exponential in terms of the
complementary error function. Geometric coefficient sequences have exactly these ordinary
Borel transforms, giving an unconditional infinite-series example of the level change.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Linear exponential growth translates the Gaussian center and contributes an exact prefactor. -/
theorem gaussianAccelerationKernel_mul_exponential (s r x : ℝ) :
    gaussianAccelerationKernel (Real.exp s) x * Real.exp (r * x) =
      Real.exp (Real.exp s * r ^ 2) *
        gaussianAccelerationKernel (Real.exp s) (x - 2 * Real.exp s * r) := by
  unfold gaussianAccelerationKernel
  rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
  congr 2
  field_simp [Real.exp_ne_zero]
  <;> ring

/-- Every linear exponential is accelerable at every positive time, on the entire real axis. -/
theorem integrable_gaussianAcceleration_exponential (s r : ℝ) :
    Integrable (fun x => gaussianAccelerationKernel (Real.exp s) x * Real.exp (r * x)) := by
  simp_rw [gaussianAccelerationKernel_mul_exponential]
  unfold gaussianAccelerationKernel
  exact (((integrable_exp_neg_mul_sq (by positivity : 0 < (4 * Real.exp s)⁻¹)).comp_sub_right
    (2 * Real.exp s * r)).const_mul (Real.sqrt (Real.pi * Real.exp s))⁻¹).const_mul _

private theorem integral_shift_gaussianAccelerationKernel (s h : ℝ) :
    (∫ x in Ioi (0 : ℝ), gaussianAccelerationKernel (Real.exp s) (x - h)) =
      ∫ x in Ioi (-h), gaussianAccelerationKernel (Real.exp s) x := by
  have himage : (fun x : ℝ => x - h) '' Ioi 0 = Ioi (-h) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change 0 < x at hx
      change -h < x - h
      linarith only [hx]
    · intro hy
      change -h < y at hy
      refine ⟨y + h, ?_, by ring⟩
      change 0 < y + h
      linarith only [hy]
  have hc := integral_image_eq_integral_abs_deriv_smul
    (f := fun x : ℝ => x - h) (f' := fun _ => (1 : ℝ)) (s := Ioi (0 : ℝ))
    measurableSet_Ioi (fun x _ => ((hasDerivAt_id x).sub_const h).hasDerivWithinAt)
    (fun x _ y _ hxy => sub_right_injective h hxy)
    (gaussianAccelerationKernel (Real.exp s))
  rw [himage] at hc
  simpa only [abs_one, one_smul] using hc.symm

/-- Exact acceleration of exponential data, including both signs of the exponent. -/
theorem gaussianAcceleration_exponential (s r : ℝ) :
    gaussianAcceleration (fun x => Real.exp (r * x)) (Real.exp s) =
      Real.exp (Real.exp s * r ^ 2) * gaussianErfc (-r * Real.sqrt (Real.exp s)) := by
  unfold gaussianAcceleration
  simp_rw [gaussianAccelerationKernel_mul_exponential]
  rw [integral_const_mul, integral_shift_gaussianAccelerationKernel,
    integral_gaussianAccelerationKernel_tail]
  have hs : Real.sqrt (Real.exp s) ^ 2 = Real.exp s := Real.sq_sqrt (Real.exp_pos s).le
  have he : -(2 * Real.exp s * r) / (2 * Real.sqrt (Real.exp s)) =
      -r * Real.sqrt (Real.exp s) := by
    apply (div_eq_iff (by positivity : (2 * Real.sqrt (Real.exp s)) ≠ 0)).mpr
    linear_combination 2 * r * hs
  rw [he]

/-- The ordinary Borel transform of geometric coefficients is an exponential. -/
theorem borelSeries_geometric_eq_exp (r x : ℝ) :
    borelSeries (fun n => r ^ n) x = Real.exp (r * x) := by
  rw [Real.exp_eq_exp_ℝ, ← (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (r * x)).tsum_eq]
  unfold borelSeries dividedPowerFn
  apply tsum_congr
  intro n
  simp only [mul_pow, smul_eq_mul]
  ring

/-- An exact infinite-series Borel-level change for every geometric coefficient sequence. -/
theorem gaussianAcceleration_borelSeries_geometric (s r : ℝ) :
    gaussianAcceleration (borelSeries (fun n => r ^ n)) (Real.exp s) =
      Real.exp (Real.exp s * r ^ 2) * gaussianErfc (-r * Real.sqrt (Real.exp s)) := by
  have he : borelSeries (fun n => r ^ n) = fun x => Real.exp (r * x) :=
    funext (borelSeries_geometric_eq_exp r)
  rw [he, gaussianAcceleration_exponential]

end

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.gaussianAccelerationKernel_mul_exponential
#print axioms GaloisForLFunctions.HTGeometry.integrable_gaussianAcceleration_exponential
#print axioms GaloisForLFunctions.HTGeometry.gaussianAcceleration_exponential
#print axioms GaloisForLFunctions.HTGeometry.borelSeries_geometric_eq_exp
#print axioms GaloisForLFunctions.HTGeometry.gaussianAcceleration_borelSeries_geometric
