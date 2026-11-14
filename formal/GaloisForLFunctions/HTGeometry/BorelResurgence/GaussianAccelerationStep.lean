import GaloisForLFunctions.HTGeometry.BorelResurgence.GaussianAcceleration

/-!
# Acceleration of a Borel step discontinuity

A positive-ray unit step accelerates to the complementary Gaussian error function. The latter
is defined by its convergent Gaussian tail, so this identity does not depend on a formal series
or analytic continuation convention.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real complementary error function, normalized by its Gaussian tail. -/
def gaussianErfc (x : ℝ) : ℝ :=
  2 / Real.sqrt Real.pi * ∫ y in Ioi x, Real.exp (-(y ^ 2))

theorem integrable_gaussianErfc_tail (x : ℝ) :
    IntegrableOn (fun y : ℝ => Real.exp (-(y ^ 2))) (Ioi x) := by
  simpa only [neg_one_mul] using (integrable_exp_neg_mul_sq (b := 1) zero_lt_one).integrableOn

theorem gaussianErfc_zero : gaussianErfc 0 = 1 := by
  unfold gaussianErfc
  have h := integral_gaussian_Ioi (1 : ℝ)
  simp only [neg_one_mul, div_one] at h
  rw [h]
  field_simp [Real.sqrt_ne_zero'.mpr Real.pi_pos]

/-- Every finite Gaussian tail has strictly positive mass. -/
theorem gaussianErfc_pos (x : ℝ) : 0 < gaussianErfc x := by
  unfold gaussianErfc
  apply mul_pos (by positivity)
  apply (integral_pos_iff_support_of_nonneg (fun y => (Real.exp_pos _).le)
    (integrable_gaussianErfc_tail x)).mpr
  have hs : Function.support (fun y : ℝ => Real.exp (-(y ^ 2))) = univ := by
    ext y
    simp only [Function.mem_support, mem_univ, iff_true]
    exact Real.exp_ne_zero _
  rw [hs]
  simp

/-- The acceleration kernel's tail is the complementary error function at the rescaled cutoff. -/
theorem integral_gaussianAccelerationKernel_tail (s A : ℝ) :
    (∫ x in Ioi A, gaussianAccelerationKernel (Real.exp s) x) =
      gaussianErfc (A / (2 * Real.sqrt (Real.exp s))) := by
  let a := (2 * Real.sqrt (Real.exp s))⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  have hp : Real.sqrt Real.pi ≠ 0 := by positivity
  have ht : Real.sqrt (Real.exp s) ≠ 0 := by positivity
  have hs : Real.sqrt (Real.exp s) ^ 2 = Real.exp s := Real.sq_sqrt (Real.exp_pos s).le
  have ha2 : a ^ 2 = (4 * Real.exp s)⁻¹ := by
    dsimp [a]
    rw [inv_pow, mul_pow, hs]
    norm_num
  have hk (x : ℝ) : gaussianAccelerationKernel (Real.exp s) x =
      (2 / Real.sqrt Real.pi * a) * Real.exp (-((a * x) ^ 2)) := by
    unfold gaussianAccelerationKernel
    rw [mul_pow, ha2, neg_mul, Real.sqrt_mul Real.pi_pos.le]
    dsimp [a]
    field_simp [hp, ht]
    <;> ring
  simp_rw [hk]
  rw [integral_const_mul, integral_comp_mul_left_Ioi (fun x => Real.exp (-(x ^ 2))) A ha]
  have harg : A / (2 * Real.sqrt (Real.exp s)) = a * A := by dsimp [a]; ring
  rw [harg, gaussianErfc, smul_eq_mul]
  field_simp [ha.ne']
  <;> ring

/-- A positive Borel threshold accelerates exactly to an error-function discontinuity. -/
theorem gaussianAcceleration_step (s u : ℝ) :
    gaussianAcceleration ((Ioi (Real.exp u)).indicator (fun _ : ℝ => 1)) (Real.exp s) =
      gaussianErfc (Real.exp u / (2 * Real.sqrt (Real.exp s))) := by
  unfold gaussianAcceleration
  have he (x : ℝ) : gaussianAccelerationKernel (Real.exp s) x *
      (Ioi (Real.exp u)).indicator (fun _ : ℝ => 1) x =
        (Ioi (Real.exp u)).indicator (gaussianAccelerationKernel (Real.exp s)) x := by
    by_cases hx : x ∈ Ioi (Real.exp u)
    · simp only [indicator_of_mem hx, mul_one]
    · simp only [indicator_of_notMem hx, mul_zero]
  simp_rw [he]
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  have hsub : Ioi (Real.exp u) ⊆ Ioi (0 : ℝ) := fun x hx => (Real.exp_pos u).trans hx
  rw [inter_eq_left.mpr hsub]
  exact integral_gaussianAccelerationKernel_tail s (Real.exp u)

end

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.integrable_gaussianErfc_tail
#print axioms GaloisForLFunctions.HTGeometry.gaussianErfc_zero
#print axioms GaloisForLFunctions.HTGeometry.gaussianErfc_pos
#print axioms GaloisForLFunctions.HTGeometry.integral_gaussianAccelerationKernel_tail
#print axioms GaloisForLFunctions.HTGeometry.gaussianAcceleration_step
