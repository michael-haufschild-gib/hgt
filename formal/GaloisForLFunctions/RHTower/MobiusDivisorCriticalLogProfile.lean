import GaloisForLFunctions.RHTower.MobiusDivisorCriticalAbelSignedBoundaryMoments

/-!
# The actual critical source in logarithmic time

The signed profile and its source velocity retain the floor and Euler
correction. Their quadratic moments admit the finite prime-tail argument;
the profile's first two signed moments are identified exactly.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

def criticalAbelLogProfile (t : ℝ) : ℝ :=
  Real.exp (-(3 / 2 : ℝ) * t) * criticalContinuousAbel (Real.exp t)

def criticalAbelLogDefect (t : ℝ) : ℝ :=
  Real.exp (-t) * psiDefect ⌊Real.exp t⌋₊

def criticalAbelLogVelocity (t : ℝ) : ℝ :=
  criticalAbelLogDefect t / 2 - (3 / 2 : ℝ) * criticalAbelLogProfile t

private theorem exp_ray_integrable_iff (f : ℝ → ℝ) :
    IntegrableOn f (Ioi (1 : ℝ)) ↔
      IntegrableOn (fun t : ℝ => Real.exp t * f (Real.exp t)) (Ioi (0 : ℝ)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    (fun a _ b _ hab => Real.exp_injective hab) f
  simpa only [Real.image_exp_Ioi, Real.exp_zero, abs_of_pos (Real.exp_pos _),
    smul_eq_mul] using h

private theorem exp_ray_integral (f : ℝ → ℝ) :
    (∫ y in Ioi (1 : ℝ), f y) =
      ∫ t in Ioi (0 : ℝ), Real.exp t * f (Real.exp t) := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    (fun a _ b _ hab => Real.exp_injective hab) f
  simpa only [Real.image_exp_Ioi, Real.exp_zero, abs_of_pos (Real.exp_pos _),
    smul_eq_mul] using h

private theorem exp_abel_weight (t : ℝ) :
    Real.exp t / (Real.exp t) ^ (5 / 2 : ℝ) = Real.exp (-(3 / 2 : ℝ) * t) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, ← Real.exp_sub]
  congr 1
  ring

theorem measurable_criticalAbelLogProfile : Measurable criticalAbelLogProfile :=
  ((measurable_const.mul measurable_id).exp).mul
    (measurable_criticalContinuousAbel.comp Real.measurable_exp)

theorem measurable_criticalAbelLogDefect : Measurable criticalAbelLogDefect :=
  (measurable_id.neg.exp).mul
    ((measurable_of_countable psiDefect).comp Real.measurable_exp.nat_floor)

/-- Absolute quadratic moment admission for the literal signed log profile. -/
theorem integrableOn_criticalAbelLogProfile_quadratic :
    IntegrableOn (fun t : ℝ => (1 + t ^ (2 : ℕ)) * criticalAbelLogProfile t)
      (Ioi (0 : ℝ)) := by
  have hi := (exp_ray_integrable_iff _).mp
    integrableOn_criticalContinuousAbel_boundary_log_sq
  apply hi.mono'
    (((measurable_const.add (measurable_id.pow_const (2 : ℕ))).mul
      measurable_criticalAbelLogProfile).aestronglyMeasurable.restrict)
  filter_upwards with t
  dsimp only [Pi.mul_apply, Pi.add_apply, id_eq]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + t ^ (2 : ℕ)),
    criticalAbelLogProfile, abs_mul, abs_of_pos (Real.exp_pos _), Real.log_exp]
  have hw := exp_abel_weight t
  apply le_of_eq
  calc
    (1 + t ^ (2 : ℕ)) * (Real.exp (-(3 / 2 : ℝ) * t) * |criticalContinuousAbel (Real.exp t)|) =
        (Real.exp t / (Real.exp t) ^ (5 / 2 : ℝ)) *
          (|criticalContinuousAbel (Real.exp t)| * (1 + t ^ (2 : ℕ))) := by rw [hw]; ring
    _ = _ := by ring

/-- Every absolute polynomial log-time moment of the actual defect is admitted. -/
theorem integrableOn_criticalAbelLogDefect_moment (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k * criticalAbelLogDefect t) (Ioi (0 : ℝ)) := by
  have hi := (exp_ray_integrable_iff _).mp (integrableOn_psiDefect_floor_log_moment k)
  apply hi.mono' (((measurable_id.pow_const k).mul
    measurable_criticalAbelLogDefect).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  dsimp only [Pi.mul_apply, id_eq]
  rw [Real.norm_eq_abs, criticalAbelLogDefect, abs_mul, abs_mul,
    abs_of_nonneg (pow_nonneg ht.le k), abs_of_pos (Real.exp_pos _), Real.log_exp,
    Real.exp_neg]
  exact le_of_eq (by field_simp [Real.exp_ne_zero t])

/-- The full signed velocity, including its profile correction, has an
absolute quadratic moment. -/
theorem integrableOn_criticalAbelLogVelocity_quadratic :
    IntegrableOn (fun t : ℝ => (1 + t ^ (2 : ℕ)) * criticalAbelLogVelocity t)
      (Ioi (0 : ℝ)) := by
  have hq0 : IntegrableOn criticalAbelLogDefect (Ioi (0 : ℝ)) := by
    simpa using integrableOn_criticalAbelLogDefect_moment 0
  have hq2 := integrableOn_criticalAbelLogDefect_moment 2
  have h : IntegrableOn (fun t : ℝ =>
      (criticalAbelLogDefect t + t ^ (2 : ℕ) * criticalAbelLogDefect t) / 2 -
        (3 / 2 : ℝ) * ((1 + t ^ (2 : ℕ)) * criticalAbelLogProfile t)) (Ioi (0 : ℝ)) :=
    ((hq0.add hq2).div_const 2).sub
    (integrableOn_criticalAbelLogProfile_quadratic.const_mul (3 / 2 : ℝ))
  apply h.congr_fun _ measurableSet_Ioi
  intro t _
  dsimp [criticalAbelLogVelocity]
  ring

/-- Exact zero signed mass after logarithmic change of variables. -/
theorem criticalAbelLogProfile_mass_zero :
    (∫ t in Ioi (0 : ℝ), criticalAbelLogProfile t) = 0 := by
  have h := criticalAbel_boundary_mass_zero
  rw [exp_ray_integral] at h
  convert h using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp [criticalAbelLogProfile]
  rw [show Real.exp t * (criticalContinuousAbel (Real.exp t) /
      (Real.exp t) ^ (5 / 2 : ℝ)) =
      (Real.exp t / (Real.exp t) ^ (5 / 2 : ℝ)) * criticalContinuousAbel (Real.exp t) by ring,
    exp_abel_weight]

/-- Exact first signed moment of the logarithmic profile. -/
theorem criticalAbelLogProfile_first_moment :
    (∫ t in Ioi (0 : ℝ), t * criticalAbelLogProfile t) =
      -(divisorHarmonicBoundary / 3) := by
  have h := criticalAbel_boundary_log_moment
  rw [exp_ray_integral] at h
  convert h using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp [criticalAbelLogProfile]
  rw [Real.log_exp]
  calc
    _ = (Real.exp t / (Real.exp t) ^ (5 / 2 : ℝ)) *
        criticalContinuousAbel (Real.exp t) * t := by rw [exp_abel_weight]; ring
    _ = _ := by ring

end RHTower
