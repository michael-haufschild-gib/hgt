import GaloisForLFunctions.BiScaleUncertainty.PhysicalCellAveraging
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Actual dilation of physical L² velocities

The representative `a * q (a*t)` defines a bounded linear operator for every
real scale, including zero. Its exact energy and primitive transformation
need no integrability, regularity or representative-selection premise.
-/

noncomputable section
open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

private theorem ae_mul_pullback (a : ℝ) (ha : a ≠ 0) {f g : ℝ → ℝ}
    (h : f =ᵐ[volume] g) :
    (fun t => f (a*t)) =ᵐ[volume] (fun t => g (a*t)) := by
  simpa only [Function.comp_def, smul_eq_mul] using
    (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) ha).ae_eq h

private theorem dilation_memLp (a : ℝ) (q : Velocity) :
    MemLp (fun t => a*q (a*t)) 2 volume := by
  by_cases ha : a = 0
  · simp only [ha, zero_mul]
    exact MemLp.zero
  · have hm : AEStronglyMeasurable (fun t => q (a*t)) volume := by
      simpa only [Function.comp_def, smul_eq_mul] using
        (Lp.memLp q).aestronglyMeasurable.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) ha)
    exact ((memLp_two_iff_integrable_sq hm).2
      ((integrable_velocity_sq q).comp_mul_left' ha)).const_mul a

def dilatedVelocity (a : ℝ) (q : Velocity) : Velocity :=
  (dilation_memLp a q).toLp (fun t => a*q (a*t))

theorem ae_dilatedVelocity (a : ℝ) (q : Velocity) :
    dilatedVelocity a q =ᵐ[volume] (fun t => a*q (a*t)) := MemLp.coeFn_toLp _

theorem norm_sq_dilatedVelocity (a : ℝ) (q : Velocity) :
    ‖dilatedVelocity a q‖^2 = |a| * ‖q‖^2 := by
  rw [norm_sq_velocity, norm_sq_velocity]
  calc
    _ = ∫ t, (a*q (a*t))^2 := by
      apply integral_congr_ae
      filter_upwards [ae_dilatedVelocity a q] with t ht
      rw [ht]
    _ = a^2 * ∫ t, (q (a*t))^2 := by
      simp only [mul_pow, integral_const_mul]
    _ = _ := by
      rw [Measure.integral_comp_mul_left (fun t => (q t)^2) a, smul_eq_mul, abs_inv]
      by_cases ha : a = 0
      · simp [ha]
      · have hab : |a| ≠ 0 := abs_ne_zero.mpr ha
        rw [← sq_abs a]
        field_simp

theorem norm_dilatedVelocity (a : ℝ) (q : Velocity) :
    ‖dilatedVelocity a q‖ = Real.sqrt |a| * ‖q‖ := by
  have h := norm_sq_dilatedVelocity a q
  have hs : (Real.sqrt |a| * ‖q‖)^2 = |a| * ‖q‖^2 := by
    rw [mul_pow, Real.sq_sqrt (abs_nonneg a)]
  nlinarith only [h, hs, norm_nonneg (dilatedVelocity a q),
    mul_nonneg (Real.sqrt_nonneg |a|) (norm_nonneg q)]

theorem dilatedVelocity_zero (q : Velocity) : dilatedVelocity 0 q = 0 := by
  apply Lp.ext
  filter_upwards [ae_dilatedVelocity 0 q, Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with t ht hz
  simp only [ht, hz, zero_mul, Pi.zero_apply]

theorem dilatedVelocity_add (a : ℝ) (q r : Velocity) :
    dilatedVelocity a (q+r) = dilatedVelocity a q+dilatedVelocity a r := by
  by_cases ha : a = 0
  · subst a
    simp only [dilatedVelocity_zero, add_zero]
  · apply Lp.ext
    filter_upwards [ae_dilatedVelocity a (q+r), ae_dilatedVelocity a q,
      ae_dilatedVelocity a r, ae_mul_pullback a ha (Lp.coeFn_add q r),
      Lp.coeFn_add (dilatedVelocity a q) (dilatedVelocity a r)] with t ht hq hr hs he
    simp only [Pi.add_apply] at hs he
    rw [ht, he, hs, hq, hr]
    ring

theorem dilatedVelocity_smul (a c : ℝ) (q : Velocity) :
    dilatedVelocity a (c • q) = c • dilatedVelocity a q := by
  by_cases ha : a = 0
  · subst a
    simp only [dilatedVelocity_zero, smul_zero]
  · apply Lp.ext
    filter_upwards [ae_dilatedVelocity a (c • q), ae_dilatedVelocity a q,
      ae_mul_pullback a ha (Lp.coeFn_smul c q),
      Lp.coeFn_smul c (dilatedVelocity a q)] with t ht hq hs he
    simp only [Pi.smul_apply, smul_eq_mul] at hs he
    rw [ht, he, hs, hq]
    ring

def physicalDilation (a : ℝ) : Velocity →L[ℝ] Velocity :=
  ({ toFun := dilatedVelocity a
     map_add' := dilatedVelocity_add a
     map_smul' := fun c q => by simpa using dilatedVelocity_smul a c q } :
    Velocity →ₗ[ℝ] Velocity).mkContinuous (Real.sqrt |a|)
    (fun q => (norm_dilatedVelocity a q).le)

theorem physicalDilation_apply (a : ℝ) (q : Velocity) :
    physicalDilation a q = dilatedVelocity a q := rfl

theorem ae_physicalDilation (a : ℝ) (q : Velocity) :
    physicalDilation a q =ᵐ[volume] (fun t => a*q (a*t)) := ae_dilatedVelocity a q

theorem physicalDilation_energy (a : ℝ) (q : Velocity) :
    ‖physicalDilation a q‖^2 = |a| * ‖q‖^2 := norm_sq_dilatedVelocity a q

theorem physicalDilation_norm (a : ℝ) (q : Velocity) :
    ‖physicalDilation a q‖ = Real.sqrt |a| * ‖q‖ := norm_dilatedVelocity a q

theorem physicalDilation_zero (q : Velocity) : physicalDilation 0 q = 0 :=
  dilatedVelocity_zero q

theorem physicalDilation_one (q : Velocity) : physicalDilation 1 q = q := by
  apply Lp.ext
  simpa only [one_mul] using ae_physicalDilation 1 q

theorem physicalDilation_comp (a b : ℝ) (q : Velocity) :
    physicalDilation a (physicalDilation b q) = physicalDilation (a*b) q := by
  by_cases ha : a = 0
  · simp [ha, physicalDilation_zero]
  · apply Lp.ext
    filter_upwards [ae_physicalDilation a (physicalDilation b q),
      ae_mul_pullback a ha (ae_physicalDilation b q), ae_physicalDilation (a*b) q]
      with t ht hb he
    rw [ht, hb, he, show b*(a*t) = (a*b)*t by ring]
    ring

theorem primitive_physicalDilation (a : ℝ) (q : Velocity) (t : ℝ) :
    primitive (physicalDilation a q) t = primitive q (a*t) := by
  unfold primitive
  calc
    _ = ∫ u in 0..t, a*q (a*u) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_physicalDilation a q] with u hu
      exact fun _ => hu
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      simpa only [smul_eq_mul, mul_zero] using
        (intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := t) (q : ℝ → ℝ) a)

theorem log_physicalDilation (n : ℕ) (q : Velocity) (x : ℝ) :
    logPrimitive (physicalDilation ((n : ℝ)+1) q) x =
      logPrimitive q (x+Real.log ((n : ℝ)+1)) := by
  rw [logPrimitive, logPrimitive, primitive_physicalDilation,
    Real.exp_add, Real.exp_log (by positivity)]
  congr 1
  ring

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
