import GaloisForLFunctions.HTGeometry.SmoothCylinderKernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Integration by parts on a compact cylinder

Kernel support removes the radial endpoint terms and periodicity cancels the
angular terms. The resulting divergence identity moves both derivatives to
the kernel. The norm bound uses only values of the source.
-/

open Set Filter Topology
open scoped ContDiff
namespace GaloisForLFunctions.HTGeometry.SmoothCylinder
noncomputable section
variable {a b : ℝ}

open MeasureTheory

def box (a b : ℝ) : Set (ℝ × ℝ) := Icc a b ×ˢ Icc 0 (2*Real.pi)

def boxIntegral (a b : ℝ) (F : ℝ × ℝ → ℂ) : ℂ := ∫ p in box a b, F p

theorem box_integrable {F : ℝ × ℝ → ℂ} (hF : Continuous F) :
    IntegrableOn F (box a b) :=
  hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem boxIntegral_eq_iterated {F : ℝ × ℝ → ℂ} (hab : a ≤ b) (hF : Continuous F) :
    boxIntegral a b F = ∫ r in a..b, ∫ theta in 0..2*Real.pi, F (r,theta) := by
  have hi : Integrable F ((volume.restrict (Icc a b)).prod
      (volume.restrict (Icc 0 (2*Real.pi)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact box_integrable hF
  have h := MeasureTheory.integral_prod F hi
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  simp_rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : 0 ≤ 2*Real.pi)] at h
  rw [← intervalIntegral.integral_of_le hab] at h
  exact h

theorem boxIntegral_eq_iterated_symm {F : ℝ × ℝ → ℂ} (hab : a ≤ b) (hF : Continuous F) :
    boxIntegral a b F = ∫ theta in 0..2*Real.pi, ∫ r in a..b, F (r,theta) := by
  have hi : Integrable F ((volume.restrict (Icc a b)).prod
      (volume.restrict (Icc 0 (2*Real.pi)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact box_integrable hF
  have h := MeasureTheory.integral_prod_symm F hi
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  simp_rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab] at h
  rw [← intervalIntegral.integral_of_le (by positivity : 0 ≤ 2*Real.pi)] at h
  exact h

theorem boxIntegral_add {F G : ℝ × ℝ → ℂ} (hF : Continuous F) (hG : Continuous G) :
    boxIntegral a b (fun p => F p + G p) = boxIntegral a b F + boxIntegral a b G :=
  integral_add (box_integrable hF) (box_integrable hG)

theorem boxIntegral_neg (F : ℝ × ℝ → ℂ) :
    boxIntegral a b (fun p => -F p) = -boxIntegral a b F := integral_neg _

theorem boxIntegral_const_mul (c : ℂ) (F : ℝ × ℝ → ℂ) :
    boxIntegral a b (fun p => c*F p) = c*boxIntegral a b F := integral_const_mul _ _

theorem directional_smooth {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (v : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun p => fderiv ℝ F p v) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem angular_hasDerivAt {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (r theta : ℝ) :
    HasDerivAt (fun t => F (r,t)) (fderiv ℝ F (r,theta) (0,1)) theta :=
  (hF.differentiable (by simp) (r,theta)).hasFDerivAt.comp_hasDerivAt theta
    ((hasDerivAt_const theta r).prodMk (hasDerivAt_id theta))

theorem radial_integration_by_parts (hab : a ≤ b) (k : Kernel a b)
    {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) :
    boxIntegral a b (fun p => k p * fderiv ℝ F p (1,0)) =
      -boxIntegral a b (fun p => k.directional (1,0) p * F p) := by
  have hD := directional_smooth hF (1,0)
  have haux (theta : ℝ) :
      (∫ r in a..b, k (r,theta) * fderiv ℝ F (r,theta) (1,0)) =
      -(∫ r in a..b, k.directional (1,0) (r,theta) * F (r,theta)) := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun r => k (r,theta)) (u' := fun r => k.directional (1,0) (r,theta))
      (v := fun r => F (r,theta)) (v' := fun r => fderiv ℝ F (r,theta) (1,0))
      (fun r _ => SmoothAngularAverage.slice_hasDerivAt k.smooth r theta)
      (fun r _ => SmoothAngularAverage.slice_hasDerivAt hF r theta)
      (((k.directional (1,0)).smooth.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
      ((hD.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
    simpa only [k.boundary_left, k.boundary_right, zero_mul, sub_self, zero_sub] using h
  rw [boxIntegral_eq_iterated_symm (F := fun p => k p * fderiv ℝ F p (1,0)) hab (k.smooth.continuous.mul hD.continuous),
    boxIntegral_eq_iterated_symm (F := fun p => k.directional (1,0) p * F p) hab ((k.directional (1,0)).smooth.continuous.mul hF.continuous)]
  simp_rw [haux]
  rw [intervalIntegral.integral_neg]

theorem angular_integration_by_parts (hab : a ≤ b) (k : Kernel a b)
    {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ r theta, F (r,theta+2*Real.pi) = F (r,theta)) :
    boxIntegral a b (fun p => k p * fderiv ℝ F p (0,1)) =
      -boxIntegral a b (fun p => k.directional (0,1) p * F p) := by
  have hD := directional_smooth hF (0,1)
  have haux (r : ℝ) :
      (∫ theta in 0..2*Real.pi, k (r,theta) * fderiv ℝ F (r,theta) (0,1)) =
      -(∫ theta in 0..2*Real.pi, k.directional (0,1) (r,theta) * F (r,theta)) := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun theta => k (r,theta)) (u' := fun theta => k.directional (0,1) (r,theta))
      (v := fun theta => F (r,theta)) (v' := fun theta => fderiv ℝ F (r,theta) (0,1))
      (fun theta _ => angular_hasDerivAt k.smooth r theta)
      (fun theta _ => angular_hasDerivAt hF r theta)
      (((k.directional (0,1)).smooth.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 (2*Real.pi))
      ((hD.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 (2*Real.pi))
    have hk0 : k (r,2*Real.pi) = k (r,0) := by simpa only [zero_add] using k.periodic r 0
    have hf0 : F (r,2*Real.pi) = F (r,0) := by simpa only [zero_add] using hper r 0
    simpa only [hk0,hf0,sub_self,zero_sub] using h
  rw [boxIntegral_eq_iterated (F := fun p => k p * fderiv ℝ F p (0,1)) hab (k.smooth.continuous.mul hD.continuous),
    boxIntegral_eq_iterated (F := fun p => k.directional (0,1) p * F p) hab ((k.directional (0,1)).smooth.continuous.mul hF.continuous)]
  simp_rw [haux]
  rw [intervalIntegral.integral_neg]

theorem norm_boxIntegral_mul_le (k : Kernel a b) (F : ℝ × ℝ → ℂ) {C : ℝ}
    (hC : ∀ p ∈ box a b, ‖F p‖ ≤ C) :
    ‖boxIntegral a b (fun p => k p * F p)‖ ≤ (∫ p in box a b, ‖k p‖) * C := by
  have hi : IntegrableOn (fun p => ‖k p‖*C) (box a b) :=
    (k.smooth.continuous.norm.mul continuous_const).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  calc
    _ ≤ ∫ p in box a b, ‖k p‖*C := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem (isClosed_Icc.measurableSet.prod isClosed_Icc.measurableSet)] with p hp
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC p hp) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

/-- The formal transpose of a radial/angular vector field acts on the kernel. -/
theorem divergence_identity (hab : a ≤ b) (kr kt : Kernel a b)
    {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ r theta, F (r,theta+2*Real.pi) = F (r,theta)) :
    boxIntegral a b (fun p => kr p * fderiv ℝ F p (1,0) + kt p * fderiv ℝ F p (0,1)) =
      boxIntegral a b (fun p => ((kr.directional (1,0)).add (kt.directional (0,1))).neg p * F p) := by
  have he : (fun p => ((kr.directional (1,0)).add (kt.directional (0,1))).neg p * F p) =
      fun p => -(kr.directional (1,0) p * F p + kt.directional (0,1) p * F p) := by
    funext p
    change -(kr.directional (1,0) p + kt.directional (0,1) p) * F p = _
    ring
  rw [he, boxIntegral_neg,
    boxIntegral_add (F := fun p => kr p * fderiv ℝ F p (1,0))
      (G := fun p => kt p * fderiv ℝ F p (0,1))
      (kr.smooth.continuous.mul (directional_smooth hF (1,0)).continuous)
      (kt.smooth.continuous.mul (directional_smooth hF (0,1)).continuous),
    radial_integration_by_parts hab kr hF, angular_integration_by_parts hab kt hF hper,
    boxIntegral_add (F := fun p => kr.directional (1,0) p * F p)
      (G := fun p => kt.directional (0,1) p * F p)
      ((kr.directional (1,0)).smooth.continuous.mul hF.continuous)
      ((kt.directional (0,1)).smooth.continuous.mul hF.continuous)]
  ring

end
end GaloisForLFunctions.HTGeometry.SmoothCylinder
