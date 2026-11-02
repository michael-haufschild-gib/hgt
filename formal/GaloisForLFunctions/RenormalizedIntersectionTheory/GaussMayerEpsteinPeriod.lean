import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEpsteinQuadrants
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCauchyMoments

/-! An actual Cauchy integral maps the independently defined rectangular
Epstein field to the Mayer scattering period. Both axes and all four
quadrants are retained, with absolute convergence in the source chamber. -/

open Complex Set MeasureTheory
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerQuadraticCone MayerEpsteinQuadrants MayerCauchyMoments
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinPeriod

private theorem period_power {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (w : ℂ) :
    ((a/t : ℝ) : ℂ)^(-w)=(a : ℂ)^(-w)*(t : ℂ)^w := by
  rw [div_eq_mul_inv,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg ha.le (inv_pos.mpr ht).le]
  have h := Complex.cpow_mul_ofReal_nonneg ht.le (-1 : ℝ) (-w)
  rw [Real.rpow_neg_one] at h
  have he : ((-1 : ℝ) : ℂ)*(-w)=w := by push_cast; ring
  rw [he] at h
  rw [← h]

private theorem field_integrand {w : ℂ} (hw : 2 < w.re) {a t : ℝ}
    (ha : 0 < a) (ht : 0 < t) :
    cauchyWeight w t*epsteinField w (a/t)=
      riemannZeta w*cauchyWeight w t+
      (riemannZeta w*(a : ℂ)^(-w))*((t : ℂ)^w*cauchyWeight w t)+
      2*(cauchyWeight w t*quadraticCone w (a/t)) := by
  rw [epsteinField_eq hw (div_pos ha ht),period_power ha ht w]
  ring

/-- Absolute convergence of the full Epstein field's Cauchy average. -/
theorem epstein_average_integrable {w : ℂ} (hw : 2 < w.re) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => cauchyWeight w t*epsteinField w (a/t)) (Ioi 0) := by
  have h0 := ((cauchyWeight_integrable hw).integrableOn (s := Ioi (0 : ℝ))).const_mul (riemannZeta w)
  have hw' := (spectralWeight_integrable hw).const_mul (riemannZeta w*(a : ℂ)^(-w))
  have hq := (quadratic_average_integrable hw ha).const_mul (2 : ℂ)
  exact MeasureTheory.IntegrableOn.congr_fun ((h0.add hw').add hq)
    (fun t ht => (field_integrand hw ha ht).symm) measurableSet_Ioi

/-- The complete Epstein average, including its two axes, equals the full lattice period. -/
theorem epstein_average_eq {w : ℂ} (hw : 2 < w.re) {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), cauchyWeight w t*epsteinField w (a/t))=
      averagingFactor w*(riemannZeta w*(1+(a : ℂ)^(-w))+
        2*MayerPeriodMellin.conePeriod w a) := by
  have h0 := ((cauchyWeight_integrable hw).integrableOn (s := Ioi (0 : ℝ))).const_mul (riemannZeta w)
  have hw' := (spectralWeight_integrable hw).const_mul (riemannZeta w*(a : ℂ)^(-w))
  have hq := (quadratic_average_integrable hw ha).const_mul (2 : ℂ)
  have h01 : IntegrableOn (fun t : ℝ => riemannZeta w*cauchyWeight w t+
      (riemannZeta w*(a : ℂ)^(-w))*((t : ℂ)^w*cauchyWeight w t)) (Ioi 0) := h0.add hw'
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => field_integrand hw ha ht),
    integral_add h01 hq,integral_add h0 hw']
  simp only [integral_const_mul,cauchyWeight_integral hw,spectralWeight_integral hw,
    quadratic_average_eq_cone hw ha]
  ring

private theorem normalized_integrand {t : ℝ} (ht : 0 < t) (w : ℂ) (a : ℝ) :
    cauchyKernel w t*epsteinField w (a/t)/(t : ℂ)=
      (averagingFactor w)⁻¹*(cauchyWeight w t*epsteinField w (a/t)) := by
  unfold cauchyKernel
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne']

/-- The Epstein-to-period map is an absolutely convergent multiplicative convolution. -/
theorem cauchyKernel_epstein_integrable {w : ℂ} (hw : 2 < w.re)
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => cauchyKernel w t*epsteinField w (a/t)/(t : ℂ)) (Ioi 0) := by
  have h := (epstein_average_integrable hw ha).const_mul (averagingFactor w)⁻¹
  exact MeasureTheory.IntegrableOn.congr_fun h
    (fun t ht => (normalized_integrand ht w a).symm) measurableSet_Ioi

/-- The independently defined Epstein field maps to the actual Mayer scattering period. -/
theorem cauchyKernel_epstein_period {w : ℂ} (hw : 2 < w.re) {a : ℝ}
    (ha : a ∈ MayerScatteringPeriod.periodSegment) :
    _root_.RHTower.positiveMellinConvolution (cauchyKernel w) (epsteinField w) a=
      MayerScatteringPeriod.periodValue w a := by
  have ha0 : 0 < a := by linarith only [ha.1]
  rw [_root_.RHTower.positiveMellinConvolution,
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => normalized_integrand ht w a),
    integral_const_mul,epstein_average_eq hw ha0,
    inv_mul_cancel_left₀ (averagingFactor_ne_zero hw),
    MayerPeriodMellin.period_axes_decomposition hw ha]

#print axioms epstein_average_integrable
#print axioms epstein_average_eq
#print axioms cauchyKernel_epstein_integrable
#print axioms cauchyKernel_epstein_period
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinPeriod
