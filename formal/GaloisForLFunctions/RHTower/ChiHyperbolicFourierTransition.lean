import GaloisForLFunctions.HTGeometry.FourierIntegralDilation
import GaloisForLFunctions.RHTower.BourgainPhasePerturbation
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exact hyperbolic Fourier transition

The complete two-coordinate kernel with phase p*q/r+x*p+y*q equals
its full bilinear Fourier multiplier at the completed-phase coordinates.
Fourier inversion and an affine change of variables retain both entire
Schwartz amplitudes, including their edge transitions. Absolute product
integrability is proved on both sides; no stationary approximation or
cancellation hypothesis is used.
-/

noncomputable section
open MeasureTheory Complex
open scoped FourierTransform
namespace RHTower.BAGTrace

private def wave (u : ℝ) : ℂ := bourgainOscillation (2*Real.pi*u)

private theorem wave_add (u v : ℝ) : wave (u+v)=wave u*wave v := by
  unfold wave bourgainOscillation
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem wave_continuous : Continuous wave := by
  unfold wave bourgainOscillation
  fun_prop

private theorem wave_norm (u : ℝ) : ‖wave u‖=1 := norm_bourgainOscillation _

private theorem fourier_eq_wave (f : ℝ → ℂ) (a : ℝ) :
    𝓕 f a = ∫ x : ℝ, wave (-a*x)*f x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  congr 1
  unfold wave bourgainOscillation
  congr 1
  push_cast
  ring

private theorem inversion_wave (g : SchwartzMap ℝ ℂ) (a : ℝ) :
    (∫ x : ℝ, wave (a*x)*(𝓕 g) x)=g a := by
  have h := congrArg (fun h : SchwartzMap ℝ ℂ => h a)
    (show (𝓕⁻ (𝓕 g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ)=g from FourierTransform.fourierInv_fourier_eq g)
  change (𝓕 (𝓕 g)) (-a)=g a at h
  rw [SchwartzMap.fourier_coe,fourier_eq_wave] at h
  simpa only [neg_neg] using h

/-- The full bilinear Fourier multiplier; no edge or stationary expansion is taken. -/
def bagHyperbolicTransition (r : ℝ) (f g : SchwartzMap ℝ ℂ) (s t : ℝ) : ℂ :=
  ∫ ξ : ℝ, ∫ η : ℝ,
    bourgainOscillation (2*Real.pi*(s*ξ+t*η-r*ξ*η)) * ((𝓕 f) ξ*(𝓕 g) η)

theorem integrable_bagHyperbolicTransition (r : ℝ) (f g : SchwartzMap ℝ ℂ) (s t : ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      bourgainOscillation (2*Real.pi*(s*z.1+t*z.2-r*z.1*z.2)) *
        ((𝓕 f) z.1*(𝓕 g) z.2)) (volume.prod volume) := by
  apply (((𝓕 f).integrable (μ := volume)).mul_prod ((𝓕 g).integrable (μ := volume))).bdd_mul (c := 1)
  · exact (wave_continuous.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards [] with z
    exact le_of_eq (wave_norm _)

/-- Fourier inversion retains the whole transition profile, including all edges. -/
theorem bagHyperbolicTransition_eq_partial (r : ℝ) (f g : SchwartzMap ℝ ℂ) (s t : ℝ) :
    bagHyperbolicTransition r f g s t =
      ∫ ξ : ℝ, bourgainOscillation (2*Real.pi*(s*ξ))*(𝓕 f) ξ*g (t-r*ξ) := by
  unfold bagHyperbolicTransition
  apply integral_congr_ae
  filter_upwards [] with ξ
  change (∫ η : ℝ, wave (s*ξ+t*η-r*ξ*η)*((𝓕 f) ξ*(𝓕 g) η)) = _
  calc
    _ = ∫ η : ℝ, (wave (s*ξ)*(𝓕 f) ξ)*(wave ((t-r*ξ)*η)*(𝓕 g) η) := by
      apply integral_congr_ae
      filter_upwards [] with η
      rw [show s*ξ+t*η-r*ξ*η = s*ξ+(t-r*ξ)*η by ring,wave_add]
      ring
    _ = _ := by rw [integral_const_mul,inversion_wave]; rfl

/-- The original full two-variable oscillatory integral. -/
def bagHyperbolicKernel (r x y : ℝ) (f g : SchwartzMap ℝ ℂ) : ℂ :=
  ∫ q : ℝ, ∫ p : ℝ,
    bourgainOscillation (2*Real.pi*(p*q/r+x*p+y*q))*(f p*g q)

theorem integrable_bagHyperbolicKernel (r x y : ℝ) (f g : SchwartzMap ℝ ℂ) :
    Integrable (fun z : ℝ × ℝ =>
      bourgainOscillation (2*Real.pi*(z.2*z.1/r+x*z.2+y*z.1))*(f z.2*g z.1))
      (volume.prod volume) := by
  have h := ((g.integrable (μ := volume)).mul_prod (f.integrable (μ := volume))).bdd_mul (c := 1)
    (wave_continuous.comp (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z : ℝ × ℝ => le_of_eq (wave_norm
      (z.2*z.1/r+x*z.2+y*z.1))))
  simpa only [wave,Function.comp_apply,mul_comm] using h

private theorem kernel_partial (r x y : ℝ) (f g : SchwartzMap ℝ ℂ) :
    bagHyperbolicKernel r x y f g =
      ∫ q : ℝ, wave (y*q)*g q*(𝓕 f) (-q/r-x) := by
  unfold bagHyperbolicKernel
  apply integral_congr_ae
  filter_upwards [] with q
  rw [SchwartzMap.fourier_coe,fourier_eq_wave,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  change wave (p*q/r+x*p+y*q)*(f p*g q) = _
  rw [show p*q/r+x*p+y*q=y*q+(-(-q/r-x)*p) by ring,wave_add]
  ring

/-- Exact hyperbolic transition identity, retaining every part of both amplitudes. -/
theorem bagHyperbolicKernel_eq_transition {r : ℝ} (hr : 0 < r) (x y : ℝ)
    (f g : SchwartzMap ℝ ℂ) :
    bagHyperbolicKernel r x y f g =
      (r : ℂ)*bourgainOscillation (2*Real.pi*(-r*x*y))*
        bagHyperbolicTransition r f g (-r*y) (-r*x) := by
  let F : ℝ → ℂ := fun q => wave (y*q)*g q*(𝓕 f) (-q/r-x)
  have hc : (∫ ξ : ℝ, F (-r*x-r*ξ)) = (r : ℂ)⁻¹*(∫ q : ℝ, F q) := by
    calc
      _ = ∫ ξ : ℝ, (fun u : ℝ => F (u+(-r*x))) ((-r)*ξ) := by
        congr 1
        funext ξ
        congr 1
        ring
      _ = _ := by
        rw [Measure.integral_comp_mul_left (fun u : ℝ => F (u+(-r*x))) (-r),integral_add_right_eq_self]
        simp only [abs_inv,abs_neg,abs_of_pos hr,Complex.real_smul,Complex.ofReal_inv]
  have hp (ξ : ℝ) : F (-r*x-r*ξ) =
      wave (-r*x*y)*(wave ((-r*y)*ξ)*(𝓕 f) ξ*g (-r*x-r*ξ)) := by
    dsimp [F]
    rw [show -(-r*x-r*ξ)/r-x=ξ by field_simp; ring,
      show y*(-r*x-r*ξ)=(-r*x*y)+((-r*y)*ξ) by ring,wave_add]
    ring
  rw [kernel_partial]
  change (∫ q : ℝ, F q) = _
  calc
    _ = (r : ℂ)*(∫ ξ : ℝ, F (-r*x-r*ξ)) := by
      rw [hc,← mul_assoc,mul_inv_cancel₀ (by exact_mod_cast hr.ne'),one_mul]
    _ = (r : ℂ)*(∫ ξ : ℝ,
        wave (-r*x*y)*(wave ((-r*y)*ξ)*(𝓕 f) ξ*g (-r*x-r*ξ))) := by
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall hp)
    _ = _ := by
      rw [integral_const_mul,bagHyperbolicTransition_eq_partial]
      simp only [wave,mul_assoc]

end RHTower.BAGTrace
