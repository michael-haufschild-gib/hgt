import GaloisForLFunctions.HTGeometry.DispersivePDE.TheGrossPitaevskiiCorrectorOfTheKdVPulse
import GaloisForLFunctions.HTGeometry.DispersivePDE.NLSSolitons
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The density shear of a grey Gross–Pitaevskii soliton

In the normalization of Schneider–Thorin, the exact grey wave has the KdV
density profile at a different speed. The speed error is quadratic in the
depth of the notch. The center discrepancy gives an exact observation on
the longer, inverse-fifth-power time scale.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.DispersivePDE

private def greyProfile (a s t x : ℝ) : ℂ :=
  ((a*solitonT (a*(x-2*s*t)) : ℝ) : ℂ) + (s:ℂ)*Complex.I

/-- Unit-background travelling grey wave; the angle parametrizes the whole
circle of admissible depths and velocities, including the black soliton. -/
def greyGPPulse (θ : ℝ) : ℝ → ℝ → ℂ := greyProfile (Real.sin θ) (Real.cos θ)

private theorem grey_derivatives (a s t x : ℝ) :
    let z := a*(x-2*s*t)
    deriv (fun τ => greyProfile a s τ x) t = ((-2*s*a^2*solitonQ z:ℝ):ℂ) ∧
    deriv (greyProfile a s t) x = ((a^2*solitonQ z:ℝ):ℂ) ∧
    deriv (deriv (greyProfile a s t)) x = ((a^3*solitonQ1 z:ℝ):ℂ) := by
  intro z
  have ht : HasDerivAt (fun τ : ℝ => a*(x-2*s*τ)) (-(2*s)*a) t := by
    have h := ((hasDerivAt_const t x).sub ((hasDerivAt_id t).const_mul (2*s))).const_mul a
    exact h.congr_deriv (by ring)
  have hx (y : ℝ) : HasDerivAt (fun w : ℝ => a*(w-2*s*t)) a y := by
    exact (((hasDerivAt_id y).sub_const (2*s*t)).const_mul a).congr_deriv (by ring)
  have time := ((((hasDerivAt_solitonT z).comp t ht).const_mul a).ofReal_comp).add_const ((s:ℂ)*Complex.I)
  have space (y : ℝ) : deriv (greyProfile a s t) y = ((a^2*solitonQ (a*(y-2*s*t)):ℝ):ℂ) := by
    have h := ((((hasDerivAt_solitonT _).comp y (hx y)).const_mul a).ofReal_comp).add_const ((s:ℂ)*Complex.I)
    exact (h.congr_deriv (by push_cast; ring)).deriv
  refine ⟨(time.congr_deriv (by push_cast; ring)).deriv,space x,?_⟩
  rw [funext space]
  have hh := (((hasDerivAt_solitonQ z).comp x (hx x)).const_mul (a^2)).ofReal_comp
  exact (hh.congr_deriv (by push_cast; ring)).deriv

/-- The density deficit equals the KdV pulse exactly at the GP speed. -/
theorem grey_density_is_kdv_pulse (θ t x : ℝ) :
    ‖greyGPPulse θ t x‖^2 = 1+acousticPulse (Real.sin θ) (x-2*Real.cos θ*t) := by
  let a := Real.sin θ
  let s := Real.cos θ
  let z := a*(x-2*s*t)
  have circle := Real.sin_sq_add_cos_sq θ
  change a^2+s^2=1 at circle
  change ‖((a*solitonT z:ℝ):ℂ)+(s:ℂ)*Complex.I‖^2 = 1 + -(a^2)*solitonQ z
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,zero_add,add_zero]
  unfold solitonQ
  linarith only [circle]

/-- The moving family solves the GP equation itself, with the actual time
derivative and second spatial derivative of its complex field. -/
theorem grey_gross_pitaevskii_equation (θ t x : ℝ) :
    Complex.I * deriv (fun τ => greyGPPulse θ τ x) t + deriv (deriv (greyGPPulse θ t)) x -
      ((2*(‖greyGPPulse θ t x‖^2-1):ℝ):ℂ)*greyGPPulse θ t x = 0 := by
  let a := Real.sin θ
  let s := Real.cos θ
  let z := a*(x-2*s*t)
  obtain ⟨ht,_,hxx⟩ := grey_derivatives a s t x
  rw [grey_density_is_kdv_pulse]
  change Complex.I*deriv (fun τ => greyProfile a s τ x) t+deriv (deriv (greyProfile a s t)) x-
    ((2*(1+ -(a^2)*solitonQ z-1):ℝ):ℂ)*(((a*solitonT z:ℝ):ℂ)+(s:ℂ)*Complex.I)=0
  rw [ht,hxx]
  change Complex.I*((-2*s*a^2*solitonQ z:ℝ):ℂ)+((a^3*solitonQ1 z:ℝ):ℂ)-_=0
  unfold solitonQ1
  push_cast
  ring

/-- The current relative to the unit background is the density deficit
multiplied by half the wave speed, including at a zero of the black wave. -/
theorem grey_current_density (θ t x : ℝ) :
    (star (greyGPPulse θ t x) * deriv (greyGPPulse θ t) x).im =
      Real.cos θ*(‖greyGPPulse θ t x‖^2-1) := by
  let a := Real.sin θ
  let s := Real.cos θ
  let z := a*(x-2*s*t)
  rw [grey_density_is_kdv_pulse]
  change (star (greyProfile a s t x)*deriv (greyProfile a s t) x).im =
    s*(1+ -(a^2)*solitonQ z-1)
  rw [(grey_derivatives a s t x).2.1]
  simp [greyProfile,Complex.mul_im,Complex.mul_re,z,sq]
  <;> ring

private theorem grey_speed_defect (θ : ℝ) :
    2*Real.cos θ-(2-(Real.sin θ)^2) = -(1-Real.cos θ)^2 := by
  linarith only [Real.sin_sq_add_cos_sq θ]

private theorem profile_variation (u v : ℝ) : |solitonQ u-solitonQ v|≤2*|u-v| := by
  have bound (x : ℝ) : ‖deriv solitonQ x‖≤2 := by
    rw [(hasDerivAt_solitonQ x).deriv,Real.norm_eq_abs,solitonQ1,abs_mul,abs_mul]
    have h₁ : |solitonT x|≤1 := (Real.abs_tanh_lt_one x).le
    have h₂ : 0 ≤ solitonQ x := by rw [solitonQ_eq_inv_cosh_sq]; positivity
    have h₃ : solitonQ x≤1 := sub_le_self _ (sq_nonneg _)
    rw [abs_of_nonneg h₂]
    norm_num
    nlinarith only [mul_le_mul h₁ h₃ h₂ zero_le_one]
  exact Convex.norm_image_sub_le_of_norm_deriv_le (s:=Set.univ) (f:=solitonQ)
    (fun x _ => (hasDerivAt_solitonQ x).differentiableAt) (fun x _ => bound x)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ v) (Set.mem_univ u)

/-- A spatially uniform bound for the density error when propagating
with the KdV speed. The only error is translation of the profile. -/
theorem grey_kdv_density_error (θ t x : ℝ) :
    let a := Real.sin θ
    let s := Real.cos θ
    |‖greyGPPulse θ t x‖^2-(1+acousticPulse a (x-(2-a^2)*t))| ≤
      2*|a|^3*(1-s)^2*|t| := by
  intro a s
  have hd := grey_speed_defect θ
  change 2*s-(2-a^2) = -(1-s)^2 at hd
  let u := a*(x-2*s*t)
  let v := a*(x-(2-a^2)*t)
  have diff : u-v = a*(1-s)^2*t := by
    dsimp only [u,v]
    linear_combination -a*t*hd
  have er : ‖greyGPPulse θ t x‖^2-(1+acousticPulse a (x-(2-a^2)*t)) =
      -(a^2)*(solitonQ u-solitonQ v) := by
    rw [grey_density_is_kdv_pulse]
    change (1+ -(a^2)*solitonQ u)-(1+ -(a^2)*solitonQ v)=_
    ring
  rw [er,abs_mul,abs_neg,abs_pow]
  have h := mul_le_mul_of_nonneg_left (profile_variation u v) (sq_nonneg |a|)
  rw [diff,abs_mul,abs_mul,abs_of_nonneg (sq_nonneg (1-s))] at h
  linarith only [h]

/-- At the true center the discrepancy has an exact hyperbolic tangent
profile. Its relative size is read at the phase drift, without estimates. -/
theorem grey_center_density_error (θ t : ℝ) :
    let a := Real.sin θ
    let s := Real.cos θ
    (1+acousticPulse a (2*s*t-(2-a^2)*t))-‖greyGPPulse θ t (2*s*t)‖^2 =
      a^2*(solitonT (a*(1-s)^2*t))^2 := by
  intro a s
  have hd := grey_speed_defect θ
  change 2*s-(2-a^2) = -(1-s)^2 at hd
  have z : a*(2*s*t-(2-a^2)*t) = -(a*(1-s)^2*t) := by
    linear_combination a*t*hd
  rw [grey_density_is_kdv_pulse]
  change (1+ -(a^2)*solitonQ (a*(2*s*t-(2-a^2)*t)))-
    (1+ -(a^2)*solitonQ (a*(2*s*t-2*s*t)))=_
  rw [z,sub_self,mul_zero]
  simp only [solitonQ,solitonT,Real.tanh_zero,Real.tanh_neg,neg_sq,zero_pow (by decide : 2≠0),sub_zero]
  ring

/-- At the inverse fifth power of the inverse width, a fixed positive
fraction of the full density depth is lost by the KdV speed prediction. -/
theorem grey_fifth_power_observation (θ u : ℝ) (ha : Real.sin θ≠0) :
    let a := Real.sin θ
    let s := Real.cos θ
    let t := (1+s)^2*u/a^5
    (1+acousticPulse a (2*s*t-(2-a^2)*t))-‖greyGPPulse θ t (2*s*t)‖^2 =
      a^2*(solitonT u)^2 := by
  intro a s t
  rw [grey_center_density_error]
  have circle := Real.sin_sq_add_cos_sq θ
  change a^2+s^2=1 at circle
  have prod : (1-s)*(1+s)=a^2 := by linarith only [circle]
  have phase : a*(1-s)^2*t=u := by
    dsimp only [t]
    field_simp [show a≠0 from ha]
    first
      | linear_combination u*((1-s)*(1+s)+a^2)*prod
      | linear_combination a*u*((1-s)*(1+s)+a^2)*prod
  change a^2*(solitonT (a*(1-s)^2*t))^2=_
  rw [phase]

end GaloisForLFunctions.HTGeometry.DispersivePDE
