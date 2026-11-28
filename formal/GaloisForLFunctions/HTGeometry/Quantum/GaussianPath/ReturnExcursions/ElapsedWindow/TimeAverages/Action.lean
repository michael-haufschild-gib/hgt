import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Gaussian time averages of damped spectral characters -/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
noncomputable section

/-- A time observation with mean m and variance v multiplies a spectral
frequency by this complex factor when its field variance is c. -/
def timeActionKernel (m u : ℝ) (c v : ℝ≥0) : ℂ :=
  let D := 1+(c:ℝ)*v
  (((sqrt D)⁻¹ * exp (-(c*m^2)/(2*D)):ℝ):ℂ) *
    Complex.exp (((u*(m/D):ℝ):ℂ)*Complex.I - (((v:ℝ)/D*u^2/2:ℝ):ℂ))

/-- Multiplying the time density by Gaussian field damping narrows its
variance and displaces its mean toward zero. -/
private theorem tilted_time_density (m t : ℝ) (c v : ℝ≥0) (hv : v ≠ 0) :
    let D := 1+(c:ℝ)*v
    gaussianPDFReal m v t * exp (-(c*t^2)/2) =
      ((sqrt D)⁻¹ * exp (-(c*m^2)/(2*D))) *
        gaussianPDFReal (m/D) (v/(1+c*v)) t := by
  intro D
  have hD : 0 < D := by dsimp [D]; positivity
  have hv' : 0 < (v:ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hD' : ((1+c*v : ℝ≥0):ℝ) = D := rfl
  have hnorm : (sqrt (2*π*(v:ℝ)))⁻¹ =
      (sqrt D)⁻¹ * (sqrt (2*π*((v:ℝ)/D)))⁻¹ := by
    rw [←mul_div_assoc,Real.sqrt_div (by positivity)]
    field_simp [(Real.sqrt_pos.mpr hD).ne', (Real.sqrt_pos.mpr (by positivity : 0<2*π*(v:ℝ))).ne']
  have hpow : -(t-m)^2/(2*(v:ℝ)) + -(c*t^2)/2 =
      -(c*m^2)/(2*D) + -(t-m/D)^2/(2*((v:ℝ)/D)) := by
    field_simp [hD.ne',hv'.ne']
    dsimp only [D]
    ring
  simp only [gaussianPDFReal_def,NNReal.coe_div,hD']
  calc
    _ = (sqrt (2*π*(v:ℝ)))⁻¹ * exp (-(t-m)^2/(2*(v:ℝ)) + -(c*t^2)/2) := by
      rw [Real.exp_add]; ring
    _ = _ := by rw [hnorm,hpow,Real.exp_add]; ring

/-- Exact time-averaged action at every variance, including a deterministic
test date and a resonant frequency. -/
theorem gaussian_time_action (m u : ℝ) (c v : ℝ≥0) :
    (∫ t : ℝ, (exp (-(c*t^2)/2):ℂ) * Complex.exp (((u*t:ℝ):ℂ)*Complex.I)
      ∂gaussianReal m v) = timeActionKernel m u c v := by
  by_cases hv : v=0
  · subst v
    simp [timeActionKernel]
  let D := 1+(c:ℝ)*v
  let v' := v/(1+c*v)
  let K := (sqrt D)⁻¹ * exp (-(c*m^2)/(2*D))
  let f (t : ℝ) := Complex.exp (((u*t:ℝ):ℂ)*Complex.I)
  have hv' : v' ≠ 0 := div_ne_zero hv (by positivity)
  have hden (t : ℝ) :
      gaussianPDFReal m v t • ((exp (-(c*t^2)/2):ℂ) * f t) =
        (K:ℂ) * (gaussianPDFReal (m/D) v' t • f t) := by
    have ht := tilted_time_density m t c v hv
    change gaussianPDFReal m v t * exp (-(c*t^2)/2) = K * gaussianPDFReal (m/D) v' t at ht
    simp only [Complex.real_smul,←mul_assoc,←Complex.ofReal_mul,ht]
  change (∫ t, (exp (-(c*t^2)/2):ℂ) * f t ∂gaussianReal m v) = _
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp_rw [hden]
  rw [integral_const_mul,←integral_gaussianReal_eq_integral_smul hv']
  have hf : (∫ t, f t ∂gaussianReal (m/D) v') = charFun (gaussianReal (m/D) v') u := by
    rw [charFun_apply_real]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [f]
    congr 1
    push_cast
    ring
  rw [hf,charFun_gaussianReal]
  unfold timeActionKernel
  congr 2
  dsimp [K,D,v']
  push_cast
  ring

#print axioms gaussian_time_action
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
