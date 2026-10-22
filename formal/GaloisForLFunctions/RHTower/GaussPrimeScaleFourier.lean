import GaloisForLFunctions.RHTower.GaussComponentAmplitude
import GaloisForLFunctions.RHTower.CCM.CCMHalfUnitExtrapolationCost
import GaloisForLFunctions.HTGeometry.FourierCircleTranslation

/-!
# Fourier coefficients of the prime-scale amplitude

The amplitude carried by the prime block of a Gauss component is `b_p(x) = p^{(1-x)/2}` on one
period.  Its Fourier coefficients are elementary and explicit,

`b̂(j) = (√p - 1) / (log p / 2 + 2π i j)`,

and they decay like `1/(1 + |j|)`.  Both facts are what the moving-translation estimate consumes:
the exact value fixes the limiting amplitude, and the decay controls the high-frequency tail.
-/

namespace RHTower

open Complex Filter intervalIntegral

noncomputable section

/-- The prime-scale amplitude `b_p(x) = p^{(1-x)/2}` on one period. -/
def gaussPrimeScale (p : ℝ) (x : ℝ) : ℝ :=
  Real.exp ((1 - x) * Real.log p / 2)

theorem gaussPrimeScale_pos (p x : ℝ) : 0 < gaussPrimeScale p x :=
  Real.exp_pos _

theorem gaussPrimeScale_eq_rpow {p : ℝ} (hp : 0 < p) (x : ℝ) :
    gaussPrimeScale p x = p ^ ((1 - x) / 2) := by
  rw [gaussPrimeScale, Real.rpow_def_of_pos hp]
  ring_nf

theorem gaussPrimeScale_zero {p : ℝ} (hp : 0 < p) :
    gaussPrimeScale p 0 = Real.sqrt p := by
  rw [gaussPrimeScale]
  simpa using GaloisForLFunctions.RHTower.exp_log_div_two p hp

theorem gaussPrimeScale_one (p : ℝ) : gaussPrimeScale p 1 = 1 := by
  simp [gaussPrimeScale]

/-- The `j`th Fourier coefficient of the prime-scale amplitude. -/
def gaussPrimeScaleFourierCoefficient (p : ℝ) (j : ℤ) : ℂ :=
  ((Real.sqrt p - 1 : ℝ) : ℂ) /
    (((Real.log p / 2 : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (j : ℂ))

theorem gaussPrimeScaleFourier_denom_re {p : ℝ} (j : ℤ) :
    (((Real.log p / 2 : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)).re
      = Real.log p / 2 := by
  simp

theorem gaussPrimeScaleFourier_denom_im {p : ℝ} (j : ℤ) :
    (((Real.log p / 2 : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)).im
      = 2 * Real.pi * (j : ℝ) := by
  simp

theorem gaussPrimeScaleFourier_denom_ne_zero {p : ℝ} (hp : 1 < p) (j : ℤ) :
    ((Real.log p / 2 : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) ≠ 0 := by
  intro h
  have hre := gaussPrimeScaleFourier_denom_re (p := p) j
  rw [h] at hre
  have hlog : 0 < Real.log p := Real.log_pos hp
  simp only [Complex.zero_re] at hre
  linarith

/-- **The Fourier coefficients of the prime-scale amplitude.**  On one period,
`∫₀¹ b_p(x) e^{-2π i j x} dx = (√p - 1)/(log p / 2 + 2π i j)`. -/
theorem intervalIntegral_gaussPrimeScale_fourier {p : ℝ} (hp : 1 < p) (j : ℤ) :
    (∫ x in (0:ℝ)..1,
        (gaussPrimeScale p x : ℂ) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (x : ℂ))))
      = gaussPrimeScaleFourierCoefficient p j := by
  have hppos : (0 : ℝ) < p := lt_trans zero_lt_one hp
  set z : ℂ := ((Real.log p / 2 : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) with hz
  have hzne : z ≠ 0 := gaussPrimeScaleFourier_denom_ne_zero hp j
  have hcne : -z ≠ 0 := neg_ne_zero.mpr hzne
  have hint : ∀ x : ℝ,
      (gaussPrimeScale p x : ℂ) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (x : ℂ)))
        = Complex.exp (((Real.log p / 2 : ℝ) : ℂ)) * Complex.exp (-z * (x : ℂ)) := by
    intro x
    rw [gaussPrimeScale, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [hz]
    push_cast
    ring
  rw [intervalIntegral.integral_congr (fun x _ => hint x),
    intervalIntegral.integral_const_mul, integral_exp_mul_complex hcne]
  have hexp : Complex.exp (-z * (1 : ℝ)) = Complex.exp (-((Real.log p / 2 : ℝ) : ℂ)) := by
    rw [hz]
    have hunit : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ))) = 1 := by
      have h := Complex.exp_int_mul_two_pi_mul_I (-j)
      rw [show ((-j : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
          = -(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)) by push_cast; ring] at h
      exact h
    rw [show -(((Real.log p / 2 : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)) *
        ((1 : ℝ) : ℂ)
        = -((Real.log p / 2 : ℝ) : ℂ) + -(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)) by
      push_cast; ring]
    rw [Complex.exp_add, hunit, mul_one]
  rw [hexp]
  have hzero : Complex.exp (-z * ((0 : ℝ) : ℂ)) = 1 := by
    simp
  rw [hzero]
  have hsqrt : Complex.exp (((Real.log p / 2 : ℝ) : ℂ)) = ((Real.sqrt p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, GaloisForLFunctions.RHTower.exp_log_div_two p hppos]
  have hsqrtinv : Complex.exp (-((Real.log p / 2 : ℝ) : ℂ)) = ((Real.sqrt p : ℝ) : ℂ)⁻¹ := by
    rw [Complex.exp_neg, hsqrt]
  rw [hsqrt, hsqrtinv, gaussPrimeScaleFourierCoefficient, ← hz]
  have hspos : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr hppos
  have hsne : ((Real.sqrt p : ℝ) : ℂ) ≠ 0 := by
    simpa using hspos.ne'
  field_simp
  push_cast
  ring

/-! ## Decay of the coefficients -/

theorem one_lt_sqrt {p : ℝ} (hp : 1 < p) : 1 < Real.sqrt p := by
  have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) hp
  simpa using h

/-- **Coefficient decay.**  The prime-scale Fourier coefficients are `O(1/(1 + |j|))`, with an
explicit constant depending only on `p`. -/
theorem norm_gaussPrimeScaleFourierCoefficient_le {p : ℝ} (hp : 1 < p) (j : ℤ) :
    ‖gaussPrimeScaleFourierCoefficient p j‖ ≤
      (2 * (Real.sqrt p - 1) / min (Real.log p / 2) (2 * Real.pi)) / (1 + |(j : ℝ)|) := by
  set z : ℂ := ((Real.log p / 2 : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) with hz
  set M : ℝ := min (Real.log p / 2) (2 * Real.pi) with hM
  have hlog : 0 < Real.log p := Real.log_pos hp
  have hMpos : 0 < M := lt_min (by linarith) (by positivity)
  have hjabs : (0 : ℝ) ≤ |(j : ℝ)| := abs_nonneg _
  have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hre' : Real.log p / 2 ≤ ‖z‖ := by
    have hval : z.re = Real.log p / 2 := gaussPrimeScaleFourier_denom_re (p := p) j
    rw [hval] at hre
    rw [abs_of_pos (by linarith)] at hre
    exact hre
  have him' : 2 * Real.pi * |(j : ℝ)| ≤ ‖z‖ := by
    have hval : z.im = 2 * Real.pi * (j : ℝ) := gaussPrimeScaleFourier_denom_im (p := p) j
    rw [hval] at him
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at him
    exact him
  have hlower : M * (1 + |(j : ℝ)|) ≤ 2 * ‖z‖ := by
    have h1 : M ≤ Real.log p / 2 := min_le_left _ _
    have h2 : M ≤ 2 * Real.pi := min_le_right _ _
    have h3 : M * |(j : ℝ)| ≤ 2 * Real.pi * |(j : ℝ)| :=
      mul_le_mul_of_nonneg_right h2 hjabs
    nlinarith [hre', him']
  have hznorm : 0 < ‖z‖ := by
    nlinarith [hlower, hMpos, hjabs]
  have hnum : (0 : ℝ) ≤ Real.sqrt p - 1 := by
    have := one_lt_sqrt hp
    linarith
  have hnorm : ‖gaussPrimeScaleFourierCoefficient p j‖ = (Real.sqrt p - 1) / ‖z‖ := by
    rw [gaussPrimeScaleFourierCoefficient, ← hz, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hnum]
  have hA : (0 : ℝ) < M * (1 + |(j : ℝ)|) := by positivity
  have hsplit : 2 * (Real.sqrt p - 1) / M / (1 + |(j : ℝ)|)
      = 2 * (Real.sqrt p - 1) / (M * (1 + |(j : ℝ)|)) := by
    rw [div_div]
  rw [hnorm, hsplit, le_div_iff₀ hA, div_mul_eq_mul_div, div_le_iff₀ hznorm]
  nlinarith [hlower, hnum, hznorm]

/-! ## The circle representative -/

/-- The prime-scale amplitude as a function on the circle. -/
def gaussPrimeScaleCircle (p : ℝ) : AddCircle (1 : ℝ) → ℂ :=
  AddCircle.liftIoc 1 0 (fun x => (gaussPrimeScale p x : ℂ))

theorem gaussPrimeScaleCircle_coe {p x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    gaussPrimeScaleCircle p ((x : ℝ) : AddCircle (1 : ℝ)) = (gaussPrimeScale p x : ℂ) := by
  rw [gaussPrimeScaleCircle]
  exact AddCircle.liftIoc_coe_apply (by simpa using hx)

/-- **The Fourier coefficients of the prime-scale amplitude**, in the circle normalization. -/
theorem fourierCoeff_gaussPrimeScaleCircle {p : ℝ} (hp : 1 < p) (j : ℤ) :
    fourierCoeff (gaussPrimeScaleCircle p) j = gaussPrimeScaleFourierCoefficient p j := by
  rw [fourierCoeff_eq_intervalIntegral (gaussPrimeScaleCircle p) j 0,
    ← intervalIntegral_gaussPrimeScale_fourier hp j]
  simp only [one_div, inv_one, one_smul, zero_add]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with x hx
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  rw [gaussPrimeScaleCircle_coe hx, fourier_coe_apply, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

/-- **The moving target of the translation estimate.**  Translating the prime-scale amplitude by
`δ` multiplies its `j`th coefficient by `e^{-2π i j δ}`. -/
theorem fourierCoeff_gaussPrimeScaleCircle_translate {p : ℝ} (hp : 1 < p) (j : ℤ)
    (δ : AddCircle (1 : ℝ)) :
    fourierCoeff (fun x => gaussPrimeScaleCircle p (x - δ)) j =
      fourier (-j) δ * gaussPrimeScaleFourierCoefficient p j := by
  rw [GaloisForLFunctions.fourierCoeff_comp_sub, fourierCoeff_gaussPrimeScaleCircle hp]

end

end RHTower
