import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Fourier transforms on a symmetric aperture: the exponential basis and two decay bounds

Three elementary facts used in the localization of Weil's quadratic form to `(-a,a)`.

* The Fourier transform of a pure phase on the aperture is a shifted sine quotient,

  `∫_{-a}^a e^{iξx} dx = 2 sin(ξa)/ξ`;

  specializing `ξ = z + nπ/a` gives `ê_n(z) = 2 sin(az + nπ)/(z + nπ/a)` for the exponential
  basis `e_n(x) = e^{iπnx/a}` of `L²(-a,a)`.

* The trivial `L¹` bound `|ŵ(z)| ≤ ∫|w|`.

* The integration-by-parts bound

  `|ŵ(z)| ≤ (|w(a)| + |w(-a)| + ‖w'‖_{L¹})/|z|`,

  which is what turns a boundary cut-off of small support into an `O(|z|^{-1})` frequency profile
  uniformly in the cut-off scale.

Together the last two give, for a family supported in two intervals of total length `2ε` with
uniformly bounded `L¹` derivative norm, the logarithmic-window bound
`∫ log(3+|z|)|ŵ_ε(z)|² dz ≪ ε log(1/ε)`.
-/

open Complex MeasureTheory Set intervalIntegral

noncomputable section

namespace RHTower

/-! ## The exponential basis -/

/-- `∫_{-a}^a e^{iξx} dx = 2 sin(ξa)/ξ` for `ξ ≠ 0`. -/
theorem intervalIntegral_exp_phase (a ξ : ℝ) (hξ : ξ ≠ 0) :
    (∫ x in (-a)..a, Complex.exp (((ξ * x : ℝ) : ℂ) * I))
      = 2 * ((Real.sin (ξ * a) : ℝ) : ℂ) / ((ξ : ℝ) : ℂ) := by
  have hξC : ((ξ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ
  have hderiv : ∀ x ∈ uIcc (-a) a,
      HasDerivAt (fun t : ℝ => Complex.exp (((ξ : ℂ) * t) * I) / (((ξ : ℝ) : ℂ) * I))
        (Complex.exp (((ξ * x : ℝ) : ℂ) * I)) x := by
    intro x _
    have hlin : HasDerivAt (fun t : ℝ => ((ξ : ℂ) * t) * I) ((ξ : ℂ) * I) x := by
      simpa using (((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (ξ : ℂ)).mul_const I)
    have hexp : HasDerivAt (fun t : ℝ => Complex.exp (((ξ : ℂ) * t) * I))
        (Complex.exp (((ξ : ℂ) * x) * I) * ((ξ : ℂ) * I)) x := hlin.cexp
    have := hexp.div_const (((ξ : ℝ) : ℂ) * I)
    have hval : Complex.exp (((ξ : ℂ) * x) * I) * ((ξ : ℂ) * I) / (((ξ : ℝ) : ℂ) * I)
        = Complex.exp (((ξ * x : ℝ) : ℂ) * I) := by
      rw [mul_div_assoc, div_self (mul_ne_zero hξC Complex.I_ne_zero), mul_one]
      push_cast
      ring_nf
    rwa [hval] at this
  have hint : IntervalIntegrable (fun x : ℝ => Complex.exp (((ξ * x : ℝ) : ℂ) * I))
      volume (-a) a := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hsin : Complex.exp (((ξ : ℂ) * a) * I) - Complex.exp (((ξ : ℂ) * (-a)) * I)
      = 2 * I * ((Real.sin (ξ * a) : ℝ) : ℂ) := by
    have h1 : ((ξ : ℂ) * (-a)) = -((ξ : ℂ) * a) := by ring
    rw [h1, Complex.exp_mul_I, show -((ξ : ℂ) * a) * I = (-((ξ : ℂ) * a)) * I by ring,
      Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    have : ((Real.sin (ξ * a) : ℝ) : ℂ) = Complex.sin ((ξ : ℂ) * a) := by
      rw [← Complex.ofReal_sin]
      push_cast
      ring_nf
    rw [this]
    ring
  rw [div_sub_div_same, hsin]
  field_simp
  ring

/-- Suzuki's exponential basis `e_n(x) = e^{iπnx/a}` has Fourier transform
`2 sin(az + nπ)/(z + nπ/a)`. -/
theorem intervalIntegral_expBasis_fourier (a : ℝ) (ha : a ≠ 0) (n : ℤ) (z : ℝ)
    (hξ : z + n * Real.pi / a ≠ 0) :
    (∫ x in (-a)..a, Complex.exp (((n * Real.pi / a * x : ℝ) : ℂ) * I)
        * Complex.exp (((z * x : ℝ) : ℂ) * I))
      = 2 * ((Real.sin (a * z + n * Real.pi) : ℝ) : ℂ)
          / (((z + n * Real.pi / a : ℝ) : ℂ)) := by
  have hmerge : ∀ x : ℝ,
      Complex.exp (((n * Real.pi / a * x : ℝ) : ℂ) * I)
          * Complex.exp (((z * x : ℝ) : ℂ) * I)
        = Complex.exp ((((z + n * Real.pi / a) * x : ℝ) : ℂ) * I) := by
    intro x
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hmerge]
  rw [intervalIntegral_exp_phase a _ hξ]
  congr 2
  have : (z + n * Real.pi / a) * a = a * z + n * Real.pi := by
    field_simp
    ring
  rw [this]

/-! ## Two decay bounds -/

/-- The trivial `L¹` bound for an aperture Fourier transform. -/
theorem norm_intervalIntegral_fourier_le_l1 {a : ℝ} (ha : -a ≤ a) (w : ℝ → ℂ) (z : ℝ)
    (hw : IntervalIntegrable w volume (-a) a) :
    ‖∫ x in (-a)..a, w x * Complex.exp (((z * x : ℝ) : ℂ) * I)‖
      ≤ ∫ x in (-a)..a, ‖w x‖ := by
  refine (intervalIntegral.norm_integral_le_abs_integral_norm).trans ?_
  have hcongr : (∫ x in (-a)..a, ‖w x * Complex.exp (((z * x : ℝ) : ℂ) * I)‖)
      = ∫ x in (-a)..a, ‖w x‖ := by
    refine intervalIntegral.integral_congr ?_
    intro x _
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [hcongr, abs_of_nonneg]
  exact intervalIntegral.integral_nonneg ha fun _ _ => norm_nonneg _

/-- **The integration-by-parts decay bound.**  For a function with an interval-integrable
derivative,

`|ŵ(z)| ≤ (|w(a)| + |w(-a)| + ‖w'‖_{L¹})/|z|`. -/
theorem norm_intervalIntegral_fourier_le_ibp {a : ℝ} (ha : -a ≤ a) {w w' : ℝ → ℂ} {z : ℝ}
    (hz : z ≠ 0)
    (hderiv : ∀ x ∈ uIcc (-a) a, HasDerivAt w (w' x) x)
    (hw' : IntervalIntegrable w' volume (-a) a) :
    ‖∫ x in (-a)..a, w x * Complex.exp (((z * x : ℝ) : ℂ) * I)‖
      ≤ (‖w a‖ + ‖w (-a)‖ + ∫ x in (-a)..a, ‖w' x‖) / |z| := by
  have hzC : ((z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
  set V : ℝ → ℂ := fun t => Complex.exp (((z : ℂ) * t) * I) / (((z : ℝ) : ℂ) * I) with hV
  have hVderiv : ∀ x ∈ uIcc (-a) a,
      HasDerivAt V (Complex.exp (((z * x : ℝ) : ℂ) * I)) x := by
    intro x _
    have hlin : HasDerivAt (fun t : ℝ => ((z : ℂ) * t) * I) ((z : ℂ) * I) x := by
      simpa using (((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (z : ℂ)).mul_const I)
    have hexp : HasDerivAt (fun t : ℝ => Complex.exp (((z : ℂ) * t) * I))
        (Complex.exp (((z : ℂ) * x) * I) * ((z : ℂ) * I)) x := hlin.cexp
    have hdiv := hexp.div_const (((z : ℝ) : ℂ) * I)
    have hval : Complex.exp (((z : ℂ) * x) * I) * ((z : ℂ) * I) / (((z : ℝ) : ℂ) * I)
        = Complex.exp (((z * x : ℝ) : ℂ) * I) := by
      rw [mul_div_assoc, div_self (mul_ne_zero hzC Complex.I_ne_zero), mul_one]
      push_cast
      ring_nf
    rwa [hval] at hdiv
  have hVnorm : ∀ x : ℝ, ‖V x‖ = 1 / |z| := by
    intro x
    rw [hV]
    simp only [norm_div, norm_mul]
    rw [show ((z : ℂ) * x) = (((z * x : ℝ) : ℂ)) from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      mul_one]
  have hexpInt : IntervalIntegrable (fun x : ℝ => Complex.exp (((z * x : ℝ) : ℂ) * I))
      volume (-a) a := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hderiv hVderiv hw' hexpInt]
  have hbound : ‖w a * V a - w (-a) * V (-a) - ∫ x in (-a)..a, w' x * V x‖
      ≤ ‖w a‖ * (1 / |z|) + ‖w (-a)‖ * (1 / |z|)
        + (∫ x in (-a)..a, ‖w' x‖) * (1 / |z|) := by
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖w a * V a - w (-a) * V (-a)‖ ≤ ‖w a‖ * (1 / |z|) + ‖w (-a)‖ * (1 / |z|) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, hVnorm, hVnorm]
    have h2 : ‖∫ x in (-a)..a, w' x * V x‖ ≤ (∫ x in (-a)..a, ‖w' x‖) * (1 / |z|) := by
      refine (intervalIntegral.norm_integral_le_abs_integral_norm).trans ?_
      have hcongr : (∫ x in (-a)..a, ‖w' x * V x‖)
          = ∫ x in (-a)..a, ‖w' x‖ * (1 / |z|) := by
        refine intervalIntegral.integral_congr ?_
        intro x _
        rw [norm_mul, hVnorm]
      rw [hcongr, intervalIntegral.integral_mul_const, abs_of_nonneg]
      have hnn : 0 ≤ ∫ x in (-a)..a, ‖w' x‖ :=
        intervalIntegral.integral_nonneg ha fun _ _ => norm_nonneg _
      positivity
    linarith
  refine hbound.trans ?_
  rw [div_eq_mul_one_div]
  ring_nf
  exact le_of_eq rfl

end RHTower
