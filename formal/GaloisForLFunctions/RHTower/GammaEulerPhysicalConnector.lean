import GaloisForLFunctions.HTGeometry.CoshFourierTransform
import GaloisForLFunctions.RHTower.GammaEulerCharacteristicPositivity
import GaloisForLFunctions.RHTower.GammaEulerTwoChannelAsymptotic
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Physical Gamma--Euler connector

This module realizes the abstract hyperbolic characteristic used by the Gamma--Euler tail-parity
theorems as the literal normalized vertical Gamma density.  It also realizes every finite list of
Euler differences as multiplication by the corresponding normalized squared Euler factors.
-/

open Complex Filter MeasureTheory Real Set
open scoped ENNReal FourierTransform FourierTransformInv Topology

namespace RHTower

noncomputable section

/-! ## Fourier inversion for every positive hyperbolic power -/

/-- The complex-valued hyperbolic characteristic before the `u / 2` rescaling. -/
def gammaCoshPower (r : ℝ) (u : ℝ) : ℂ :=
  ((Real.cosh u ^ (-r) : ℝ) : ℂ)

def gammaCoshPowerDeriv (r : ℝ) (u : ℝ) : ℂ :=
  ((-r * Real.cosh u ^ (-r - 1) * Real.sinh u : ℝ) : ℂ)

def gammaCoshPowerDeriv2 (r : ℝ) (u : ℝ) : ℂ :=
  ((r ^ 2 * Real.cosh u ^ (-r) -
      r * (r + 1) * Real.cosh u ^ (-r - 2) : ℝ) : ℂ)

theorem hasDerivAt_gammaCoshPowerReal (r u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.cosh v ^ (-r))
      (-r * Real.cosh u ^ (-r - 1) * Real.sinh u) u := by
  have hc : 0 < Real.cosh u := Real.cosh_pos u
  have h := (Real.hasDerivAt_cosh u).rpow_const (p := -r) (Or.inl hc.ne')
  convert h using 1 <;> ring

theorem hasDerivAt_gammaCoshPowerDerivReal (r u : ℝ) :
    HasDerivAt
      (fun v : ℝ => -r * Real.cosh v ^ (-r - 1) * Real.sinh v)
      (r ^ 2 * Real.cosh u ^ (-r) -
        r * (r + 1) * Real.cosh u ^ (-r - 2)) u := by
  have hc : 0 < Real.cosh u := Real.cosh_pos u
  have hp := (Real.hasDerivAt_cosh u).rpow_const
    (p := -r - 1) (Or.inl hc.ne')
  have h := (hp.const_mul (-r)).mul (Real.hasDerivAt_sinh u)
  have hpow1 : Real.cosh u ^ (-r - 1) * Real.cosh u = Real.cosh u ^ (-r) := by
    nth_rewrite 2 [show Real.cosh u = Real.cosh u ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hc]
    congr 1
    ring
  have hpow2 : Real.cosh u ^ (-r - 2) * Real.cosh u ^ (2 : ℝ) =
      Real.cosh u ^ (-r) := by
    rw [← Real.rpow_add hc]
    congr 1
    ring
  have hsq : Real.cosh u ^ (2 : ℝ) = Real.cosh u ^ (2 : ℕ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hsinh : Real.sinh u ^ 2 = Real.cosh u ^ 2 - 1 := by
    linarith [Real.cosh_sq_sub_sinh_sq u]
  have hkey : Real.cosh u ^ (-r - 2) * Real.sinh u ^ 2 =
      Real.cosh u ^ (-r) - Real.cosh u ^ (-r - 2) := by
    rw [hsinh, mul_sub, mul_one, ← hsq, hpow2]
  have hval :
      -r * (Real.sinh u * (-r - 1) * Real.cosh u ^ (-r - 1 - 1)) * Real.sinh u +
          -r * Real.cosh u ^ (-r - 1) * Real.cosh u =
        r ^ 2 * Real.cosh u ^ (-r) -
          r * (r + 1) * Real.cosh u ^ (-r - 2) := by
    rw [show -r - 1 - 1 = -r - 2 by ring]
    linear_combination r * (r + 1) * hkey - r * hpow1
  rwa [hval] at h

theorem hasDerivAt_gammaCoshPower (r u : ℝ) :
    HasDerivAt (gammaCoshPower r) (gammaCoshPowerDeriv r u) u :=
  (hasDerivAt_gammaCoshPowerReal r u).ofReal_comp

theorem hasDerivAt_gammaCoshPowerDeriv (r u : ℝ) :
    HasDerivAt (gammaCoshPowerDeriv r) (gammaCoshPowerDeriv2 r u) u :=
  (hasDerivAt_gammaCoshPowerDerivReal r u).ofReal_comp

theorem differentiable_gammaCoshPower (r : ℝ) : Differentiable ℝ (gammaCoshPower r) :=
  fun u => (hasDerivAt_gammaCoshPower r u).differentiableAt

theorem differentiable_gammaCoshPowerDeriv (r : ℝ) :
    Differentiable ℝ (gammaCoshPowerDeriv r) :=
  fun u => (hasDerivAt_gammaCoshPowerDeriv r u).differentiableAt

theorem deriv_gammaCoshPower (r : ℝ) :
    deriv (gammaCoshPower r) = gammaCoshPowerDeriv r :=
  funext fun u => (hasDerivAt_gammaCoshPower r u).deriv

theorem deriv_gammaCoshPowerDeriv (r : ℝ) :
    deriv (gammaCoshPowerDeriv r) = gammaCoshPowerDeriv2 r :=
  funext fun u => (hasDerivAt_gammaCoshPowerDeriv r u).deriv

theorem continuous_gammaCoshPower (r : ℝ) : Continuous (gammaCoshPower r) :=
  (differentiable_gammaCoshPower r).continuous

theorem integrable_gammaCoshPower {r : ℝ} (hr : 0 < r) :
    Integrable (gammaCoshPower r) := by
  exact (HTGeometry.integrable_cosh_rpow_neg hr).ofReal.congr
    (by filter_upwards with u using rfl)

theorem integrable_gammaCoshPowerDeriv {r : ℝ} (hr : 0 < r) :
    Integrable (gammaCoshPowerDeriv r) := by
  have hbase :=
    (HTGeometry.integrable_cosh_rpow_neg hr).const_mul r
  refine hbase.mono' ?_ ?_
  · exact (differentiable_gammaCoshPowerDeriv r).continuous.aestronglyMeasurable
  · filter_upwards with u
    have hc : 0 < Real.cosh u := Real.cosh_pos u
    have habs : |Real.sinh u| ≤ Real.cosh u := by
      nlinarith [Real.cosh_sq_sub_sinh_sq u, sq_abs (Real.sinh u),
        abs_nonneg (Real.sinh u)]
    have hpow : Real.cosh u ^ (-r - 1) * Real.cosh u =
        Real.cosh u ^ (-r) := by
      nth_rewrite 2 [show Real.cosh u = Real.cosh u ^ (1 : ℝ) by rw [Real.rpow_one]]
      rw [← Real.rpow_add hc]
      congr 1
      ring
    have hpowPos : 0 ≤ Real.cosh u ^ (-r - 1) :=
      (Real.rpow_pos_of_pos hc _).le
    rw [gammaCoshPowerDeriv, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_neg, abs_of_pos hr, abs_of_nonneg hpowPos]
    calc
      r * Real.cosh u ^ (-r - 1) * |Real.sinh u|
          ≤ r * Real.cosh u ^ (-r - 1) * Real.cosh u := by gcongr
      _ = r * Real.cosh u ^ (-r) := by rw [mul_assoc, hpow]

theorem integrable_gammaCoshPowerDeriv2 {r : ℝ} (hr : 0 < r) :
    Integrable (gammaCoshPowerDeriv2 r) := by
  have h1 :=
    (HTGeometry.integrable_cosh_rpow_neg hr).const_mul (r ^ 2)
  have h2 :=
    (HTGeometry.integrable_cosh_rpow_neg (by linarith : 0 < r + 2)).const_mul
      (r * (r + 1))
  apply (h1.sub h2).ofReal.congr
  filter_upwards with u
  unfold gammaCoshPowerDeriv2
  simp only [Pi.sub_apply]
  push_cast
  rw [show -(r + 2) = -r - 2 by ring]
  rfl

theorem fourier_gammaCoshPowerDeriv2 {r : ℝ} (hr : 0 < r) (x : ℝ) :
    𝓕 (gammaCoshPowerDeriv2 r) x =
      (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ 2 * 𝓕 (gammaCoshPower r) x := by
  have h1 := Real.fourier_deriv (integrable_gammaCoshPower hr)
    (differentiable_gammaCoshPower r)
    (by rw [deriv_gammaCoshPower]; exact integrable_gammaCoshPowerDeriv hr)
  have h2 := Real.fourier_deriv (integrable_gammaCoshPowerDeriv hr)
    (differentiable_gammaCoshPowerDeriv r)
    (by rw [deriv_gammaCoshPowerDeriv]; exact integrable_gammaCoshPowerDeriv2 hr)
  rw [deriv_gammaCoshPower] at h1
  rw [deriv_gammaCoshPowerDeriv] at h2
  have e2 : 𝓕 (gammaCoshPowerDeriv2 r) x =
      (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) •
        𝓕 (gammaCoshPowerDeriv r) x := by rw [h2]
  have e1 : 𝓕 (gammaCoshPowerDeriv r) x =
      (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) •
        𝓕 (gammaCoshPower r) x := by rw [h1]
  rw [e2, e1, smul_eq_mul, smul_eq_mul]
  ring

theorem integrable_fourier_gammaCoshPower {r : ℝ} (hr : 0 < r) :
    Integrable (𝓕 (gammaCoshPower r)) := by
  have hA : 0 ≤ ∫ u : ℝ, ‖gammaCoshPower r u‖ :=
    integral_nonneg fun u => norm_nonneg _
  have hB : 0 ≤ ∫ u : ℝ, ‖gammaCoshPowerDeriv2 r u‖ :=
    integral_nonneg fun u => norm_nonneg _
  have hpi : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hbound : ∀ x : ℝ, ‖𝓕 (gammaCoshPower r) x‖ ≤
      2 * ((∫ u : ℝ, ‖gammaCoshPower r u‖) +
        ∫ u : ℝ, ‖gammaCoshPowerDeriv2 r u‖) * (1 + x ^ 2)⁻¹ := by
    intro x
    have hpos : 0 < 1 + x ^ 2 := by positivity
    have hN : 0 ≤ ‖𝓕 (gammaCoshPower r) x‖ := norm_nonneg _
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    by_cases hx : x ^ 2 ≤ 1
    · have h1 : ‖𝓕 (gammaCoshPower r) x‖ ≤
          ∫ u : ℝ, ‖gammaCoshPower r u‖ :=
        VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
      nlinarith [h1, hA, hB, hN]
    · have hx' : 1 < x ^ 2 := not_le.mp hx
      have heq := fourier_gammaCoshPowerDeriv2 hr x
      have hval : ‖(2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ 2‖ =
          4 * Real.pi ^ 2 * x ^ 2 := by
        rw [norm_pow]
        simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, Complex.norm_ofNat]
        rw [abs_of_pos Real.pi_pos, mul_pow, mul_pow, sq_abs]
        ring
      have hle : ‖𝓕 (gammaCoshPowerDeriv2 r) x‖ ≤
          ∫ u : ℝ, ‖gammaCoshPowerDeriv2 r u‖ :=
        VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
      rw [heq, norm_mul, hval] at hle
      have hstep1 : ‖𝓕 (gammaCoshPower r) x‖ * x ^ 2 ≤
          ‖𝓕 (gammaCoshPower r) x‖ * x ^ 2 * (4 * Real.pi ^ 2) := by
        have := mul_le_mul_of_nonneg_left hpi
          (by positivity : 0 ≤ ‖𝓕 (gammaCoshPower r) x‖ * x ^ 2)
        nlinarith
      have hstep2 : ‖𝓕 (gammaCoshPower r) x‖ * x ^ 2 ≤
          ∫ u : ℝ, ‖gammaCoshPowerDeriv2 r u‖ := by nlinarith
      have hprod : 0 ≤ ‖𝓕 (gammaCoshPower r) x‖ * (x ^ 2 - 1) :=
        mul_nonneg hN (by linarith)
      nlinarith
  refine Integrable.mono' (g := fun x : ℝ =>
    2 * ((∫ u : ℝ, ‖gammaCoshPower r u‖) +
      ∫ u : ℝ, ‖gammaCoshPowerDeriv2 r u‖) * (1 + x ^ 2)⁻¹) ?_ ?_
      (Filter.Eventually.of_forall hbound)
  · exact integrable_inv_one_add_sq.const_mul _
  · refine (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar ?_
      (integrable_gammaCoshPower hr)).aestronglyMeasurable
    fun_prop

theorem fourierInv_fourier_gammaCoshPower {r : ℝ} (hr : 0 < r) :
    𝓕⁻ (𝓕 (gammaCoshPower r)) = gammaCoshPower r :=
  (continuous_gammaCoshPower r).fourierInv_fourier_eq
    (integrable_gammaCoshPower hr) (integrable_fourier_gammaCoshPower hr)

/-! ## Literal normalized Gamma height law -/

/-- The normalized Gamma height density
`2^(r-1)/(π Γ(r)) * |Γ(r/2+it)|²`. -/
def gammaHeightDensity (r t : ℝ) : ℝ :=
  (2 : ℝ) ^ (r - 1) *
    Complex.normSq (Complex.Gamma (((r : ℂ) + (2 * t : ℝ) * Complex.I) / 2)) /
      (Real.pi * Real.Gamma r)

theorem gammaHeightDensity_nonneg {r : ℝ} (hr : 0 < r) (t : ℝ) :
    0 ≤ gammaHeightDensity r t := by
  unfold gammaHeightDensity
  have hG : 0 < Real.Gamma r := Real.Gamma_pos_of_pos hr
  exact div_nonneg
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Complex.normSq_nonneg _))
    (mul_nonneg Real.pi_pos.le hG.le)

theorem fourier_gammaCoshPower_apply {r : ℝ} (hr : 0 < r) (x : ℝ) :
    𝓕 (gammaCoshPower r) x =
      (((2 : ℝ) ^ (r - 1) *
        Complex.normSq (Complex.Gamma (((r : ℂ) + (2 * Real.pi * x : ℝ) * Complex.I) / 2)) /
          Real.Gamma r : ℝ) : ℂ) := by
  rw [Real.fourier_eq]
  have hcongr : ∀ u : ℝ, (𝐞 (-(inner ℝ u x)) • gammaCoshPower r u) =
      (((Real.cosh u) ^ (-r) : ℝ) : ℂ) *
        Complex.exp (-(((2 * Real.pi * x : ℝ) : ℂ) * (u : ℂ)) * Complex.I) := by
    intro u
    have hexp : ((2 * Real.pi * (-(u * x)) : ℝ) : ℂ) * Complex.I =
        -(((2 * Real.pi * x : ℝ) : ℂ) * (u : ℂ)) * Complex.I := by
      push_cast
      ring
    rw [Real.inner_apply, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul,
      gammaCoshPower, hexp]
    ring
  simp_rw [hcongr]
  simpa using HTGeometry.integral_cosh_rpow_neg_mul_exp_eq_ofReal
    hr (2 * Real.pi * x)

theorem gammaHeightDensity_eq_scaledFourier {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (gammaHeightDensity r t : ℂ) =
      ((Real.pi⁻¹ : ℝ) : ℂ) * 𝓕 (gammaCoshPower r) (t / Real.pi) := by
  rw [fourier_gammaCoshPower_apply hr]
  unfold gammaHeightDensity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

theorem integrable_gammaHeightDensity {r : ℝ} (hr : 0 < r) :
    Integrable (gammaHeightDensity r) := by
  have hscale : (Real.pi : ℝ)⁻¹ ≠ 0 := inv_ne_zero Real.pi_ne_zero
  have hcomp := (integrable_fourier_gammaCoshPower hr).comp_mul_left' hscale
  have hreal := hcomp.re.const_mul Real.pi⁻¹
  apply hreal.congr
  filter_upwards with t
  have h := congrArg Complex.re (gammaHeightDensity_eq_scaledFourier hr t)
  simpa [div_eq_mul_inv, mul_comm] using h.symm

/-- Exact characteristic function of the literal normalized Gamma density. -/
theorem integral_cexp_mul_gammaHeightDensity {r : ℝ} (hr : 0 < r) (u : ℝ) :
    (∫ t : ℝ, Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
        (gammaHeightDensity r t : ℂ)) =
      ((Real.cosh (u / 2) ^ (-r) : ℝ) : ℂ) := by
  have hinv := congrFun (fourierInv_fourier_gammaCoshPower hr) (u / 2)
  rw [Real.fourierInv_eq] at hinv
  let G : ℝ → ℂ := fun t =>
    Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * (gammaHeightDensity r t : ℂ)
  have hscaled : ∀ x : ℝ,
      G (Real.pi * x) =
        ((Real.pi⁻¹ : ℝ) : ℂ) *
          (𝐞 (inner ℝ x (u / 2)) • 𝓕 (gammaCoshPower r) x) := by
    intro x
    dsimp only [G]
    rw [gammaHeightDensity_eq_scaledFourier hr]
    have harg : Real.pi * x / Real.pi = x := by field_simp [Real.pi_ne_zero]
    rw [harg, Real.inner_apply, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    have hexp : ((2 * Real.pi * (x * (u / 2)) : ℝ) : ℂ) * Complex.I =
        (((Real.pi * x * u : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hexp]
    ring
  have hscale := MeasureTheory.Measure.integral_comp_mul_left G Real.pi
  have hpiAbs : |(Real.pi : ℝ)⁻¹| = Real.pi⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr Real.pi_pos)]
  rw [hpiAbs, real_smul, show (fun x => G (Real.pi * x)) = fun x =>
      ((Real.pi⁻¹ : ℝ) : ℂ) *
        (𝐞 (inner ℝ x (u / 2)) • 𝓕 (gammaCoshPower r) x) from funext hscaled,
    MeasureTheory.integral_const_mul, hinv, gammaCoshPower] at hscale
  have hpiC : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  change (∫ t : ℝ, G t) = _
  apply (mul_left_cancel₀ hpiC)
  push_cast at hscale ⊢
  field_simp [hpiC] at hscale ⊢
  exact hscale.symm

theorem integral_gammaHeightDensity_eq_one {r : ℝ} (hr : 0 < r) :
    (∫ t : ℝ, gammaHeightDensity r t) = 1 := by
  have h := congrArg Complex.re (integral_cexp_mul_gammaHeightDensity hr 0)
  simpa [integral_complex_ofReal] using h

/-! ## Literal finite Euler tilts -/

def gammaEulerScale (r h : ℝ) : ℝ :=
  Real.exp (-r * h / 2)

/-- The normalized squared Euler factor in its real cosine form. -/
def gammaEulerNormalizedFactor (r h t : ℝ) : ℝ :=
  let a := gammaEulerScale r h
  (1 + a ^ 2 - 2 * a * Real.cos (h * t)) / (1 + a ^ 2)

theorem gammaEulerScale_pos (r h : ℝ) : 0 < gammaEulerScale r h :=
  Real.exp_pos _

theorem one_add_gammaEulerScale_sq (r h : ℝ) :
    1 + gammaEulerScale r h ^ 2 =
      2 * gammaEulerScale r h * Real.cosh (r * h / 2) := by
  let x := r * h / 2
  have hx : Real.exp (-r * h / 2) = Real.exp (-x) := by
    congr 1
    dsimp only [x]
    ring
  unfold gammaEulerScale
  rw [hx, show Real.cosh (r * h / 2) = Real.cosh x by rfl, Real.cosh_eq]
  have h1 : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    simp
  have h2 : Real.exp (-x) * Real.exp (-x) = Real.exp (-x) ^ 2 := by ring
  calc
    1 + Real.exp (-x) ^ 2 =
        Real.exp (-x) * Real.exp x + Real.exp (-x) * Real.exp (-x) := by rw [h1, h2]
    _ = 2 * Real.exp (-x) * ((Real.exp x + Real.exp (-x)) / 2) := by ring

/-- The cosine formula is literally the normalized squared factor
`|1-a exp(-iht)|²/(1+a²)`. -/
theorem gammaEulerNormalizedFactor_eq_normSq (r h t : ℝ) :
    gammaEulerNormalizedFactor r h t =
      Complex.normSq
          (1 - (gammaEulerScale r h : ℂ) *
            Complex.exp (-(((h * t : ℝ) : ℂ) * Complex.I))) /
        (1 + gammaEulerScale r h ^ 2) := by
  let a := gammaEulerScale r h
  have hexp : Complex.exp (-(((h * t : ℝ) : ℂ) * Complex.I)) =
      ((Real.cos (h * t) : ℝ) : ℂ) - ((Real.sin (h * t) : ℝ) : ℂ) * Complex.I := by
    rw [show -(((h * t : ℝ) : ℂ) * Complex.I) =
        (((-(h * t) : ℝ) : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hexp]
  let z : ℂ := 1 - (a : ℂ) *
    (((Real.cos (h * t) : ℝ) : ℂ) - ((Real.sin (h * t) : ℝ) : ℂ) * Complex.I)
  change (1 + a ^ 2 - 2 * a * Real.cos (h * t)) / (1 + a ^ 2) =
    Complex.normSq z / (1 + a ^ 2)
  have hzre : z.re = 1 - a * Real.cos (h * t) := by
    dsimp only [z]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul,
      mul_one]
  have hzim : z.im = a * Real.sin (h * t) := by
    dsimp only [z]
    simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul,
      mul_one, add_zero]
    ring
  have htrig := Real.sin_sq_add_cos_sq (h * t)
  rw [Complex.normSq_apply, hzre, hzim]
  field_simp
  nlinarith

theorem gammaEulerNormalizedFactor_nonneg (r h t : ℝ) :
    0 ≤ gammaEulerNormalizedFactor r h t := by
  rw [gammaEulerNormalizedFactor_eq_normSq]
  exact div_nonneg (Complex.normSq_nonneg _) (by positivity)

theorem gammaEulerNormalizedFactor_le_two (r h t : ℝ) :
    gammaEulerNormalizedFactor r h t ≤ 2 := by
  let a := gammaEulerScale r h
  have ha : 0 < a := gammaEulerScale_pos r h
  have hcos : -1 ≤ Real.cos (h * t) := neg_one_le_cos _
  have hsquare : 0 ≤ (a - 1) ^ 2 := sq_nonneg _
  unfold gammaEulerNormalizedFactor
  dsimp only [a]
  rw [div_le_iff₀ (by positivity : 0 < 1 + a ^ 2)]
  nlinarith

def gammaEulerFiniteWeight (r : ℝ) (L : List ℝ) (t : ℝ) : ℝ :=
  (L.map fun h => gammaEulerNormalizedFactor r h t).prod

@[simp] theorem gammaEulerFiniteWeight_nil (r t : ℝ) :
    gammaEulerFiniteWeight r [] t = 1 := rfl

@[simp] theorem gammaEulerFiniteWeight_cons (r h : ℝ) (L : List ℝ) (t : ℝ) :
    gammaEulerFiniteWeight r (h :: L) t =
      gammaEulerNormalizedFactor r h t * gammaEulerFiniteWeight r L t := by
  simp [gammaEulerFiniteWeight]

theorem gammaEulerFiniteWeight_nonneg (r : ℝ) (L : List ℝ) (t : ℝ) :
    0 ≤ gammaEulerFiniteWeight r L t := by
  exact List.prod_nonneg fun a ha => by
    obtain ⟨h, _hh, rfl⟩ := List.mem_map.mp ha
    exact gammaEulerNormalizedFactor_nonneg r h t

theorem continuous_gammaEulerFiniteWeight (r : ℝ) (L : List ℝ) :
    Continuous (gammaEulerFiniteWeight r L) := by
  induction L with
  | nil =>
      change Continuous (fun _ : ℝ => (1 : ℝ))
      exact continuous_const
  | cons h L ih =>
      rw [show gammaEulerFiniteWeight r (h :: L) = fun t =>
          gammaEulerNormalizedFactor r h t * gammaEulerFiniteWeight r L t by
        funext t; rw [gammaEulerFiniteWeight_cons]]
      apply Continuous.mul
      · unfold gammaEulerNormalizedFactor gammaEulerScale
        fun_prop
      · exact ih

theorem gammaEulerFiniteWeight_le (r : ℝ) (L : List ℝ) (t : ℝ) :
    gammaEulerFiniteWeight r L t ≤ 2 ^ L.length := by
  induction L with
  | nil => simp
  | cons h L ih =>
      rw [gammaEulerFiniteWeight_cons, List.length_cons]
      calc
        gammaEulerNormalizedFactor r h t * gammaEulerFiniteWeight r L t
            ≤ 2 * 2 ^ L.length :=
          mul_le_mul (gammaEulerNormalizedFactor_le_two r h t) ih
            (gammaEulerFiniteWeight_nonneg r L t) (by norm_num)
        _ = 2 ^ (L.length + 1) := by rw [pow_succ]; ring

def gammaEulerTiltedDensity (r : ℝ) (L : List ℝ) (t : ℝ) : ℝ :=
  gammaEulerFiniteWeight r L t * gammaHeightDensity r t

theorem gammaEulerTiltedDensity_nonneg {r : ℝ} (hr : 0 < r) (L : List ℝ) (t : ℝ) :
    0 ≤ gammaEulerTiltedDensity r L t :=
  mul_nonneg (gammaEulerFiniteWeight_nonneg r L t) (gammaHeightDensity_nonneg hr t)

theorem integrable_gammaEulerTiltedDensity {r : ℝ} (hr : 0 < r) (L : List ℝ) :
    Integrable (gammaEulerTiltedDensity r L) := by
  refine Integrable.mono' (g := fun t => 2 ^ L.length * gammaHeightDensity r t)
    ((integrable_gammaHeightDensity hr).const_mul _) ?_ ?_
  · exact (continuous_gammaEulerFiniteWeight r L).aestronglyMeasurable.mul
      (integrable_gammaHeightDensity hr).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (gammaEulerTiltedDensity_nonneg hr L t)]
    exact mul_le_mul_of_nonneg_right (gammaEulerFiniteWeight_le r L t)
      (gammaHeightDensity_nonneg hr t)

def gammaEulerTiltedCharacteristic (r : ℝ) (L : List ℝ) (u : ℝ) : ℂ :=
  ∫ t : ℝ, Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
    (gammaEulerTiltedDensity r L t : ℂ)

theorem integrable_cexp_mul_gammaEulerTiltedDensity {r : ℝ} (hr : 0 < r)
    (L : List ℝ) (u : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
      (gammaEulerTiltedDensity r L t : ℂ)) := by
  refine (integrable_gammaEulerTiltedDensity hr L).ofReal.bdd_mul (c := 1)
    (by fun_prop) (Filter.Eventually.of_forall fun t => ?_)
  rw [Complex.norm_exp_ofReal_mul_I]

theorem gammaEulerTiltedCharacteristic_nil {r : ℝ} (hr : 0 < r) (u : ℝ) :
    gammaEulerTiltedCharacteristic r [] u =
      ((Real.cosh (u / 2) ^ (-r) : ℝ) : ℂ) := by
  simpa [gammaEulerTiltedCharacteristic, gammaEulerTiltedDensity] using
    integral_cexp_mul_gammaHeightDensity hr u

theorem two_cos_mul_cexp (u h t : ℝ) :
    ((2 * Real.cos (h * t) : ℝ) : ℂ) *
        Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((t * (u + h) : ℝ) : ℂ) * Complex.I) +
        Complex.exp (((t * (u - h) : ℝ) : ℂ) * Complex.I) := by
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.exp_ofReal_mul_I_re, Complex.add_re]
    rw [show t * (u + h) = t * u + h * t by ring,
      show t * (u - h) = t * u - h * t by ring,
      Real.cos_add, Real.cos_sub]
    ring
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, Complex.exp_ofReal_mul_I_im, Complex.add_im]
    rw [show t * (u + h) = t * u + h * t by ring,
      show t * (u - h) = t * u - h * t by ring,
      Real.sin_add, Real.sin_sub]
    ring

theorem cexp_mul_gammaEulerNormalizedFactor (r h u t : ℝ) :
    Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
        (gammaEulerNormalizedFactor r h t : ℂ) =
      ((gammaEulerScale r h / (1 + gammaEulerScale r h ^ 2) : ℝ) : ℂ) *
        (2 * Real.cosh (r * h / 2) *
            Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((t * (u + h) : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((t * (u - h) : ℝ) : ℂ) * Complex.I)) := by
  let a := gammaEulerScale r h
  let d := 1 + a ^ 2
  have htwo := two_cos_mul_cexp u h t
  have hdenR : d = 2 * a * Real.cosh (r * h / 2) :=
    one_add_gammaEulerScale_sq r h
  have hdpos : 0 < d := by dsimp only [d]; positivity
  have hnum :
      (((1 + a ^ 2 - 2 * a * Real.cos (h * t) : ℝ)) : ℂ) =
        (d : ℂ) - (a : ℂ) * ((2 * Real.cos (h * t) : ℝ) : ℂ) := by
    dsimp only [d]
    push_cast
    ring
  have hdenC : (d : ℂ) = ((2 * a * Real.cosh (r * h / 2) : ℝ) : ℂ) :=
    congrArg Complex.ofReal hdenR
  have htwoMul :
      Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
          ((a : ℂ) * ((2 * Real.cos (h * t) : ℝ) : ℂ)) =
        (a : ℂ) *
          (Complex.exp (((t * (u + h) : ℝ) : ℂ) * Complex.I) +
            Complex.exp (((t * (u - h) : ℝ) : ℂ) * Complex.I)) := by
    calc
      Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
          ((a : ℂ) * ((2 * Real.cos (h * t) : ℝ) : ℂ)) =
        (a : ℂ) * (((2 * Real.cos (h * t) : ℝ) : ℂ) *
          Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)) := by ring
      _ = _ := by rw [htwo]
  have hmain :
      Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
          ((d : ℂ) - (a : ℂ) * ((2 * Real.cos (h * t) : ℝ) : ℂ)) =
        (a : ℂ) *
          (((2 * Real.cosh (r * h / 2) : ℝ) : ℂ) *
              Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((t * (u + h) : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((t * (u - h) : ℝ) : ℂ) * Complex.I)) := by
    calc
      Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
          ((d : ℂ) - (a : ℂ) * ((2 * Real.cos (h * t) : ℝ) : ℂ)) =
        Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * (d : ℂ) -
          Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
            ((a : ℂ) * ((2 * Real.cos (h * t) : ℝ) : ℂ)) := by ring
      _ = Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
            ((2 * a * Real.cosh (r * h / 2) : ℝ) : ℂ) -
          (a : ℂ) *
            (Complex.exp (((t * (u + h) : ℝ) : ℂ) * Complex.I) +
              Complex.exp (((t * (u - h) : ℝ) : ℂ) * Complex.I)) := by
        rw [hdenC, htwoMul]
      _ = _ := by
        push_cast only [Complex.ofReal_mul, Complex.ofReal_ofNat]
        ring
  unfold gammaEulerNormalizedFactor
  dsimp only
  dsimp only [a, d] at hnum hdpos hmain
  simp only [Complex.ofReal_div]
  rw [hnum]
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using congrArg
    (fun z : ℂ => z / ((1 + gammaEulerScale r h ^ 2 : ℝ) : ℂ)) hmain

theorem gammaEulerTiltedCharacteristic_cons {r : ℝ} (hr : 0 < r)
    (h : ℝ) (L : List ℝ) (u : ℝ) :
    gammaEulerTiltedCharacteristic r (h :: L) u =
      ((gammaEulerScale r h / (1 + gammaEulerScale r h ^ 2) : ℝ) : ℂ) *
        (2 * Real.cosh (r * h / 2) * gammaEulerTiltedCharacteristic r L u -
          gammaEulerTiltedCharacteristic r L (u + h) -
          gammaEulerTiltedCharacteristic r L (u - h)) := by
  let f : ℝ → ℂ := fun t =>
    Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
      (gammaEulerTiltedDensity r (h :: L) t : ℂ)
  let g0 : ℝ → ℂ := fun t =>
    2 * Real.cosh (r * h / 2) *
      (Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
        (gammaEulerTiltedDensity r L t : ℂ))
  let gp : ℝ → ℂ := fun t =>
    Complex.exp (((t * (u + h) : ℝ) : ℂ) * Complex.I) *
      (gammaEulerTiltedDensity r L t : ℂ)
  let gm : ℝ → ℂ := fun t =>
    Complex.exp (((t * (u - h) : ℝ) : ℂ) * Complex.I) *
      (gammaEulerTiltedDensity r L t : ℂ)
  have hf : f = fun t =>
      ((gammaEulerScale r h / (1 + gammaEulerScale r h ^ 2) : ℝ) : ℂ) *
        (g0 t - gp t - gm t) := by
    funext t
    dsimp only [f, g0, gp, gm, gammaEulerTiltedDensity]
    rw [gammaEulerFiniteWeight_cons]
    push_cast only [Complex.ofReal_mul]
    have hfactor := cexp_mul_gammaEulerNormalizedFactor r h u t
    push_cast only [Complex.ofReal_mul] at hfactor
    nth_rewrite 1 [show
      (gammaEulerNormalizedFactor r h t : ℂ) *
          (gammaEulerFiniteWeight r L t : ℂ) * (gammaHeightDensity r t : ℂ) =
        (gammaEulerNormalizedFactor r h t : ℂ) *
          ((gammaEulerFiniteWeight r L t : ℂ) * (gammaHeightDensity r t : ℂ)) by ring]
    rw [← mul_assoc, hfactor]
    ring
  have hg0 : Integrable g0 := by
    dsimp only [g0]
    exact (integrable_cexp_mul_gammaEulerTiltedDensity hr L u).const_mul _
  have hgp : Integrable gp := integrable_cexp_mul_gammaEulerTiltedDensity hr L (u + h)
  have hgm : Integrable gm := integrable_cexp_mul_gammaEulerTiltedDensity hr L (u - h)
  have hsub : (∫ t : ℝ, g0 t - gp t - gm t) =
      (∫ t : ℝ, g0 t) - (∫ t : ℝ, gp t) - (∫ t : ℝ, gm t) := by
    calc
      (∫ t : ℝ, g0 t - gp t - gm t) =
          ∫ t : ℝ, (g0 - gp) t - gm t := by rfl
      _ = (∫ t : ℝ, (g0 - gp) t) - ∫ t : ℝ, gm t :=
        MeasureTheory.integral_sub (hg0.sub hgp) hgm
      _ = (∫ t : ℝ, g0 t) - (∫ t : ℝ, gp t) - (∫ t : ℝ, gm t) := by
        exact congrArg (fun z => z - ∫ t : ℝ, gm t)
          (MeasureTheory.integral_sub hg0 hgp)
  have hg0eq : (∫ t : ℝ, g0 t) =
      2 * Real.cosh (r * h / 2) * gammaEulerTiltedCharacteristic r L u := by
    dsimp only [g0, gammaEulerTiltedCharacteristic]
    rw [MeasureTheory.integral_const_mul]
  have hgpeq : (∫ t : ℝ, gp t) = gammaEulerTiltedCharacteristic r L (u + h) := rfl
  have hgmeq : (∫ t : ℝ, gm t) = gammaEulerTiltedCharacteristic r L (u - h) := rfl
  rw [gammaEulerTiltedCharacteristic, show (fun t =>
      Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
        (gammaEulerTiltedDensity r (h :: L) t : ℂ)) = f from rfl,
    hf, MeasureTheory.integral_const_mul,
    hsub, hg0eq, hgpeq, hgmeq]

def gammaEulerFiniteCoefficient (r : ℝ) (L : List ℝ) : ℝ :=
  (L.map fun h => gammaEulerScale r h / (1 + gammaEulerScale r h ^ 2)).prod

theorem gammaEulerFiniteCoefficient_pos (r : ℝ) (L : List ℝ) :
    0 < gammaEulerFiniteCoefficient r L := by
  apply List.prod_pos
  intro a ha
  obtain ⟨h, _hh, rfl⟩ := List.mem_map.mp ha
  exact div_pos (gammaEulerScale_pos r h) (by positivity)

/-- Every finite literal Euler tilt has exactly the abstract iterated-difference characteristic. -/
theorem gammaEulerTiltedCharacteristic_eq_differenceList {r : ℝ} (hr : 0 < r)
    (L : List ℝ) (u : ℝ) :
    gammaEulerTiltedCharacteristic r L u =
      ((gammaEulerFiniteCoefficient r L *
        gammaEulerDifferenceList r L
          (fun v => Real.cosh (v / 2) ^ (-r)) u : ℝ) : ℂ) := by
  induction L generalizing u with
  | nil =>
      simpa [gammaEulerFiniteCoefficient, gammaEulerDifferenceList] using
        gammaEulerTiltedCharacteristic_nil hr u
  | cons h L ih =>
      rw [gammaEulerTiltedCharacteristic_cons hr h L u,
        ih u, ih (u + h), ih (u - h)]
      simp only [gammaEulerFiniteCoefficient, List.map_cons, List.prod_cons,
        gammaEulerDifferenceList, List.foldr_cons]
      rw [gammaEulerCentralDifference]
      push_cast
      ring

/-! ## Literal energy change and primewise contraction reversal -/

/-- Total mass of the Gamma density after the finite normalized Euler tilt. -/
def gammaEulerTiltedEnergy (r : ℝ) (L : List ℝ) : ℝ :=
  ∫ t : ℝ, gammaEulerTiltedDensity r L t

/-- Real correlation of the finite tilted Gamma density. -/
def gammaEulerTiltedCorrelation (r : ℝ) (L : List ℝ) (u : ℝ) : ℝ :=
  (gammaEulerTiltedCharacteristic r L u).re

theorem gammaEulerTiltedCorrelation_eq_integral_cos {r : ℝ} (hr : 0 < r)
    (L : List ℝ) (u : ℝ) :
    gammaEulerTiltedCorrelation r L u =
      ∫ t : ℝ, Real.cos (t * u) * gammaEulerTiltedDensity r L t := by
  unfold gammaEulerTiltedCorrelation gammaEulerTiltedCharacteristic
  calc
    (∫ t : ℝ, Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
        (gammaEulerTiltedDensity r L t : ℂ)).re =
        ∫ t : ℝ, (Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
          (gammaEulerTiltedDensity r L t : ℂ)).re :=
      (integral_re (integrable_cexp_mul_gammaEulerTiltedDensity hr L u)).symm
    _ = ∫ t : ℝ, Real.cos (t * u) * gammaEulerTiltedDensity r L t := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.ofReal_re,
        Complex.exp_ofReal_mul_I_im, Complex.ofReal_im, mul_zero, sub_zero]

theorem gammaEulerNormalizedFactor_eq_one_sub (r h t : ℝ) :
    gammaEulerNormalizedFactor r h t =
      1 - 2 * gammaEulerScale r h / (1 + gammaEulerScale r h ^ 2) *
        Real.cos (h * t) := by
  unfold gammaEulerNormalizedFactor
  field_simp

/-- Exact mass change under insertion of one normalized squared Euler factor. -/
theorem gammaEulerTiltedEnergy_cons {r : ℝ} (hr : 0 < r)
    (h : ℝ) (L : List ℝ) :
    gammaEulerTiltedEnergy r (h :: L) - gammaEulerTiltedEnergy r L =
      -(2 * gammaEulerScale r h / (1 + gammaEulerScale r h ^ 2)) *
        gammaEulerTiltedCorrelation r L h := by
  let c := 2 * gammaEulerScale r h / (1 + gammaEulerScale r h ^ 2)
  have hden := integrable_gammaEulerTiltedDensity hr L
  have hcos : Integrable
      (fun t : ℝ => Real.cos (h * t) * gammaEulerTiltedDensity r L t) := by
    refine hden.bdd_mul (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun t => ?_)
    simpa [Real.norm_eq_abs] using abs_cos_le_one (h * t)
  have hpoint : gammaEulerTiltedDensity r (h :: L) =
      fun t => gammaEulerTiltedDensity r L t -
        c * (Real.cos (h * t) * gammaEulerTiltedDensity r L t) := by
    funext t
    rw [gammaEulerTiltedDensity, gammaEulerFiniteWeight_cons,
      gammaEulerNormalizedFactor_eq_one_sub]
    dsimp only [c]
    dsimp only [gammaEulerTiltedDensity]
    ring
  unfold gammaEulerTiltedEnergy
  rw [hpoint,
    MeasureTheory.integral_sub hden (hcos.const_mul c),
    MeasureTheory.integral_const_mul,
    gammaEulerTiltedCorrelation_eq_integral_cos hr]
  rw [show (fun t : ℝ => Real.cos (t * h) * gammaEulerTiltedDensity r L t) =
      (fun t : ℝ => Real.cos (h * t) * gammaEulerTiltedDensity r L t) by
    funext t
    rw [mul_comm t h]]
  dsimp only [c]
  ring

/-- One literal normalized Euler channel preserves strict positivity of every correlation. -/
theorem gammaEulerTiltedCorrelation_singleton_pos {r h : ℝ}
    (hr : 0 < r) (hh : 0 < h) (u : ℝ) :
    0 < gammaEulerTiltedCorrelation r [h] u := by
  rw [gammaEulerTiltedCorrelation,
    gammaEulerTiltedCharacteristic_eq_differenceList hr]
  simp only [Complex.ofReal_re]
  apply mul_pos (gammaEulerFiniteCoefficient_pos r [h])
  simpa [gammaEulerDifferenceList] using
    gammaEulerCentralDifference_cosh_rpow_pos hr hh u

/-- Every positive, nonempty, even finite Euler block has a negative correlation tail. -/
theorem gammaEulerTiltedCorrelation_eventually_neg {r : ℝ} (hr : 0 < r)
    {L : List ℝ} (hpos : ∀ h ∈ L, 0 < h) (hL : L ≠ [])
    (hlen : Even L.length) :
    ∀ᶠ u : ℝ in atTop, gammaEulerTiltedCorrelation r L u < 0 := by
  filter_upwards [gammaEulerDifferenceList_eventually_neg hr hpos hL hlen] with u hu
  rw [gammaEulerTiltedCorrelation,
    gammaEulerTiltedCharacteristic_eq_differenceList hr]
  simp only [Complex.ofReal_re]
  exact mul_neg_of_pos_of_neg (gammaEulerFiniteCoefficient_pos r L) hu

/-- After any positive nonempty even block, some larger prime scale makes the next normalized
Euler insertion strictly increase the literal Gamma energy. -/
theorem exists_prime_gammaEulerTiltedEnergy_increase_after_even_block
    {r : ℝ} (hr : 0 < r) {L : List ℝ}
    (hpos : ∀ h ∈ L, 0 < h) (hL : L ≠ []) (hlen : Even L.length) :
    ∃ p : ℕ, Nat.Prime p ∧ 0 < Real.log (p : ℝ) ∧
      gammaEulerTiltedEnergy r L <
        gammaEulerTiltedEnergy r (Real.log (p : ℝ) :: L) := by
  obtain ⟨U, hU⟩ := eventually_atTop.mp
    (gammaEulerTiltedCorrelation_eventually_neg hr hpos hL hlen)
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (Real.exp U)
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes N
  have hexp : Real.exp U < (p : ℝ) := hN.trans_le (by exact_mod_cast hNp)
  have hpR : 0 < (p : ℝ) := (Real.exp_pos U).trans hexp
  have hlog : U < Real.log (p : ℝ) := by
    rw [← Real.log_exp U]
    exact Real.strictMonoOn_log (Real.exp_pos U) hpR hexp
  have hcorr : gammaEulerTiltedCorrelation r L (Real.log (p : ℝ)) < 0 :=
    hU _ hlog.le
  have hcoef :
      0 < 2 * gammaEulerScale r (Real.log (p : ℝ)) /
        (1 + gammaEulerScale r (Real.log (p : ℝ)) ^ 2) :=
    div_pos (mul_pos (by norm_num) (gammaEulerScale_pos _ _)) (by positivity)
  have hchange := gammaEulerTiltedEnergy_cons hr (Real.log (p : ℝ)) L
  refine ⟨p, hp, Real.log_pos (by exact_mod_cast hp.one_lt), ?_⟩
  rw [← sub_pos]
  rw [hchange]
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos hcoef) hcorr

/-- Headline no-go: after two fixed positive Euler channels, a third prime channel reverses
prime-by-prime contraction. -/
theorem exists_prime_gammaEulerTiltedEnergy_increase_after_two_channels
    {r h₁ h₂ : ℝ} (hr : 0 < r) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) :
    ∃ p : ℕ, Nat.Prime p ∧ 0 < Real.log (p : ℝ) ∧
      gammaEulerTiltedEnergy r [h₁, h₂] <
        gammaEulerTiltedEnergy r [Real.log (p : ℝ), h₁, h₂] := by
  simpa using exists_prime_gammaEulerTiltedEnergy_increase_after_even_block hr
    (L := [h₁, h₂]) (by simpa using ⟨hh₁, hh₂⟩) (by simp) (by norm_num)

end

end RHTower
