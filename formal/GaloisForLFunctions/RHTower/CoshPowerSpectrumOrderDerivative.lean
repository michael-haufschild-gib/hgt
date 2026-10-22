import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspWignerPairSpectrum

/-!
# The order derivative of the hyperbolic-secant power transform

The cosine transform of `(cosh y)^(-b)` is `2^(b-1) |Γ((b+iξ)/2)|² / Γ(b)`.  Differentiating in the
order `b` under the integral sign, which is legitimate because `log (cosh y) (cosh y)^(-b)` is
dominated by `(4/a) (cosh y)^(-a/4)` uniformly near `b = a`, identifies the log-weighted transform:

```text
∫_ℝ log (cosh y) (cosh y)^(-a) cos (ξ y) dy = - d/da [ 2^(a-1) |Γ((a+iξ)/2)|² / Γ(a) ] .
```

This is the remaining archimedean ingredient of the centre-weighted theta Wigner pair current.
-/

open Real MeasureTheory Set

namespace RHTower

noncomputable section

/-- The real cosine transform of a hyperbolic-secant power. -/
def coshPowerSpectrum (b ξ : ℝ) : ℝ :=
  (2 : ℝ) ^ (b - 1) *
    Complex.normSq (Complex.Gamma (((b : ℂ) + (ξ : ℂ) * Complex.I) / 2)) / Real.Gamma b

theorem integrable_cosh_rpow_neg_mul_cos {b : ℝ} (hb : 0 < b) (ξ : ℝ) :
    Integrable (fun y : ℝ => (Real.cosh y) ^ (-b) * Real.cos (ξ * y)) := by
  have hcont : Continuous fun y : ℝ => (Real.cosh y) ^ (-b) :=
    Real.continuous_cosh.rpow_const fun y => Or.inl (Real.cosh_pos y).ne'
  refine Integrable.mono' (HTGeometry.integrable_cosh_rpow_neg hb) ?_ ?_
  · exact (hcont.mul (Real.continuous_cos.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos (Real.cosh_pos y) _)]
    have : |Real.cos (ξ * y)| ≤ 1 := Real.abs_cos_le_one _
    nlinarith [Real.rpow_pos_of_pos (Real.cosh_pos y) (-b), abs_nonneg (Real.cos (ξ * y))]

theorem integral_cosh_rpow_neg_mul_cos {b : ℝ} (hb : 0 < b) (ξ : ℝ) :
    (∫ y : ℝ, (Real.cosh y) ^ (-b) * Real.cos (ξ * y)) = coshPowerSpectrum b ξ := by
  have hint := integrable_cosh_rpow_neg_mul_fourier hb ξ
  have key : (∫ y : ℝ, (Real.cosh y) ^ (-b) * Real.cos (ξ * y)) =
      (∫ y : ℝ, (((Real.cosh y) ^ (-b) : ℝ) : ℂ) *
        Complex.exp (-((ξ : ℂ) * (y : ℂ)) * Complex.I)).re := by
    rw [← RCLike.re_to_complex, ← integral_re hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hphase : Complex.exp (-((ξ : ℂ) * (y : ℂ)) * Complex.I) =
        Complex.exp (((-(ξ * y) : ℝ) : ℂ) * Complex.I) := by
      congr 1; push_cast; ring
    show (Real.cosh y) ^ (-b) * Real.cos (ξ * y) =
      RCLike.re ((((Real.cosh y) ^ (-b) : ℝ) : ℂ) *
        Complex.exp (-((ξ : ℂ) * (y : ℂ)) * Complex.I))
    rw [RCLike.re_to_complex, hphase, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg]
    ring
  rw [key, HTGeometry.integral_cosh_rpow_neg_mul_exp_eq_ofReal hb ξ, Complex.ofReal_re,
    coshPowerSpectrum]

theorem hasDerivAt_cosh_rpow_neg (y b : ℝ) :
    HasDerivAt (fun c : ℝ => (Real.cosh y) ^ (-c))
      (-(Real.log (Real.cosh y) * (Real.cosh y) ^ (-b))) b := by
  have hc : (0 : ℝ) < Real.cosh y := Real.cosh_pos y
  have hfun : (fun c : ℝ => (Real.cosh y) ^ (-c))
      = fun c : ℝ => Real.exp (Real.log (Real.cosh y) * (-c)) := by
    funext c; rw [Real.rpow_def_of_pos hc]
  rw [hfun]
  have hinner : HasDerivAt (fun c : ℝ => Real.log (Real.cosh y) * (-c))
      (-Real.log (Real.cosh y)) b := by
    simpa using ((hasDerivAt_neg b).const_mul (Real.log (Real.cosh y)))
  have h := (Real.hasDerivAt_exp (Real.log (Real.cosh y) * (-b))).comp b hinner
  refine h.congr_deriv ?_
  rw [← Real.rpow_def_of_pos hc]
  ring

theorem log_cosh_mul_cosh_rpow_le {δ : ℝ} (hδ : 0 < δ) {b c : ℝ} (hbc : c + δ ≤ b) (y : ℝ) :
    Real.log (Real.cosh y) * (Real.cosh y) ^ (-b) ≤ (1 / δ) * (Real.cosh y) ^ (-c) := by
  have h1 : (1 : ℝ) ≤ Real.cosh y := Real.one_le_cosh y
  have hpos : (0 : ℝ) < Real.cosh y := by linarith
  have hlogn : (0 : ℝ) ≤ Real.log (Real.cosh y) := Real.log_nonneg h1
  have hlog : Real.log (Real.cosh y) ≤ (Real.cosh y) ^ δ / δ :=
    Real.log_le_rpow_div hpos.le hδ
  have hmono : (Real.cosh y) ^ (-b) ≤ (Real.cosh y) ^ (-(c + δ)) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have hsplit : (Real.cosh y) ^ δ * (Real.cosh y) ^ (-(c + δ)) = (Real.cosh y) ^ (-c) := by
    rw [← Real.rpow_add hpos]; congr 1; ring
  have hcd : (0 : ℝ) < (Real.cosh y) ^ (-(c + δ)) := Real.rpow_pos_of_pos hpos _
  calc Real.log (Real.cosh y) * (Real.cosh y) ^ (-b)
      ≤ Real.log (Real.cosh y) * (Real.cosh y) ^ (-(c + δ)) := by
        exact mul_le_mul_of_nonneg_left hmono hlogn
    _ ≤ ((Real.cosh y) ^ δ / δ) * (Real.cosh y) ^ (-(c + δ)) := by
        exact mul_le_mul_of_nonneg_right hlog hcd.le
    _ = (1 / δ) * (Real.cosh y) ^ (-c) := by
        rw [← hsplit]; field_simp

theorem integrable_log_cosh_mul_cosh_rpow_neg_mul_cos {b : ℝ} (hb : 0 < b) (ξ : ℝ) :
    Integrable (fun y : ℝ =>
      -(Real.log (Real.cosh y) * (Real.cosh y) ^ (-b)) * Real.cos (ξ * y)) := by
  have hcont : Continuous fun y : ℝ =>
      -(Real.log (Real.cosh y) * (Real.cosh y) ^ (-b)) * Real.cos (ξ * y) := by
    have h1 : Continuous fun y : ℝ => Real.log (Real.cosh y) :=
      Real.continuousOn_log.comp_continuous Real.continuous_cosh fun y => (Real.cosh_pos y).ne'
    have h2 : Continuous fun y : ℝ => (Real.cosh y) ^ (-b) :=
      Real.continuous_cosh.rpow_const fun y => Or.inl (Real.cosh_pos y).ne'
    exact ((h1.mul h2).neg).mul (Real.continuous_cos.comp (by fun_prop))
  refine Integrable.mono' ((HTGeometry.integrable_cosh_rpow_neg
    (show (0 : ℝ) < b / 2 by linarith)).const_mul (1 / (b / 2))) hcont.aestronglyMeasurable ?_
  filter_upwards with y
  have hb2 : (0 : ℝ) < b / 2 := by linarith
  have hkey := log_cosh_mul_cosh_rpow_le (δ := b / 2) hb2 (b := b) (c := b / 2)
    (by linarith) y
  have hcos : |Real.cos (ξ * y)| ≤ 1 := Real.abs_cos_le_one _
  have hlogn : (0 : ℝ) ≤ Real.log (Real.cosh y) := Real.log_nonneg (Real.one_le_cosh y)
  have hrp : (0 : ℝ) < (Real.cosh y) ^ (-b) := Real.rpow_pos_of_pos (Real.cosh_pos y) _
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
  nlinarith [mul_nonneg hlogn hrp.le, abs_nonneg (Real.cos (ξ * y))]

/-- **The log-weighted secant-power cosine transform is minus the order derivative.** -/
theorem hasDerivAt_coshPowerSpectrum {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    HasDerivAt (fun b : ℝ => coshPowerSpectrum b ξ)
      (∫ y : ℝ, -(Real.log (Real.cosh y) * (Real.cosh y) ^ (-a)) * Real.cos (ξ * y)) a := by
  set S : Set ℝ := Set.Ioo (a / 2) (3 * a / 2) with hS
  have hSmem : S ∈ nhds a := by
    rw [hS]
    exact Ioo_mem_nhds (by linarith) (by linarith)
  have ha4 : (0 : ℝ) < a / 4 := by linarith
  have hbound : Integrable (fun y : ℝ => (1 / (a / 4)) * (Real.cosh y) ^ (-(a / 4))) :=
    (HTGeometry.integrable_cosh_rpow_neg ha4).const_mul _
  have hFmeas : ∀ᶠ b : ℝ in nhds a,
      AEStronglyMeasurable (fun y : ℝ => (Real.cosh y) ^ (-b) * Real.cos (ξ * y)) volume := by
    filter_upwards with b
    have h2 : Continuous fun y : ℝ => (Real.cosh y) ^ (-b) :=
      Real.continuous_cosh.rpow_const fun y => Or.inl (Real.cosh_pos y).ne'
    exact (h2.mul (Real.continuous_cos.comp (by fun_prop))).aestronglyMeasurable
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (𝕜 := ℝ) (E := ℝ)
    (F := fun b y : ℝ => (Real.cosh y) ^ (-b) * Real.cos (ξ * y))
    (F' := fun b y : ℝ => -(Real.log (Real.cosh y) * (Real.cosh y) ^ (-b)) * Real.cos (ξ * y))
    (x₀ := a) (bound := fun y : ℝ => (1 / (a / 4)) * (Real.cosh y) ^ (-(a / 4)))
    hSmem hFmeas (integrable_cosh_rpow_neg_mul_cos ha ξ)
    (integrable_log_cosh_mul_cosh_rpow_neg_mul_cos ha ξ).aestronglyMeasurable
    (by
      filter_upwards with y
      intro b hb
      have hb2 : a / 2 < b := hb.1
      have hkey := log_cosh_mul_cosh_rpow_le (δ := a / 4) ha4 (b := b) (c := a / 4)
        (by linarith) y
      have hcos : |Real.cos (ξ * y)| ≤ 1 := Real.abs_cos_le_one _
      have hlogn : (0 : ℝ) ≤ Real.log (Real.cosh y) := Real.log_nonneg (Real.one_le_cosh y)
      have hrp : (0 : ℝ) < (Real.cosh y) ^ (-b) := Real.rpow_pos_of_pos (Real.cosh_pos y) _
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
      nlinarith [mul_nonneg hlogn hrp.le, abs_nonneg (Real.cos (ξ * y))])
    hbound
    (by
      filter_upwards with y
      intro b _
      exact (hasDerivAt_cosh_rpow_neg y b).mul_const (Real.cos (ξ * y)))
  refine (hderiv.2).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ha] with b hb
  exact (integral_cosh_rpow_neg_mul_cos hb ξ).symm

/-- The log-weighted secant-power cosine transform in closed form. -/
theorem integral_log_cosh_mul_cosh_rpow_neg_mul_cos {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    (∫ y : ℝ, Real.log (Real.cosh y) * (Real.cosh y) ^ (-a) * Real.cos (ξ * y)) =
      -deriv (fun b : ℝ => coshPowerSpectrum b ξ) a := by
  rw [(hasDerivAt_coshPowerSpectrum ha ξ).deriv, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

end

end RHTower
