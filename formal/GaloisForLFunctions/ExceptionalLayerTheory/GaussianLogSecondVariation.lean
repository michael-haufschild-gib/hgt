import GaloisForLFunctions.ExceptionalLayerTheory.GaussianLogarithmicContinuum
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianSecondVariation

/-!
# Second-order logarithmic Gaussian lattice cancellation

Fractional logarithmic moment bounds keep the second derivative integrable
at zero and retain its Gaussian scale. Trapezoidal cancellation then gains
another power of the Gaussian length in logarithmic divisor fibres.
-/

open Complex MeasureTheory Set Filter Topology Finset

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem norm_gaussianMellinWeight {w ε : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖gaussianMellinWeight w ε x‖ = x ^ w.re * Real.exp (-ε.re * x ^ 2) := by
  rw [gaussianMellinWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_exp]
  congr 2
  simp [pow_two]

private theorem integrable_gaussian_power {q α : ℝ} (hq : -1 < q) (hα : 0 < α) :
    IntegrableOn (fun x : ℝ => x ^ q * Real.exp (-α * x ^ (2 : ℕ))) (Ioi 0) := by
  simpa only [Real.rpow_two] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow hq (by norm_num : (1 : ℝ) ≤ 2) hα)

private theorem integrable_gaussianMellinWeight {w ε : ℂ}
    (hw : -1 < w.re) (hε : 0 < ε.re) :
    IntegrableOn (gaussianMellinWeight w ε) (Ioi 0) := by
  have hc : ContinuousOn (gaussianMellinWeight w ε) (Ioi 0) := by
    intro x hx
    exact ((Complex.continuousAt_ofReal_cpow_const x w (Or.inr hx.ne')).mul
      (by fun_prop)).continuousWithinAt
  refine (integrable_gaussian_power hw hε).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (norm_gaussianMellinWeight hx).le

private theorem integral_norm_gaussianMellinWeight {w ε : ℂ}
    (hw : -1 < w.re) (hε : 0 < ε.re) :
    (∫ x in Ioi (0 : ℝ), ‖gaussianMellinWeight w ε x‖) =
      gaussianRealMoment w.re ε.re := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => norm_gaussianMellinWeight hx)]
  exact RHTower.integral_rpow_mul_exp_neg_mul_sq_Ioi hw hε

/-- Fractional powers control the logarithm without crossing its integrability
threshold at the origin. -/
theorem abs_log_div_le_fractional {x X b δ : ℝ}
    (hx : 0 < x) (hX : 0 < X) (hb : 0 < b) (hδ : 0 < δ) :
    |Real.log (x / b)| ≤
      ((x / X) ^ δ + (X / x) ^ δ) / δ + |Real.log (X / b)| := by
  have hy := div_pos hx hX
  have hp := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy δ)
  have hm := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos (div_pos hX hx) δ)
  rw [Real.log_rpow hy] at hp
  rw [Real.log_rpow (div_pos hX hx)] at hm
  have he : Real.log (X / x) = -Real.log (x / X) := by
    rw [Real.log_div hX.ne' hx.ne', Real.log_div hx.ne' hX.ne']
    ring
  rw [he] at hm
  have ha : |Real.log (x / X)| ≤ ((x / X) ^ δ + (X / x) ^ δ) / δ := by
    apply (le_div_iff₀ hδ).mpr
    have hh : |δ * Real.log (x / X)| ≤ (x / X) ^ δ + (X / x) ^ δ := by
      apply abs_le.mpr
      constructor <;> nlinarith only [hp, hm, Real.rpow_pos_of_pos hy δ,
        Real.rpow_pos_of_pos (div_pos hX hx) δ]
    simpa only [abs_mul, abs_of_pos hδ, mul_comm] using hh
  have heq : x / b = (x / X) * (X / b) := by field_simp
  rw [heq, Real.log_mul (div_ne_zero hx.ne' hX.ne') (div_ne_zero hX.ne' hb.ne')]
  exact (abs_add_le _ _).trans (_root_.add_le_add ha le_rfl)

/-- A logarithmic Gaussian moment bound valid down to exponent `q>−1`,
with an independently chosen positive margin `δ<q+1`. -/
def gaussianFractionalLogBudget (q α X b δ : ℝ) : ℝ :=
  (X ^ (-δ) * gaussianRealMoment (q + δ) α +
    X ^ δ * gaussianRealMoment (q - δ) α) / δ +
    |Real.log (X / b)| * gaussianRealMoment q α

private def fractionalLogMajorant (q α X b δ x : ℝ) : ℝ :=
  (X ^ (-δ) / δ) * (x ^ (q + δ) * Real.exp (-α * x ^ 2)) +
    (X ^ δ / δ) * (x ^ (q - δ) * Real.exp (-α * x ^ 2)) +
    |Real.log (X / b)| * (x ^ q * Real.exp (-α * x ^ 2))

private theorem log_gaussian_le_fractional {q α X b δ x : ℝ}
    (hx : 0 < x) (hX : 0 < X) (hb : 0 < b) (hδ : 0 < δ) :
    |Real.log (x / b)| * (x ^ q * Real.exp (-α * x ^ 2)) ≤
      fractionalLogMajorant q α X b δ x := by
  have h := mul_le_mul_of_nonneg_right (abs_log_div_le_fractional hx hX hb hδ)
    (show 0 ≤ x ^ q * Real.exp (-α * x ^ 2) by positivity)
  have hp : x ^ (q + δ) = x ^ q * x ^ δ := Real.rpow_add hx _ _
  have hm : x ^ (q - δ) = x ^ q / x ^ δ := by
    rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_neg hx.le, div_eq_mul_inv]
  calc
    _ ≤ (((x / X) ^ δ + (X / x) ^ δ) / δ + |Real.log (X / b)|) *
        (x ^ q * Real.exp (-α * x ^ 2)) := h
    _ = _ := by
      unfold fractionalLogMajorant
      rw [hp, hm, Real.div_rpow hx.le hX.le, Real.div_rpow hX.le hx.le,
        Real.rpow_neg hX.le]
      ring

private theorem integrable_fractionalLogMajorant {q α δ : ℝ}
    (hδ : 0 < δ) (hq : -1 < q - δ) (hα : 0 < α) (X b : ℝ) :
    IntegrableOn (fractionalLogMajorant q α X b δ) (Ioi 0) :=
  (((integrable_gaussian_power (by linarith : -1 < q + δ) hα).const_mul _).add
    ((integrable_gaussian_power hq hα).const_mul _)).add
    ((integrable_gaussian_power (by linarith : -1 < q) hα).const_mul _)

private theorem integral_fractionalLogMajorant {q α δ : ℝ}
    (hδ : 0 < δ) (hq : -1 < q - δ) (hα : 0 < α) (X b : ℝ) :
    (∫ x in Ioi (0 : ℝ), fractionalLogMajorant q α X b δ x) =
      gaussianFractionalLogBudget q α X b δ := by
  have hp := (integrable_gaussian_power (by linarith : -1 < q + δ) hα).const_mul (X ^ (-δ) / δ)
  have hm := (integrable_gaussian_power hq hα).const_mul (X ^ δ / δ)
  have h0 := (integrable_gaussian_power (by linarith : -1 < q) hα).const_mul |Real.log (X / b)|
  have hpm : IntegrableOn (fun x : ℝ =>
      (X ^ (-δ) / δ) * (x ^ (q + δ) * Real.exp (-α * x ^ 2)) +
        (X ^ δ / δ) * (x ^ (q - δ) * Real.exp (-α * x ^ 2))) (Ioi 0) := hp.add hm
  unfold fractionalLogMajorant
  rw [integral_add hpm h0, integral_add hp hm,
    integral_const_mul, integral_const_mul, integral_const_mul,
    RHTower.integral_rpow_mul_exp_neg_mul_sq_Ioi (by linarith) hα,
    RHTower.integral_rpow_mul_exp_neg_mul_sq_Ioi hq hα,
    RHTower.integral_rpow_mul_exp_neg_mul_sq_Ioi (by linarith) hα]
  unfold gaussianFractionalLogBudget gaussianRealMoment
  ring

private theorem continuousOn_gaussianLogMellinWeight (w ε : ℂ) {b : ℝ} (hb : 0 < b) :
    ContinuousOn (gaussianLogMellinWeight w ε b) (Ioi 0) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.mul
  · exact Complex.continuous_ofReal.continuousAt.comp
      ((continuousAt_id.div_const b).log (ne_of_gt (div_pos hx hb)))
  · exact (Complex.continuousAt_ofReal_cpow_const x w (Or.inr hx.ne')).mul (by fun_prop)

private theorem integrable_gaussianLogMellinWeight {w ε : ℂ}
    (hw : -1 < w.re) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (gaussianLogMellinWeight w ε b) (Ioi 0) := by
  let δ := (w.re + 1) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hq : -1 < w.re - δ := by dsimp [δ]; linarith
  refine (integrable_fractionalLogMajorant hδ hq hε 1 b).mono'
    ((continuousOn_gaussianLogMellinWeight w ε hb).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [gaussianLogMellinWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_gaussianMellinWeight hx]
  exact log_gaussian_le_fractional hx zero_lt_one hb hδ

/-- Fractional logarithmic control includes the singular second-derivative
moments with real exponents between `−1` and `0`. -/
theorem integral_norm_gaussianLogMellinWeight_le_fractional {w ε : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hw : -1 < w.re - δ) (hε : 0 < ε.re)
    {X b : ℝ} (hX : 0 < X) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), ‖gaussianLogMellinWeight w ε b x‖) ≤
      gaussianFractionalLogBudget w.re ε.re X b δ := by
  rw [← integral_fractionalLogMajorant hδ hw hε X b]
  refine integral_mono_ae (integrable_gaussianLogMellinWeight (by linarith) hε hb).norm
    (integrable_fractionalLogMajorant hδ hw hε X b) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [gaussianLogMellinWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_gaussianMellinWeight hx]
  exact log_gaussian_le_fractional hx hX hb hδ

private def gaussianFirstDeriv (w ε : ℂ) (x : ℝ) : ℂ :=
  w * gaussianMellinWeight (w - 1) ε x - 2 * ε * gaussianMellinWeight (w + 1) ε x

private theorem hasDerivAt_gaussianMellinWeight {w : ℂ} (hw : 0 < w.re)
    (ε : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (gaussianMellinWeight w ε) (gaussianFirstDeriv w ε x) x := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hpow := hasDerivAt_ofReal_cpow_const hx.ne' hw0
  have he := (((Complex.ofRealCLM.hasDerivAt (x := x)).pow 2).const_mul ε).neg.cexp
  apply (hpow.mul he).congr_deriv
  have hp : (x : ℂ) ^ (w + 1) = (x : ℂ) ^ w * (x : ℂ) := by
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_one]
  dsimp only [gaussianFirstDeriv, gaussianMellinWeight]
  rw [hp]
  simp only [Pi.neg_apply, Pi.pow_apply, Complex.ofRealCLM_apply, Complex.ofReal_one,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

private def logGaussianFirstDeriv (w ε : ℂ) (b x : ℝ) : ℂ :=
  gaussianMellinWeight (w - 1) ε x +
    w * gaussianLogMellinWeight (w - 1) ε b x -
    2 * ε * gaussianLogMellinWeight (w + 1) ε b x

private theorem continuousOn_gaussianLogMellinWeight_nonneg {w : ℂ} (hw : 0 < w.re) (ε : ℂ) {b : ℝ} (hb : 0 < b) :
    ContinuousOn (gaussianLogMellinWeight w ε b) (Ici 0) := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    apply continuousWithinAt_Ioi_iff_Ici.mp
    change Tendsto _ (𝓝[>] (0 : ℝ)) (𝓝 (gaussianLogMellinWeight w ε b 0))
    have hz : gaussianLogMellinWeight w ε b 0 = 0 := by simp [gaussianLogMellinWeight]
    rw [hz]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hp : Tendsto (fun x : ℝ => x ^ w.re) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.zero_rpow hw.ne'] using
        (Real.continuousAt_rpow_const 0 w.re (Or.inr hw.le)).tendsto.mono_left nhdsWithin_le_nhds
    have ht := (tendsto_log_mul_rpow_nhdsGT_zero hw).sub (hp.const_mul (Real.log b))
    have he : Tendsto (fun x : ℝ => Real.exp (-ε.re * x ^ 2)) (𝓝[>] 0) (𝓝 1) := by
      have hc : Continuous (fun x : ℝ => Real.exp (-ε.re * x ^ 2)) := by fun_prop
      simpa using hc.continuousAt.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    have hh := ht.abs.mul he
    simp only [mul_zero, sub_zero, abs_zero, zero_mul] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [gaussianLogMellinWeight, gaussianMellinWeight, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx,
      Complex.norm_exp, Real.log_div hx.ne' hb.ne', ← sub_mul,
      abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx _)]
    have hre : (-(ε * (x : ℂ) ^ 2)).re = -ε.re * x ^ 2 := by simp [pow_two]
    rw [hre]
    ring
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · exact Complex.continuous_ofReal.continuousAt.comp
        ((continuousAt_id.div_const b).log (ne_of_gt (div_pos hxpos hb)))
    · exact (Complex.continuousAt_ofReal_cpow_const x w (Or.inr hx0)).mul (by fun_prop)
private theorem hasDerivAt_gaussianLogMellinWeight {w : ℂ} (hw : 0 < w.re)
    (ε : ℂ) {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    HasDerivAt (gaussianLogMellinWeight w ε b) (logGaussianFirstDeriv w ε b x) x := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hpow := hasDerivAt_ofReal_cpow_const hx.ne' hw0
  have he := (((Complex.ofRealCLM.hasDerivAt (x := x)).pow 2).const_mul ε).neg.cexp
  have hlog : HasDerivAt (fun y : ℝ => (Real.log (y / b) : ℂ)) (x⁻¹ : ℝ) x := by
    apply ((Real.hasDerivAt_log hx.ne').sub_const (Real.log b)).ofReal_comp.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    rw [Real.log_div hy.ne' hb.ne']
  apply (hlog.mul (hpow.mul he)).congr_deriv
  have hp : (x : ℂ) ^ (w + 1) = (x : ℂ) ^ w * (x : ℂ) := by
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_one]
  have hm : (x : ℂ) ^ (w - 1) = (x : ℂ) ^ w * (x : ℂ)⁻¹ := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'),
      Complex.cpow_neg_one]
  dsimp only [logGaussianFirstDeriv, gaussianLogMellinWeight, gaussianMellinWeight]
  rw [hp, hm]
  simp only [Pi.neg_apply, Pi.pow_apply, Pi.mul_apply, Complex.ofRealCLM_apply, Complex.ofReal_one,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, Complex.ofReal_inv]
  ring

private def logGaussianSecondDeriv (w ε : ℂ) (b x : ℝ) : ℂ :=
  w * (w - 1) * gaussianLogMellinWeight (w - 2) ε b x +
    (2 * w - 1) * gaussianMellinWeight (w - 2) ε x -
    2 * ε * (2 * w + 1) * gaussianLogMellinWeight w ε b x -
    4 * ε * gaussianMellinWeight w ε x +
    4 * ε ^ 2 * gaussianLogMellinWeight (w + 2) ε b x

private theorem continuousOn_logGaussianFirstDeriv {w : ℂ} (hw : 1 < w.re)
    (ε : ℂ) {b : ℝ} (hb : 0 < b) :
    ContinuousOn (logGaussianFirstDeriv w ε b) (Ici 0) := by
  have hm : 0 < (w - 1).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hp : 0 < (w + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hc : Continuous (gaussianMellinWeight (w - 1) ε) :=
    (Complex.continuous_ofReal_cpow_const hm).mul (by fun_prop)
  exact (hc.continuousOn.add
    (continuousOn_const.mul (continuousOn_gaussianLogMellinWeight_nonneg hm ε hb))).sub
    (continuousOn_const.mul (continuousOn_gaussianLogMellinWeight_nonneg hp ε hb))

private theorem hasDerivAt_logGaussianFirstDeriv {w : ℂ} (hw : 1 < w.re)
    (ε : ℂ) {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    HasDerivAt (logGaussianFirstDeriv w ε b) (logGaussianSecondDeriv w ε b x) x := by
  have hm : 0 < (w - 1).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hp : 0 < (w + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  apply (((hasDerivAt_gaussianMellinWeight hm ε hx).add
    ((hasDerivAt_gaussianLogMellinWeight hm ε hb hx).const_mul w)).sub
    ((hasDerivAt_gaussianLogMellinWeight hp ε hb hx).const_mul (2 * ε))).congr_deriv
  dsimp only [logGaussianFirstDeriv, logGaussianSecondDeriv, gaussianFirstDeriv]
  rw [show w - 1 - 1 = w - 2 by ring, sub_add_cancel, add_sub_cancel_right,
    show w + 1 + 1 = w + 2 by ring]
  ring

private theorem integrable_logGaussianSecondDeriv {w ε : ℂ}
    (hw : 1 < w.re) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (logGaussianSecondDeriv w ε b) (Ioi 0) := by
  have hm : -1 < (w - 2).re := by simp only [Complex.sub_re, show (2 : ℂ).re = 2 by norm_num]; linarith
  have hp : -1 < (w + 2).re := by simp only [Complex.add_re, show (2 : ℂ).re = 2 by norm_num]; linarith
  exact ((((integrable_gaussianLogMellinWeight hm hε hb).const_mul (w * (w - 1))).add
    ((integrable_gaussianMellinWeight hm hε).const_mul (2 * w - 1))).sub
    ((integrable_gaussianLogMellinWeight (by linarith) hε hb).const_mul (2 * ε * (2 * w + 1)))).sub
    ((integrable_gaussianMellinWeight (by linarith) hε).const_mul (4 * ε)) |>.add
    ((integrable_gaussianLogMellinWeight hp hε hb).const_mul (4 * ε ^ 2))

/-- Five explicit absolute moments bound the logarithmic second derivative. -/
def gaussianLogSecondVariation (w ε : ℂ) (X b δ : ℝ) : ℝ :=
  (‖w‖ * ‖w - 1‖) * gaussianFractionalLogBudget (w.re - 2) ε.re X b δ +
    ‖2 * w - 1‖ * gaussianRealMoment (w.re - 2) ε.re +
    (2 * ‖ε‖ * ‖2 * w + 1‖) * gaussianFractionalLogBudget w.re ε.re X b δ +
    (4 * ‖ε‖) * gaussianRealMoment w.re ε.re +
    (4 * ‖ε‖ ^ 2) * gaussianFractionalLogBudget (w.re + 2) ε.re X b δ

private theorem integral_norm_logGaussianSecondDeriv_le {w ε : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hwδ : -1 < w.re - 2 - δ) (hε : 0 < ε.re)
    {X b : ℝ} (hX : 0 < X) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), ‖logGaussianSecondDeriv w ε b x‖) ≤
      gaussianLogSecondVariation w ε X b δ := by
  have hw : 1 < w.re := by linarith
  have hm : -1 < (w - 2).re := by simp only [Complex.sub_re, show (2 : ℂ).re = 2 by norm_num]; linarith
  have hp : -1 < (w + 2).re := by simp only [Complex.add_re, show (2 : ℂ).re = 2 by norm_num]; linarith
  have h0 := (integrable_gaussianLogMellinWeight hm hε hb).norm.const_mul (‖w‖ * ‖w - 1‖)
  have h1 := (integrable_gaussianMellinWeight hm hε).norm.const_mul ‖2 * w - 1‖
  have h2 := (integrable_gaussianLogMellinWeight (show -1 < w.re by linarith) hε hb).norm.const_mul
    (2 * ‖ε‖ * ‖2 * w + 1‖)
  have h3 := (integrable_gaussianMellinWeight (show -1 < w.re by linarith) hε).norm.const_mul (4 * ‖ε‖)
  have h4 := (integrable_gaussianLogMellinWeight hp hε hb).norm.const_mul (4 * ‖ε‖ ^ 2)
  have h01 : IntegrableOn (fun x : ℝ =>
      ‖w‖ * ‖w - 1‖ * ‖gaussianLogMellinWeight (w - 2) ε b x‖ +
        ‖2 * w - 1‖ * ‖gaussianMellinWeight (w - 2) ε x‖) (Ioi 0) := h0.add h1
  have h012 : IntegrableOn (fun x : ℝ =>
      ‖w‖ * ‖w - 1‖ * ‖gaussianLogMellinWeight (w - 2) ε b x‖ +
        ‖2 * w - 1‖ * ‖gaussianMellinWeight (w - 2) ε x‖ +
        (2 * ‖ε‖ * ‖2 * w + 1‖) * ‖gaussianLogMellinWeight w ε b x‖) (Ioi 0) := h01.add h2
  have h0123 : IntegrableOn (fun x : ℝ =>
      ‖w‖ * ‖w - 1‖ * ‖gaussianLogMellinWeight (w - 2) ε b x‖ +
        ‖2 * w - 1‖ * ‖gaussianMellinWeight (w - 2) ε x‖ +
        (2 * ‖ε‖ * ‖2 * w + 1‖) * ‖gaussianLogMellinWeight w ε b x‖ +
        (4 * ‖ε‖) * ‖gaussianMellinWeight w ε x‖) (Ioi 0) := h012.add h3
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ),
        ‖w‖ * ‖w - 1‖ * ‖gaussianLogMellinWeight (w - 2) ε b x‖ +
        ‖2 * w - 1‖ * ‖gaussianMellinWeight (w - 2) ε x‖ +
        (2 * ‖ε‖ * ‖2 * w + 1‖) * ‖gaussianLogMellinWeight w ε b x‖ +
        (4 * ‖ε‖) * ‖gaussianMellinWeight w ε x‖ +
        (4 * ‖ε‖ ^ 2) * ‖gaussianLogMellinWeight (w + 2) ε b x‖ := by
      apply integral_mono_ae (integrable_logGaussianSecondDeriv hw hε hb).norm (h0123.add h4)
      exact Filter.Eventually.of_forall fun x => by
        have hn (a c d e f : ℂ) : ‖a + c - d - e + f‖ ≤
            ‖a‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
          have h1 := norm_add_le a c
          have h2 := norm_sub_le (a + c) d
          have h3 := norm_sub_le (a + c - d) e
          have h4 := norm_add_le (a + c - d - e) f
          linarith only [h1, h2, h3, h4]
        unfold logGaussianSecondDeriv
        have hlast : ‖(4 : ℂ) * ε ^ 2 * gaussianLogMellinWeight (w + 2) ε b x‖ =
            4 * ‖ε‖ ^ 2 * ‖gaussianLogMellinWeight (w + 2) ε b x‖ := by
          rw [norm_mul, norm_mul, norm_pow]
          norm_num
        have hh := hn
          (w * (w - 1) * gaussianLogMellinWeight (w - 2) ε b x)
          ((2 * w - 1) * gaussianMellinWeight (w - 2) ε x)
          (2 * ε * (2 * w + 1) * gaussianLogMellinWeight w ε b x)
          (4 * ε * gaussianMellinWeight w ε x)
          (4 * ε ^ 2 * gaussianLogMellinWeight (w + 2) ε b x)
        simpa only [Pi.add_apply, hlast, norm_mul, norm_ofNat, norm_pow] using hh
    _ ≤ _ := by
      rw [integral_add h0123 h4, integral_add h012 h3, integral_add h01 h2, integral_add h0 h1,
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_norm_gaussianMellinWeight hm hε,
        integral_norm_gaussianMellinWeight (by linarith) hε]
      have h0' := integral_norm_gaussianLogMellinWeight_le_fractional (w := w - 2) hδ
        (by simpa only [Complex.sub_re, show (2 : ℂ).re = 2 by norm_num] using hwδ) hε hX hb
      have h2' := integral_norm_gaussianLogMellinWeight_le_fractional (w := w) hδ
        (by linarith) hε hX hb
      have h4' := integral_norm_gaussianLogMellinWeight_le_fractional (w := w + 2) hδ
        (by simp only [Complex.add_re, show (2 : ℂ).re = 2 by norm_num]; linarith) hε hX hb
      simp only [Complex.sub_re, Complex.add_re, show (2 : ℂ).re = 2 by norm_num] at h0' h4' ⊢
      unfold gaussianLogSecondVariation
      exact _root_.add_le_add (_root_.add_le_add
        (_root_.add_le_add (_root_.add_le_add
          (mul_le_mul_of_nonneg_left h0' (by positivity)) le_rfl)
          (mul_le_mul_of_nonneg_left h2' (by positivity))) le_rfl)
          (mul_le_mul_of_nonneg_left h4' (by positivity))

private theorem intervalIntegrable_logGaussianSecondDeriv {w ε : ℂ}
    (hw : 1 < w.re) (hε : 0 < ε.re) {B : ℝ} (hB : 0 < B)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (logGaussianSecondDeriv w ε B) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  exact (integrable_logGaussianSecondDeriv hw hε hB).mono_set
    (fun x hx => lt_of_le_of_lt ha hx.1)

private theorem intervalIntegrable_logGaussian {w : ℂ} (hw : 0 < w.re)
    (ε : ℂ) {B : ℝ} (hB : 0 < B) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (gaussianLogMellinWeight w ε B) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (continuousOn_gaussianLogMellinWeight_nonneg hw ε hB).mono
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact ha.trans hx.1

private theorem logGaussian_trapezoid_cell {w ε : ℂ} (hw : 1 < w.re) (hε : 0 < ε.re)
    {B : ℝ} (hB : 0 < B) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖((b - a : ℝ) : ℂ) * (gaussianLogMellinWeight w ε B b + gaussianLogMellinWeight w ε B a) / 2 -
        ∫ x in a..b, gaussianLogMellinWeight w ε B x‖ ≤
      (b - a) ^ 2 / 8 * ∫ x in a..b, ‖logGaussianSecondDeriv w ε B x‖ := by
  let R := fun x : ℝ => ((x - (a + b) / 2 : ℝ) : ℂ)
  let K := fun x : ℝ => (((x - a) * (x - b) / 2 : ℝ) : ℂ)
  have hsubset : uIcc a b ⊆ Ici 0 := by
    rw [uIcc_of_le hab]
    exact fun x hx => ha.trans hx.1
  have hc := (continuousOn_gaussianLogMellinWeight_nonneg (show 0 < w.re by linarith) ε hB).mono hsubset
  have hd := (continuousOn_logGaussianFirstDeriv hw ε hB).mono hsubset
  have hD := intervalIntegrable_logGaussianSecondDeriv hw hε hB ha hab
  have hxpos (x : ℝ) (hx : x ∈ Ioo (min a b) (max a b)) : 0 < x := by
    rw [min_eq_left hab, max_eq_right hab] at hx
    linarith [hx.1]
  have hR (x : ℝ) : HasDerivAt R 1 x := by
    simpa [R] using ((hasDerivAt_id x).sub_const ((a + b) / 2)).ofReal_comp
  have hK (x : ℝ) : HasDerivAt K (R x) x := by
    apply ((((hasDerivAt_id x).sub_const a).mul
      ((hasDerivAt_id x).sub_const b)).div_const 2).ofReal_comp.congr_deriv
    dsimp [R]
    push_cast
    ring
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := R) (u' := fun _ => (1 : ℂ))
    (v := gaussianLogMellinWeight w ε B) (v' := logGaussianFirstDeriv w ε B)
    (a := a) (b := b) (by dsimp [R]; fun_prop) hc
    (fun x _ => hR x)
    (fun x hx => hasDerivAt_gaussianLogMellinWeight (by linarith) ε hB (hxpos x hx))
    intervalIntegrable_const hd.intervalIntegrable
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := K) (u' := R) (v := logGaussianFirstDeriv w ε B) (v' := logGaussianSecondDeriv w ε B)
    (a := a) (b := b) (by dsimp [K]; fun_prop) hd
    (fun x _ => hK x) (fun x hx => hasDerivAt_logGaussianFirstDeriv hw ε hB (hxpos x hx))
    (by apply Continuous.intervalIntegrable; dsimp [R]; fun_prop) hD
  have hKa : K a = 0 := by simp [K]
  have hKb : K b = 0 := by simp [K]
  rw [hKa, hKb, zero_mul, zero_mul, sub_self, zero_sub] at h2
  simp only [one_mul] at h1
  have he : ((b - a : ℝ) : ℂ) * (gaussianLogMellinWeight w ε B b + gaussianLogMellinWeight w ε B a) / 2 -
      ∫ x in a..b, gaussianLogMellinWeight w ε B x =
        -(∫ x in a..b, K x * logGaussianSecondDeriv w ε B x) := by
    rw [h2, neg_neg, h1]
    dsimp [R]
    push_cast
    ring
  rw [he, norm_neg]
  calc
    _ ≤ ∫ x in a..b, ((b - a) ^ 2 / 8) * ‖logGaussianSecondDeriv w ε B x‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab
        (Filter.Eventually.of_forall fun x hx => ?_) (hD.norm.const_mul _)
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hKsign : (x - a) * (x - b) / 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by linarith [hx.1]) (by linarith [hx.2])) (by norm_num)
      change ‖(((x - a) * (x - b) / 2 : ℝ) : ℂ)‖ ≤ _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hKsign]
      nlinarith [sq_nonneg (2 * x - a - b)]
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- The finite trapezoidal error uses the integrable second derivative;
no second derivative at the singular origin is required. -/
theorem norm_sum_gaussianLogMellinWeight_sub_trapezoid_integral_le {w ε : ℂ}
    {δ : ℝ} (hδ : 0 < δ) (hwδ : -1 < w.re - 2 - δ) (hε : 0 < ε.re)
    {X B : ℝ} (hX : 0 < X) (hB : 0 < B) {b : ℝ} (hb : 0 < b) (N : ℕ) :
    ‖(∑ n ∈ range N, gaussianLogMellinWeight w ε B (b * (n + 1))) -
        gaussianLogMellinWeight w ε B (b * N) / 2 -
        (b : ℂ)⁻¹ * ∫ x in (0 : ℝ)..(b * N), gaussianLogMellinWeight w ε B x‖ ≤
      b / 8 * gaussianLogSecondVariation w ε X B δ := by
  have hw : 1 < w.re := by linarith
  have hzero : gaussianLogMellinWeight w ε B 0 = 0 := by simp [gaussianLogMellinWeight]
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => b * n) (n := N) (f := gaussianLogMellinWeight w ε B)
    (fun n _ => by
      apply intervalIntegrable_logGaussian (by linarith) ε hB (by positivity)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) hb.le)
  have hsplit' := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => b * n) (n := N) (f := fun x => ‖logGaussianSecondDeriv w ε B x‖)
    (fun n _ => by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (intervalIntegrable_logGaussianSecondDeriv hw hε hB (by positivity)
          (show b * (n : ℝ) ≤ b * (n + 1) by nlinarith [hb])).norm)
  simp only [Nat.cast_zero, mul_zero, Nat.cast_add, Nat.cast_one] at hsplit hsplit'
  have htrap := GaloisForLFunctions.HTGeometry.sum_trapezoid_complex
    (fun x => gaussianLogMellinWeight w ε B (b * x)) N
  rw [sum_range_succ'] at htrap
  simp only [Nat.cast_zero, mul_zero, hzero, add_zero, zero_add,
    Nat.cast_add, Nat.cast_one] at htrap
  have hmain : ‖(b : ℂ) * ((∑ n ∈ range N, gaussianLogMellinWeight w ε B (b * (n + 1))) -
      gaussianLogMellinWeight w ε B (b * N) / 2) -
      ∫ x in (0 : ℝ)..(b * N), gaussianLogMellinWeight w ε B x‖ ≤
      b ^ 2 / 8 * ∫ x in (0 : ℝ)..(b * N), ‖logGaussianSecondDeriv w ε B x‖ := by
    rw [← htrap, mul_sum, ← hsplit, ← sum_sub_distrib, ← hsplit', mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
    have hh := logGaussian_trapezoid_cell hw hε hB
      (show 0 ≤ b * n by positivity)
      (show b * (n : ℝ) ≤ b * (n + 1) by nlinarith [hb])
    simpa only [show b * ((n : ℝ) + 1) - b * n = b by ring, mul_div_assoc] using hh
  have htotal : (∫ x in (0 : ℝ)..(b * N), ‖logGaussianSecondDeriv w ε B x‖) ≤
      gaussianLogSecondVariation w ε X B δ := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    refine (setIntegral_mono_set (integrable_logGaussianSecondDeriv hw hε hB).norm
      (Filter.Eventually.of_forall fun x => norm_nonneg _) ?_).trans
      (integral_norm_logGaussianSecondDeriv_le hδ hwδ hε hX hB)
    exact Filter.Eventually.of_forall fun x hx => hx.1
  have he : (b : ℂ) * (((∑ n ∈ range N, gaussianLogMellinWeight w ε B (b * (n + 1))) -
      gaussianLogMellinWeight w ε B (b * N) / 2) -
      (b : ℂ)⁻¹ * ∫ x in (0 : ℝ)..(b * N), gaussianLogMellinWeight w ε B x) =
      (b : ℂ) * ((∑ n ∈ range N, gaussianLogMellinWeight w ε B (b * (n + 1))) -
      gaussianLogMellinWeight w ε B (b * N) / 2) -
        ∫ x in (0 : ℝ)..(b * N), gaussianLogMellinWeight w ε B x := by
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hb.ne'), one_mul]
  rw [← he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb] at hmain
  have hh := hmain.trans (mul_le_mul_of_nonneg_left htotal (by positivity : 0 ≤ b ^ 2 / 8))
  apply le_of_mul_le_mul_left (a := b) _ hb
  convert hh using 1; ring


/-- Second-order discrepancy for a complete logarithmic Gaussian lattice. -/
theorem norm_tsum_gaussianLogMellinWeight_sub_integral_second_le {w ε : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hwδ : -1 < w.re - 2 - δ) (hw2 : w.re ≤ 2) (hε : 0 < ε.re)
    {X B b : ℝ} (hX : 0 < X) (hB : 0 < B) (hb : 0 < b) :
    ‖(∑' n : ℕ, gaussianLogMellinWeight w ε B (b * (n + 1))) -
        (b : ℂ)⁻¹ * ∫ x in Ioi (0 : ℝ), gaussianLogMellinWeight w ε B x‖ ≤
      b / 8 * gaussianLogSecondVariation w ε X B δ := by
  have hs := summable_gaussianLogMellinWeight_lattice hw2 hε hb hB
  have hs0 : Summable (fun n : ℕ => gaussianLogMellinWeight w ε B (b * n)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hs
  have hz := hs0.tendsto_atTop_zero.div_const (2 : ℂ)
  have hN : Tendsto (fun n : ℕ => b * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hb
  have hi := intervalIntegral_tendsto_integral_Ioi 0
    (integrable_gaussianLogMellinWeight (by linarith : -1 < w.re) hε hB) hN
  have hh := le_of_tendsto
    (((hs.hasSum.tendsto_sum_nat.sub hz).sub (hi.const_mul (b : ℂ)⁻¹)).norm)
    (Filter.Eventually.of_forall fun N =>
      norm_sum_gaussianLogMellinWeight_sub_trapezoid_integral_le hδ hwδ hε hX hB hb N)
  simpa only [zero_div, sub_zero] using hh

private theorem gaussianRealMoment_nonneg {q α : ℝ} (hq : -1 < q) (hα : 0 < α) :
    0 ≤ gaussianRealMoment q α := by
  have hG := (Real.Gamma_pos_of_pos (show 0 < (q + 1) / 2 by linarith)).le
  unfold gaussianRealMoment
  positivity

private theorem gaussianRealMoment_scale {α X : ℝ} (hα : 0 < α) (hX : 0 < X)
    (hscale : α * X ^ 2 = 2) (q : ℝ) :
    gaussianRealMoment q α = X ^ (q + 1) * gaussianRealMoment q 2 := by
  have hi : 1 / α = (1 / 2 : ℝ) * X ^ 2 := by
    apply (div_eq_iff hα.ne').mpr
    nlinarith only [hscale]
  have hp : (X ^ 2) ^ ((q + 1) / 2) = X ^ (q + 1) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hX.le]
    congr 1
    ring
  unfold gaussianRealMoment
  rw [hi, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) (sq_nonneg X), hp]
  ring

private def fractionalLogScaleBudget (q δ L : ℝ) : ℝ :=
  (gaussianRealMoment (q + δ) 2 + gaussianRealMoment (q - δ) 2) / δ +
    L * gaussianRealMoment q 2

private theorem gaussianFractionalLogBudget_scale {α X : ℝ} (hα : 0 < α) (hX : 0 < X)
    (hscale : α * X ^ 2 = 2) (q b δ : ℝ) :
    gaussianFractionalLogBudget q α X b δ =
      X ^ (q + 1) * fractionalLogScaleBudget q δ |Real.log (X / b)| := by
  have hp : X ^ (-δ) * X ^ (q + δ + 1) = X ^ (q + 1) := by
    rw [← Real.rpow_add hX]
    congr 1
    ring
  have hm : X ^ δ * X ^ (q - δ + 1) = X ^ (q + 1) := by
    rw [← Real.rpow_add hX]
    congr 1
    ring
  unfold gaussianFractionalLogBudget
  rw [gaussianRealMoment_scale hα hX hscale, gaussianRealMoment_scale hα hX hscale,
    gaussianRealMoment_scale hα hX hscale]
  rw [← mul_assoc (X ^ (-δ)), ← mul_assoc (X ^ δ), hp, hm]
  unfold fractionalLogScaleBudget
  ring

private theorem fractionalLogScaleBudget_nonneg {q δ L : ℝ}
    (hδ : 0 < δ) (hq : -1 < q - δ) (hL : 0 ≤ L) :
    0 ≤ fractionalLogScaleBudget q δ L := by
  have hp := gaussianRealMoment_nonneg (show -1 < q + δ by linarith) (by norm_num : (0 : ℝ) < 2)
  have hm := gaussianRealMoment_nonneg hq (by norm_num : (0 : ℝ) < 2)
  have h0 := gaussianRealMoment_nonneg (show -1 < q by linarith) (by norm_num : (0 : ℝ) < 2)
  unfold fractionalLogScaleBudget
  positivity

private theorem fractionalLogScaleBudget_le {q δ L : ℝ}
    (hδ : 0 < δ) (hq : -1 < q - δ) (hL : 0 ≤ L) :
    fractionalLogScaleBudget q δ L ≤ fractionalLogScaleBudget q δ 1 * (1 + L) := by
  have hp := gaussianRealMoment_nonneg (show -1 < q + δ by linarith) (by norm_num : (0 : ℝ) < 2)
  have hm := gaussianRealMoment_nonneg hq (by norm_num : (0 : ℝ) < 2)
  have h0 := gaussianRealMoment_nonneg (show -1 < q by linarith) (by norm_num : (0 : ℝ) < 2)
  have hA : 0 ≤ (gaussianRealMoment (q + δ) 2 + gaussianRealMoment (q - δ) 2) / δ := by positivity
  unfold fractionalLogScaleBudget
  nlinarith only [h0, mul_nonneg hA hL]

/-- An explicit constant for the second-order logarithmic first-moment error. -/
def gaussianLogSecondMomentConstant (σ : ℝ) : ℝ :=
  4 * fractionalLogScaleBudget (-σ) ((1 - σ) / 2) 1 +
    5 * gaussianRealMoment (-σ) 2 +
    80 * fractionalLogScaleBudget (2 - σ) ((1 - σ) / 2) 1 +
    32 * gaussianRealMoment (2 - σ) 2 +
    256 * fractionalLogScaleBudget (4 - σ) ((1 - σ) / 2) 1

/-- Positivity of the logarithmic second-order constant on the open strip. -/
theorem gaussianLogSecondMomentConstant_nonneg {σ : ℝ} (hσ : σ < 1) :
    0 ≤ gaussianLogSecondMomentConstant σ := by
  have hδ : 0 < (1 - σ) / 2 := by linarith
  have h0 := fractionalLogScaleBudget_nonneg (q := -σ) hδ (by linarith) (by norm_num : (0 : ℝ) ≤ 1)
  have h1 := gaussianRealMoment_nonneg (show -1 < -σ by linarith) (by norm_num : (0 : ℝ) < 2)
  have h2 := fractionalLogScaleBudget_nonneg (q := 2 - σ) hδ (by linarith) (by norm_num : (0 : ℝ) ≤ 1)
  have h3 := gaussianRealMoment_nonneg (show -1 < 2 - σ by linarith) (by norm_num : (0 : ℝ) < 2)
  have h4 := fractionalLogScaleBudget_nonneg (q := 4 - σ) hδ (by linarith) (by norm_num : (0 : ℝ) ≤ 1)
  unfold gaussianLogSecondMomentConstant
  positivity

private theorem norm_mul_gaussianLogSecondVariation_le {w ε : ℂ} {t X δ : ℝ}
    (hδ : 0 < δ) (hwδ : -1 < w.re - 2 - δ) (hε : 0 < ε.re)
    (ht : 1 ≤ t) (hX : 0 < X) (hscale : ε.re * X ^ 2 = 2)
    (hwsize : ‖w‖ ≤ 2 * t) (hwminus : ‖w - 1‖ ≤ 2 * t)
    (hwtm : ‖2 * w - 1‖ ≤ 5 * t) (hwtp : ‖2 * w + 1‖ ≤ 5 * t)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) (b : ℝ) :
    ‖ε / (t : ℂ)‖ * gaussianLogSecondVariation w ε X b δ ≤
      8 * (4 * fractionalLogScaleBudget (w.re - 2) δ 1 +
        5 * gaussianRealMoment (w.re - 2) 2 +
        80 * fractionalLogScaleBudget w.re δ 1 +
        32 * gaussianRealMoment w.re 2 +
        256 * fractionalLogScaleBudget (w.re + 2) δ 1) *
        t ^ 2 * X ^ (w.re - 3) * (1 + |Real.log (X / b)|) := by
  let L := |Real.log (X / b)|
  let K0 := fractionalLogScaleBudget (w.re - 2) δ L
  let M0 := gaussianRealMoment (w.re - 2) 2
  let K1 := fractionalLogScaleBudget w.re δ L
  let M1 := gaussianRealMoment w.re 2
  let K2 := fractionalLogScaleBudget (w.re + 2) δ L
  let E := ‖ε‖ * X ^ 2
  have hK0 : 0 ≤ K0 := fractionalLogScaleBudget_nonneg hδ hwδ (abs_nonneg _)
  have hM0 : 0 ≤ M0 := gaussianRealMoment_nonneg (by linarith) (by norm_num)
  have hK1 : 0 ≤ K1 := fractionalLogScaleBudget_nonneg hδ (by linarith) (abs_nonneg _)
  have hM1 : 0 ≤ M1 := gaussianRealMoment_nonneg (by linarith) (by norm_num)
  have hK2 : 0 ≤ K2 := fractionalLogScaleBudget_nonneg hδ (by linarith) (abs_nonneg _)
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have ht0 : 0 < t := by linarith
  have htt : t ≤ t ^ 2 := by nlinarith only [ht]
  have he : ‖ε / (t : ℂ)‖ ≤ 4 * ε.re := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    exact (div_le_iff₀ ht0).mpr hsector
  have hE : E ≤ 8 * t := by
    calc
      _ ≤ (4 * ε.re * t) * X ^ 2 := mul_le_mul_of_nonneg_right hsector (sq_nonneg X)
      _ = _ := by linear_combination 4 * t * hscale
  have hp : X ^ (w.re + 1) = X ^ (w.re - 1) * X ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_add hX]
    congr 1
    ring
  have hpp : X ^ (w.re + 2 + 1) = X ^ (w.re - 1) * (X ^ 2) ^ 2 := by
    rw [pow_two, ← Real.rpow_two X, ← Real.rpow_add hX, ← Real.rpow_add hX]
    congr 1
    ring
  have hV : gaussianLogSecondVariation w ε X b δ =
      X ^ (w.re - 1) * (‖w‖ * ‖w - 1‖ * K0 + ‖2 * w - 1‖ * M0 +
        2 * E * ‖2 * w + 1‖ * K1 + 4 * E * M1 + 4 * E ^ 2 * K2) := by
    unfold gaussianLogSecondVariation
    rw [gaussianFractionalLogBudget_scale hε hX hscale,
      gaussianRealMoment_scale hε hX hscale,
      gaussianFractionalLogBudget_scale hε hX hscale,
      gaussianRealMoment_scale hε hX hscale,
      gaussianFractionalLogBudget_scale hε hX hscale,
      show w.re - 2 + 1 = w.re - 1 by ring, hp, hpp]
    dsimp [K0, M0, K1, M1, K2, L, E]
    ring
  have hV0 : 0 ≤ gaussianLogSecondVariation w ε X b δ := by rw [hV]; positivity
  have hc0 : ‖w‖ * ‖w - 1‖ ≤ 4 * t ^ 2 := by
    have hh := mul_le_mul hwsize hwminus (norm_nonneg _) (by positivity : 0 ≤ 2 * t)
    nlinarith only [hh]
  have hc1 : ‖2 * w - 1‖ ≤ 5 * t ^ 2 := by linarith only [hwtm, htt]
  have hc2 : 2 * E * ‖2 * w + 1‖ ≤ 80 * t ^ 2 := by
    have hh := mul_le_mul hE hwtp (norm_nonneg _) (by positivity : 0 ≤ 8 * t)
    nlinarith only [hh]
  have hc3 : 4 * E ≤ 32 * t ^ 2 := by linarith only [hE, htt]
  have hc4 : 4 * E ^ 2 ≤ 256 * t ^ 2 := by
    have hh := mul_le_mul hE hE hE0 (by positivity : 0 ≤ 8 * t)
    nlinarith only [hh]
  have hVbound : gaussianLogSecondVariation w ε X b δ ≤
      X ^ (w.re - 1) * t ^ 2 * (4 * K0 + 5 * M0 + 80 * K1 + 32 * M1 + 256 * K2) := by
    rw [hV, mul_assoc (X ^ (w.re - 1)) (t ^ 2)]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hX.le _)
    nlinarith only [mul_le_mul_of_nonneg_right hc0 hK0, mul_le_mul_of_nonneg_right hc1 hM0,
      mul_le_mul_of_nonneg_right hc2 hK1, mul_le_mul_of_nonneg_right hc3 hM1,
      mul_le_mul_of_nonneg_right hc4 hK2]
  have hpower : ε.re * X ^ (w.re - 1) = 2 * X ^ (w.re - 3) := by
    have hx : X ^ (w.re - 1) = X ^ (w.re - 3) * X ^ 2 := by
      rw [← Real.rpow_two, ← Real.rpow_add hX]
      congr 1
      ring
    rw [hx]
    linear_combination X ^ (w.re - 3) * hscale
  have hK0' := fractionalLogScaleBudget_le hδ hwδ (abs_nonneg (Real.log (X / b)))
  have hK1' := fractionalLogScaleBudget_le (q := w.re) hδ (by linarith) (abs_nonneg (Real.log (X / b)))
  have hK2' := fractionalLogScaleBudget_le (q := w.re + 2) hδ (by linarith) (abs_nonneg (Real.log (X / b)))
  have hM0' : M0 ≤ M0 * (1 + L) := by nlinarith [abs_nonneg (Real.log (X / b))]
  have hM1' : M1 ≤ M1 * (1 + L) := by nlinarith [abs_nonneg (Real.log (X / b))]
  calc
    _ ≤ (4 * ε.re) * (X ^ (w.re - 1) * t ^ 2 *
        (4 * K0 + 5 * M0 + 80 * K1 + 32 * M1 + 256 * K2)) :=
      mul_le_mul he hVbound hV0 (by positivity)
    _ = 8 * t ^ 2 * X ^ (w.re - 3) * (4 * K0 + 5 * M0 + 80 * K1 + 32 * M1 + 256 * K2) := by
      calc
        _ = 4 * (ε.re * X ^ (w.re - 1)) * t ^ 2 *
            (4 * K0 + 5 * M0 + 80 * K1 + 32 * M1 + 256 * K2) := by ring
        _ = _ := by rw [hpower]; ring
    _ ≤ 8 * t ^ 2 * X ^ (w.re - 3) *
        ((4 * fractionalLogScaleBudget (w.re - 2) δ 1 + 5 * M0 +
          80 * fractionalLogScaleBudget w.re δ 1 + 32 * M1 +
          256 * fractionalLogScaleBudget (w.re + 2) δ 1) * (1 + L)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      dsimp [K0, K1, K2, L] at *
      nlinarith only [hK0', hK1', hK2', hM0', hM1']
    _ = _ := by dsimp [M0, M1, L]; ring

private theorem integral_gaussianLogMellinWeight_split {w ε : ℂ}
    (hw : 0 < w.re) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), gaussianLogMellinWeight w ε b x) =
      (∫ x in Ioi (0 : ℝ), gaussianLogMellinWeight w ε 1 x) -
        (Real.log b : ℂ) * ((1 / 2 : ℂ) * Complex.Gamma ((w + 1) / 2) *
          ε ^ (-(w + 1) / 2)) := by
  have he : ∀ x ∈ Ioi (0 : ℝ), gaussianLogMellinWeight w ε b x =
      gaussianLogMellinWeight w ε 1 x - (Real.log b : ℂ) * gaussianMellinWeight w ε x := by
    intro x hx
    rw [gaussianLogMellinWeight, gaussianLogMellinWeight, div_one,
      Real.log_div hx.ne' hb.ne', Complex.ofReal_sub, sub_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi he,
    integral_sub (integrableOn_gaussianLogMellinWeight hw hε zero_lt_one)
      ((integrableOn_gaussianMellinWeight hw hε).const_mul _),
    integral_const_mul, integral_gaussianMellinWeight hw hε]

/-- A second-order logarithmic fibre estimate retaining both signed continuum
terms and the full Gaussian power saving. -/
theorem norm_tsum_gaussianLogFirstMoment_sub_poles_second_physical_le {σ t X : ℝ} {ε : ℂ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (ht : 2 ≤ t) (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) (hX : 0 < X) (hscale : ε.re * X ^ 2 = 2)
    {b : ℝ} (hb : 0 < b) :
    ‖(ε / (t : ℂ)) * (∑' n : ℕ,
        gaussianLogMellinWeight (2 - ((σ : ℂ) + t * I)) ε b (b * (n + 1))) -
      (b : ℂ)⁻¹ * (gaussianFirstMomentLogPole ((σ : ℂ) + t * I) ε t -
        (Real.log b : ℂ) * gaussianFirstMomentPole ((σ : ℂ) + t * I) ε t)‖ ≤
      gaussianLogSecondMomentConstant σ * b * t ^ 2 * X ^ (-1 - σ) * (1 + |Real.log (X / b)|) := by
  let w : ℂ := 2 - ((σ : ℂ) + t * I)
  have hwre : w.re = 2 - σ := by simp [w]
  have hw : 1 < w.re := by rw [hwre]; linarith
  have hw2 : w.re ≤ 2 := by rw [hwre]; linarith
  have ht0 : 0 < t := by linarith
  have hwsize : ‖w‖ ≤ 2 * t := by
    have he : w = ((2 - σ : ℝ) : ℂ) - (t : ℂ) * I := by dsimp [w]; push_cast; ring
    rw [he]
    calc
      _ ≤ ‖((2 - σ : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_sub_le _ _
      _ = 2 - σ + t := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_pos ht0]
      _ ≤ _ := by linarith
  have hδ : 0 < (1 - σ) / 2 := by linarith
  have hwδ : -1 < w.re - 2 - (1 - σ) / 2 := by rw [hwre]; linarith
  have hwminus : ‖w - 1‖ ≤ 2 * t := by
    have he : w - 1 = ((1 - σ : ℝ) : ℂ) - (t : ℂ) * I := by dsimp [w]; push_cast; ring
    rw [he]
    calc
      _ ≤ ‖((1 - σ : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_sub_le _ _
      _ = 1 - σ + t := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_pos ht0]
      _ ≤ _ := by linarith
  have hwtm : ‖2 * w - 1‖ ≤ 5 * t := by
    have hh := norm_sub_le (2 * w) 1
    simp only [norm_mul, norm_ofNat, norm_one] at hh
    linarith only [hh, hwsize, ht]
  have hwtp : ‖2 * w + 1‖ ≤ 5 * t := by
    have hh := norm_add_le (2 * w) 1
    simp only [norm_mul, norm_ofNat, norm_one] at hh
    linarith only [hh, hwsize, ht]
  have hh := mul_le_mul_of_nonneg_left
    (norm_tsum_gaussianLogMellinWeight_sub_integral_second_le hδ hwδ hw2 hε hX hb hb)
      (norm_nonneg (ε / (t : ℂ)))
  rw [← norm_mul, integral_gaussianLogMellinWeight_split (by linarith) hε hb] at hh
  have heq : (ε / (t : ℂ)) * ((∑' n : ℕ, gaussianLogMellinWeight w ε b (b * (n + 1))) -
      (b : ℂ)⁻¹ * ((∫ x in Ioi (0 : ℝ), gaussianLogMellinWeight w ε 1 x) -
        (Real.log b : ℂ) * ((1 / 2 : ℂ) * Complex.Gamma ((w + 1) / 2) *
          ε ^ (-(w + 1) / 2)))) =
      (ε / (t : ℂ)) * (∑' n : ℕ, gaussianLogMellinWeight w ε b (b * (n + 1))) -
        (b : ℂ)⁻¹ * (gaussianFirstMomentLogPole ((σ : ℂ) + t * I) ε t -
          (Real.log b : ℂ) * gaussianFirstMomentPole ((σ : ℂ) + t * I) ε t) := by
    have hp : w + 1 = 3 - ((σ : ℂ) + t * I) := by dsimp [w]; ring
    unfold gaussianFirstMomentLogPole gaussianFirstMomentPole
    rw [hp]
    dsimp [w]
    ring
  rw [heq] at hh
  apply hh.trans
  have hv := mul_le_mul_of_nonneg_left
    (norm_mul_gaussianLogSecondVariation_le hδ hwδ hε (by linarith : 1 ≤ t) hX
      hscale hwsize hwminus hwtm hwtp hsector b) (by positivity : 0 ≤ b / 8)
  rw [hwre] at hv
  simp only [show 2 - σ - 2 = -σ by ring,
    show 2 - σ + 2 = 4 - σ by ring, show 2 - σ - 3 = -1 - σ by ring] at hv
  unfold gaussianLogSecondMomentConstant
  convert hv using 1 <;> ring

#print axioms abs_log_div_le_fractional
#print axioms integral_norm_gaussianLogMellinWeight_le_fractional
#print axioms norm_sum_gaussianLogMellinWeight_sub_trapezoid_integral_le
#print axioms norm_tsum_gaussianLogMellinWeight_sub_integral_second_le
#print axioms norm_tsum_gaussianLogFirstMoment_sub_poles_second_physical_le

end GaloisForLFunctions.ExceptionalLayerTheory
