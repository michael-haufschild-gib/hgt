import GaloisForLFunctions.HTGeometry.RelativeGreenExactification
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.CDF

/-!
# Hypoexponential formation of the Green-exactified pair response

The Green-exactified response `H_{a,b}` is the distribution function of the hypoexponential law
`Exp(a) ∗ Exp(b) ∗ Exp(a+b)` of the independent sum `X_a + X_b + X_{a+b}` `(RGE.7)`.  Convolving
a law carried by `[0, ∞)` with distribution function `F` against `Exp(r)` produces the distribution
function `K` solving `K' = r(F - K)`, `K(0) = 0`; three such steps give `H`.  Consequently
`0 ≤ H ≤ 1`, `H` is nondecreasing with `H' ≥ 0`, and `H → 1` `(RGE.8)`.

The distribution function of a convolution is monotone in each factor's distribution function, and
`Exp(r)` increases stochastically as `r` decreases.  Hence for `a, b ≥ λ > 0` the response
dominates the Erlang-three distribution function `G_λ(t) = 1 - e^{-λt}(1 + λt + (λt)²/2)`
`(RGE.9)`–`(RGE.10)`; in particular `H_{a,b}(t) > 0` for `t > 0`, and the ordered defect `ab ω_t(a,b)` has the sign of
`a - b`.  At `λ₀ = log 2` the floor `c_T² = ∫₀ᵀ G_{λ₀}²` satisfies `0 < c_T² < T` `(RGE.11)`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

/-! ### Distribution functions of convolutions on the half-line -/

/-- `(μ ∗ ν)(-∞, t] = ∫ ν(-∞, t - x] dμ(x)`. -/
theorem conv_Iic (μ ν : Measure ℝ) [SFinite ν] (t : ℝ) :
    (μ ∗ ν) (Iic t) = ∫⁻ x, ν (Iic (t - x)) ∂μ := by
  rw [← lintegral_indicator_one measurableSet_Iic,
    Measure.lintegral_conv (measurable_one.indicator measurableSet_Iic)]
  refine lintegral_congr fun x => ?_
  have : (fun y => (Iic t).indicator (1 : ℝ → ℝ≥0∞) (x + y)) = (Iic (t - x)).indicator 1 := by
    ext y
    simp only [indicator, mem_Iic, Pi.one_apply, le_sub_iff_add_le']
  rw [this, lintegral_indicator_one measurableSet_Iic]

/-- The distribution function of a convolution is monotone in the second factor's distribution
function. -/
theorem conv_Iic_mono_right (μ : Measure ℝ) {ν₁ ν₂ : Measure ℝ} [SFinite ν₁] [SFinite ν₂]
    (h : ∀ s, ν₁ (Iic s) ≤ ν₂ (Iic s)) (t : ℝ) : (μ ∗ ν₁) (Iic t) ≤ (μ ∗ ν₂) (Iic t) := by
  rw [conv_Iic, conv_Iic]
  exact lintegral_mono fun x => h _

/-- The distribution function of a convolution is monotone in the first factor's distribution
function. -/
theorem conv_Iic_mono_left {μ₁ μ₂ : Measure ℝ} (ν : Measure ℝ) [SFinite μ₁] [SFinite μ₂]
    [SFinite ν] (h : ∀ s, μ₁ (Iic s) ≤ μ₂ (Iic s)) (t : ℝ) :
    (μ₁ ∗ ν) (Iic t) ≤ (μ₂ ∗ ν) (Iic t) := by
  rw [Measure.conv_comm μ₁, Measure.conv_comm μ₂]
  exact conv_Iic_mono_right ν h t

/-- A measure on `ℝ` carried by `[0, ∞)` whose distribution function there is the continuous
nonnegative function `F`. -/
structure HasHalfLineCDF (ν : Measure ℝ) (F : ℝ → ℝ) : Prop where
  continuous : Continuous F
  nonneg : ∀ s, 0 ≤ s → 0 ≤ F s
  Iic_eq : ∀ s, 0 ≤ s → ν (Iic s) = ENNReal.ofReal (F s)
  Iic_neg : ∀ s, s < 0 → ν (Iic s) = 0

/-- `Exp(r)` has distribution function `1 - e^{-rs}` on `[0, ∞)`. -/
theorem hasHalfLineCDF_expMeasure {r : ℝ} (hr : 0 < r) :
    HasHalfLineCDF (expMeasure r) fun s => 1 - Real.exp (-(r * s)) := by
  haveI := isProbabilityMeasure_expMeasure hr
  refine ⟨by fun_prop, fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
  · have : Real.exp (-(r * s)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  · rw [← ofReal_cdf, cdf_expMeasure_eq hr, if_pos hs]
  · rw [← ofReal_cdf, cdf_expMeasure_eq hr, if_neg (not_le.mpr hs), ENNReal.ofReal_zero]

/-- `Exp(r)` increases stochastically as the rate decreases. -/
theorem expMeasure_Iic_mono {r r' : ℝ} (hr : 0 < r) (hrr : r ≤ r') (s : ℝ) :
    expMeasure r (Iic s) ≤ expMeasure r' (Iic s) := by
  rcases lt_or_ge s 0 with hs | hs
  · rw [(hasHalfLineCDF_expMeasure hr).Iic_neg s hs]
    exact bot_le
  · rw [(hasHalfLineCDF_expMeasure hr).Iic_eq s hs,
      (hasHalfLineCDF_expMeasure (hr.trans_le hrr)).Iic_eq s hs]
    refine ENNReal.ofReal_le_ofReal (sub_le_sub_left (Real.exp_le_exp.mpr ?_) 1)
    nlinarith

/-- Variation of constants: if `K(0) = 0` and `(e^{rs} K(s))' = r e^{rs} F(s)`, then
`∫₀ᵗ r e^{-r(t-s)} F(s) ds = K(t)`. -/
theorem integral_exp_kernel_eq {r : ℝ} {F K : ℝ → ℝ} (hF : Continuous F) (hK0 : K 0 = 0)
    (hd : ∀ s, HasDerivAt (fun s => Real.exp (r * s) * K s) (r * Real.exp (r * s) * F s) s)
    (t : ℝ) : ∫ s in (0 : ℝ)..t, r * Real.exp (-(r * (t - s))) * F s = K t := by
  have h1 : ∀ s, r * Real.exp (-(r * (t - s))) * F s =
      Real.exp (-(r * t)) * (r * Real.exp (r * s) * F s) := fun s => by
    rw [show -(r * (t - s)) = -(r * t) + r * s by ring, Real.exp_add]
    ring
  simp_rw [h1]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      (by apply Continuous.intervalIntegrable; fun_prop), hK0, mul_zero, sub_zero,
    ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- Convolution with `Exp(r)` solves `K' = r(F - K)`, `K(0) = 0`: if `ν` has distribution function
`F` on `[0, ∞)` and `(e^{rs} K(s))' = r e^{rs} F(s)`, then `Exp(r) ∗ ν` has distribution function
`K`. -/
theorem HasHalfLineCDF.expConv {r : ℝ} (hr : 0 < r) {ν : Measure ℝ} [SFinite ν] {F K : ℝ → ℝ}
    (hν : HasHalfLineCDF ν F) (hK : Continuous K) (hK0 : K 0 = 0)
    (hd : ∀ s, HasDerivAt (fun s => Real.exp (r * s) * K s) (r * Real.exp (r * s) * F s) s) :
    HasHalfLineCDF (expMeasure r ∗ ν) K := by
  have hpdf : Measurable (exponentialPDF r) := (measurable_exponentialPDFReal r).ennreal_ofReal
  have hanti : ∀ t, Measurable fun x => ν (Iic (t - x)) := fun t =>
    Antitone.measurable fun x y hxy => measure_mono (Iic_subset_Iic.mpr (by linarith))
  have hconv : ∀ t, (expMeasure r ∗ ν) (Iic t) = ∫⁻ x, exponentialPDF r x * ν (Iic (t - x)) :=
    fun t => by
      rw [conv_Iic]
      exact lintegral_withDensity_eq_lintegral_mul _ hpdf (hanti t)
  have hKint : ∀ t, K t = ∫ s in (0 : ℝ)..t, r * Real.exp (-(r * (t - s))) * F s :=
    fun t => (integral_exp_kernel_eq hν.continuous hK0 hd t).symm
  have hFc := hν.continuous
  refine ⟨hK, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · rw [hKint t]
    exact intervalIntegral.integral_nonneg ht fun s hs =>
      mul_nonneg (by positivity) (hν.nonneg s hs.1)
  · rw [hconv]
    have hpt : ∀ x, exponentialPDF r x * ν (Iic (t - x)) = (Icc 0 t).indicator
        (fun x => ENNReal.ofReal (r * Real.exp (-(r * x)) * F (t - x))) x := fun x => by
      by_cases hx0 : 0 ≤ x
      · by_cases hxt : x ≤ t
        · rw [indicator_of_mem (show x ∈ Icc 0 t from ⟨hx0, hxt⟩), exponentialPDF_of_nonneg hx0,
            hν.Iic_eq _ (by linarith), ← ENNReal.ofReal_mul (by positivity)]
        · rw [indicator_of_notMem (fun h => hxt h.2), hν.Iic_neg _ (by linarith), mul_zero]
      · rw [indicator_of_notMem (fun h => hx0 h.1), exponentialPDF_of_neg (not_le.mp hx0),
          zero_mul]
    simp_rw [hpt]
    rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
    · congr 1
      rw [hKint t]
      have := intervalIntegral.integral_comp_sub_left
        (fun s => r * Real.exp (-(r * (t - s))) * F s) t (a := 0) (b := t)
      simp only [sub_sub_cancel, sub_self, sub_zero] at this
      exact this
    · exact (by fun_prop : Continuous fun x => r * Real.exp (-(r * x)) * F (t - x)).integrableOn_Icc
    · exact ae_restrict_of_forall_mem measurableSet_Icc fun x hx =>
        mul_nonneg (by positivity) (hν.nonneg _ (by linarith [hx.2]))
  · rw [hconv]
    have : ∀ x, exponentialPDF r x * ν (Iic (t - x)) = 0 := fun x => by
      by_cases hx0 : 0 ≤ x
      · rw [hν.Iic_neg _ (by linarith), mul_zero]
      · rw [exponentialPDF_of_neg (not_le.mp hx0), zero_mul]
    simp_rw [this, lintegral_zero]

theorem hasDerivAt_exp_mul (k s : ℝ) :
    HasDerivAt (fun s => Real.exp (k * s)) (k * Real.exp (k * s)) s := by
  have := ((hasDerivAt_id' s).const_mul k).exp
  refine this.congr_deriv ?_
  ring

/-! ### The hypoexponential law of the Green-exactified response `(RGE.7)` -/

/-- The distribution function of `X_b + X_c` for independent exponentials of rates `b ≠ c`. -/
def twoExpCDF (b c s : ℝ) : ℝ :=
  1 - (c * Real.exp (-(b * s)) - b * Real.exp (-(c * s))) / (c - b)

theorem hasHalfLineCDF_twoExp {b c : ℝ} (hb : 0 < b) (hbc : b < c) :
    HasHalfLineCDF (expMeasure b ∗ expMeasure c) (twoExpCDF b c) := by
  haveI := isProbabilityMeasure_expMeasure (hb.trans hbc)
  have hcb : c - b ≠ 0 := by linarith
  refine (hasHalfLineCDF_expMeasure (hb.trans hbc)).expConv hb (by unfold twoExpCDF; fun_prop)
    (by simp [twoExpCDF, hcb]) fun s => ?_
  have hfun : (fun s => Real.exp (b * s) * twoExpCDF b c s) =
      fun s => Real.exp (b * s) - c / (c - b) + b / (c - b) * Real.exp ((b - c) * s) := by
    funext s
    rw [twoExpCDF, show (b - c) * s = b * s + -(c * s) by ring, Real.exp_add,
      show -(b * s) = -(b * s) by rfl, Real.exp_neg (b * s)]
    field_simp
    ring
  rw [hfun]
  refine (((hasDerivAt_exp_mul b s).sub_const _).add
    ((hasDerivAt_exp_mul (b - c) s).const_mul _)).congr_deriv ?_
  rw [show (b - c) * s = b * s + -(c * s) by ring, Real.exp_add]
  field_simp
  ring

/-- The hypoexponential law `Exp(a) ∗ (Exp(b) ∗ Exp(a+b))` of `X_a + X_b + X_{a+b}`. -/
def hypoMeasure (a b : ℝ) : Measure ℝ := expMeasure a ∗ (expMeasure b ∗ expMeasure (a + b))

theorem isProbabilityMeasure_hypoMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsProbabilityMeasure (hypoMeasure a b) := by
  haveI := isProbabilityMeasure_expMeasure ha
  haveI := isProbabilityMeasure_expMeasure hb
  haveI := isProbabilityMeasure_expMeasure (add_pos ha hb)
  unfold hypoMeasure
  infer_instance

/-- **`(RGE.7)`**: `H_{a,b}` is the distribution function of `X_a + X_b + X_{a+b}`. -/
theorem hasHalfLineCDF_hypoMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasHalfLineCDF (hypoMeasure a b) (greenExact a b) := by
  haveI := isProbabilityMeasure_expMeasure hb
  haveI := isProbabilityMeasure_expMeasure (add_pos ha hb)
  have h2 := hasHalfLineCDF_twoExp hb (by linarith : b < a + b)
  refine h2.expConv ha (continuous_greenExact a b) (by simp [greenExact]) fun s => ?_
  have hab0 : a + b - b = a := by ring
  by_cases hab : a = b
  · subst hab
    have hfun : (fun s => Real.exp (a * s) * greenExact a a s) =
        fun s => Real.exp (a * s) - Real.exp (-1 * (a * s)) - 2 * a * s := by
      funext s
      rw [greenExact_self, show -(2 * a) * s = -(a * s) + -(a * s) by ring,
        show -a * s = -(a * s) by ring, show -1 * (a * s) = -(a * s) by ring, Real.exp_add,
        Real.exp_neg]
      field_simp
    rw [hfun]
    refine (((hasDerivAt_exp_mul a s).sub
      ((hasDerivAt_exp_mul (-1) (a * s)).comp s ((hasDerivAt_id s).const_mul a))).sub
        (((hasDerivAt_id s).const_mul (2 * a)))).congr_deriv ?_
    rw [twoExpCDF, hab0, show -((a + a) * s) = -(a * s) + -(a * s) by ring,
      show -1 * (a * s) = -(a * s) by ring, Real.exp_add, Real.exp_neg]
    have ha0 : a ≠ 0 := ha.ne'
    simp only [mul_one]
    field_simp
    ring
  · have hs : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hfun : (fun s => Real.exp (a * s) * greenExact a b s) =
        fun s => Real.exp (a * s) - Real.exp (-b * s) +
          (a + b) / (a - b) * (1 - Real.exp ((a - b) * s)) := by
      funext s
      rw [greenExact_of_ne hab, show -(a + b) * s = -(a * s) + -b * s by ring,
        show (a - b) * s = a * s + -b * s by ring, show -a * s = -(a * s) by ring,
        Real.exp_add, Real.exp_add, Real.exp_neg (a * s)]
      field_simp
    rw [hfun]
    refine (((hasDerivAt_exp_mul a s).sub (hasDerivAt_exp_mul (-b) s)).add
      (((hasDerivAt_exp_mul (a - b) s).const_sub 1).const_mul _)).congr_deriv ?_
    rw [twoExpCDF, hab0, show -((a + b) * s) = -(a * s) + -b * s by ring,
      show (a - b) * s = a * s + -b * s by ring, show -(b * s) = -b * s by ring,
      Real.exp_add, Real.exp_add, Real.exp_neg (a * s)]
    have ha0 : a ≠ 0 := ha.ne'
    field_simp
    ring

/-- The distribution function of the hypoexponential law is `H_{a,b}` on `[0, ∞)`. -/
theorem cdf_hypoMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 ≤ t) :
    cdf (hypoMeasure a b) t = greenExact a b t := by
  haveI := isProbabilityMeasure_hypoMeasure ha hb
  have h := (hasHalfLineCDF_hypoMeasure ha hb).Iic_eq t ht
  rw [← ofReal_cdf] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (cdf_nonneg _ _)
    ((hasHalfLineCDF_hypoMeasure ha hb).nonneg t ht)).mp h

/-! ### Distribution-function laws `(RGE.8)` -/

theorem greenExact_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ greenExact a b t :=
  (hasHalfLineCDF_hypoMeasure ha hb).nonneg t ht

theorem greenExact_le_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 ≤ t) :
    greenExact a b t ≤ 1 := by
  rw [← cdf_hypoMeasure ha hb ht]
  exact cdf_le_one _ _

theorem monotoneOn_greenExact {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    MonotoneOn (greenExact a b) (Ici 0) := fun s hs t ht hst => by
  rw [← cdf_hypoMeasure ha hb hs, ← cdf_hypoMeasure ha hb ht]
  exact monotone_cdf _ hst

theorem deriv_greenExact_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 < t) :
    0 ≤ deriv (greenExact a b) t := by
  have h : (cdf (hypoMeasure a b) : ℝ → ℝ) =ᶠ[𝓝 t] greenExact a b := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact cdf_hypoMeasure ha hb (le_of_lt hs)
  rw [← h.deriv_eq]
  exact (monotone_cdf _).deriv_nonneg

theorem tendsto_greenExact_atTop {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (greenExact a b) atTop (𝓝 1) := by
  haveI := isProbabilityMeasure_hypoMeasure ha hb
  refine (tendsto_cdf_atTop (hypoMeasure a b)).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact cdf_hypoMeasure ha hb ht

/-! ### The Erlang-three envelope `(RGE.9)`–`(RGE.10)` -/

/-- The distribution function `1 - e^{-λs}(1 + λs)` of the Erlang-two law of rate `λ`. -/
def erlangTwoCDF (l s : ℝ) : ℝ := 1 - Real.exp (-(l * s)) * (1 + l * s)

/-- The distribution function `G_λ(s) = 1 - e^{-λs}(1 + λs + (λs)²/2)` of the Erlang-three law
`(RGE.9)`. -/
def erlangThreeCDF (l s : ℝ) : ℝ := 1 - Real.exp (-(l * s)) * (1 + l * s + (l * s) ^ 2 / 2)

theorem hasDerivAt_erlangTwo (l s : ℝ) :
    HasDerivAt (fun s => Real.exp (l * s) * erlangTwoCDF l s)
      (l * Real.exp (l * s) * (1 - Real.exp (-(l * s)))) s := by
  have hfun : (fun s => Real.exp (l * s) * erlangTwoCDF l s) =
      fun s => Real.exp (l * s) - 1 - l * s := by
    funext s
    rw [erlangTwoCDF, Real.exp_neg]
    field_simp
    ring
  rw [hfun]
  refine (((hasDerivAt_exp_mul l s).sub_const 1).sub ((hasDerivAt_id s).const_mul l)).congr_deriv ?_
  rw [Real.exp_neg]
  simp only [mul_one]
  field_simp

theorem hasDerivAt_erlangThree (l s : ℝ) :
    HasDerivAt (fun s => Real.exp (l * s) * erlangThreeCDF l s)
      (l * Real.exp (l * s) * erlangTwoCDF l s) s := by
  have hfun : (fun s => Real.exp (l * s) * erlangThreeCDF l s) =
      fun s => Real.exp (l * s) - (1 + l * s + l ^ 2 / 2 * s ^ 2) := by
    funext s
    rw [erlangThreeCDF, Real.exp_neg]
    field_simp
  rw [hfun]
  refine ((hasDerivAt_exp_mul l s).sub ((((hasDerivAt_id s).const_mul l).const_add 1).add
    ((hasDerivAt_pow 2 s).const_mul (l ^ 2 / 2)))).congr_deriv ?_
  rw [erlangTwoCDF, Real.exp_neg]
  simp only [mul_one]
  field_simp
  ring

/-- The Erlang-three law `Exp(λ) ∗ (Exp(λ) ∗ Exp(λ))`. -/
def erlangThreeMeasure (l : ℝ) : Measure ℝ := expMeasure l ∗ (expMeasure l ∗ expMeasure l)

theorem hasHalfLineCDF_erlangTwo {l : ℝ} (hl : 0 < l) :
    HasHalfLineCDF (expMeasure l ∗ expMeasure l) (erlangTwoCDF l) := by
  haveI := isProbabilityMeasure_expMeasure hl
  exact (hasHalfLineCDF_expMeasure hl).expConv hl (by unfold erlangTwoCDF; fun_prop)
    (by simp [erlangTwoCDF]) (hasDerivAt_erlangTwo l)

theorem hasHalfLineCDF_erlangThree {l : ℝ} (hl : 0 < l) :
    HasHalfLineCDF (erlangThreeMeasure l) (erlangThreeCDF l) := by
  haveI := isProbabilityMeasure_expMeasure hl
  exact (hasHalfLineCDF_erlangTwo hl).expConv hl (by unfold erlangThreeCDF; fun_prop)
    (by simp [erlangThreeCDF]) (hasDerivAt_erlangThree l)

theorem erlangTwoCDF_pos {l s : ℝ} (hl : 0 < l) (hs : 0 < s) : 0 < erlangTwoCDF l s := by
  have h := Real.add_one_lt_exp (by positivity : l * s ≠ 0)
  have he := Real.exp_pos (l * s)
  rw [erlangTwoCDF, Real.exp_neg, sub_pos, inv_mul_lt_one₀ he]
  linarith

/-- `G_λ(t) > 0` for `t > 0`. -/
theorem erlangThreeCDF_pos {l t : ℝ} (hl : 0 < l) (ht : 0 < t) : 0 < erlangThreeCDF l t := by
  rw [← integral_exp_kernel_eq (by unfold erlangTwoCDF; fun_prop) (by simp [erlangThreeCDF])
    (hasDerivAt_erlangThree l) t]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (Continuous.intervalIntegrable (by unfold erlangTwoCDF; fun_prop) _ _) (fun s hs => ?_) ht
  exact mul_pos (by positivity) (erlangTwoCDF_pos hl hs.1)

theorem erlangThreeCDF_lt_one (l t : ℝ) : erlangThreeCDF l t < 1 := by
  rw [erlangThreeCDF, sub_lt_self_iff]
  exact mul_pos (Real.exp_pos _) (by nlinarith [sq_nonneg (l * t + 1)])

/-- **`(RGE.10)`: stochastic lower envelope.**  For `a, b ≥ λ > 0`, `X_a + X_b + X_{a+b}` is
stochastically smaller than the Erlang-three variable of rate `λ`, so `H_{a,b} ≥ G_λ` on
`[0, ∞)`. -/
theorem erlangThreeCDF_le_greenExact {l a b : ℝ} (hl : 0 < l) (hla : l ≤ a) (hlb : l ≤ b)
    {t : ℝ} (ht : 0 ≤ t) : erlangThreeCDF l t ≤ greenExact a b t := by
  have ha := hl.trans_le hla
  have hb := hl.trans_le hlb
  haveI := isProbabilityMeasure_expMeasure hl
  haveI := isProbabilityMeasure_expMeasure ha
  haveI := isProbabilityMeasure_expMeasure hb
  haveI := isProbabilityMeasure_expMeasure (add_pos ha hb)
  have hle : erlangThreeMeasure l (Iic t) ≤ hypoMeasure a b (Iic t) :=
    calc erlangThreeMeasure l (Iic t)
        ≤ (expMeasure a ∗ (expMeasure l ∗ expMeasure l)) (Iic t) :=
          conv_Iic_mono_left _ (expMeasure_Iic_mono hl hla) t
      _ ≤ (expMeasure a ∗ (expMeasure b ∗ expMeasure l)) (Iic t) :=
          conv_Iic_mono_right _ (conv_Iic_mono_left _ (expMeasure_Iic_mono hl hlb)) t
      _ ≤ hypoMeasure a b (Iic t) :=
          conv_Iic_mono_right _ (conv_Iic_mono_right _
            (expMeasure_Iic_mono hl (by linarith))) t
  rw [(hasHalfLineCDF_erlangThree hl).Iic_eq t ht, (hasHalfLineCDF_hypoMeasure ha hb).Iic_eq t ht,
    ENNReal.ofReal_le_ofReal_iff (greenExact_nonneg ha hb ht)] at hle
  exact hle

/-- `H_{a,b}(t) > 0` for `t > 0`. -/
theorem greenExact_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 < t) :
    0 < greenExact a b t :=
  (erlangThreeCDF_pos (lt_min ha hb) ht).trans_le
    (erlangThreeCDF_le_greenExact (lt_min ha hb) (min_le_left _ _) (min_le_right _ _) ht.le)

/-- For `t > 0` the ordered defect `ab ω_t(a,b)` has the sign of the relative grade `a - b`: the
orientation is carried by `Δ₋` and the magnitude by the positive formation law `H`. -/
theorem sign_defect {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 < t) :
    SignType.sign (a * b * defectKernel t a b) = SignType.sign (a - b) := by
  have hp : 0 < a + b := add_pos ha hb
  have h : a * b * defectKernel t a b = (a - b) * (greenExact a b t / (a + b)) := by
    rw [mul_div_assoc', eq_div_iff hp.ne', ← conservation ha hb t]
    ring
  rw [h, sign_mul, sign_pos (div_pos (greenExact_pos ha hb ht) hp), mul_one]

/-! ### The pair floor `(RGE.11)` -/

/-- The pair floor `c_T² = ∫₀ᵀ G_{log 2}(t)² dt`. -/
def pairFloor (T : ℝ) : ℝ := ∫ t in (0 : ℝ)..T, erlangThreeCDF (Real.log 2) t ^ 2

theorem pairFloor_pos {T : ℝ} (hT : 0 < T) : 0 < pairFloor T := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (Continuous.intervalIntegrable (by unfold erlangThreeCDF; fun_prop) _ _)
    (fun t ht => pow_pos (erlangThreeCDF_pos hl ht.1) 2) hT

theorem pairFloor_lt {T : ℝ} (hT : 0 < T) : pairFloor T < T := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc : Continuous fun t => erlangThreeCDF (Real.log 2) t ^ 2 := by
    unfold erlangThreeCDF; fun_prop
  have h0 : ∀ t, 0 ≤ t → 0 ≤ erlangThreeCDF (Real.log 2) t := fun t ht =>
    (hasHalfLineCDF_erlangThree hl).nonneg t ht
  have hsq : ∀ t, 0 ≤ t → erlangThreeCDF (Real.log 2) t ^ 2 < 1 := fun t ht => by
    have := erlangThreeCDF_lt_one (Real.log 2) t
    nlinarith [h0 t ht]
  calc pairFloor T < ∫ _ in (0 : ℝ)..T, (1 : ℝ) :=
        intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hT
          hc.continuousOn continuousOn_const (fun t ht => (hsq t ht.1.le).le)
          ⟨T, ⟨hT.le, le_rfl⟩, hsq T hT.le⟩
    _ = T := by simp

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
