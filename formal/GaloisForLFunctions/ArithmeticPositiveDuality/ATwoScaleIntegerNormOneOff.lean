import GaloisForLFunctions.ArithmeticPositiveDuality.AnIntegerNormOneOffCrossesTheCriticalLine
import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheLinearAbscissaLawAndItsHierarchy

/-!
# Wave Euler products with integer norms across the critical line

`AnIntegerNormOneOffCrossesTheCriticalLine` plants a single off-line conjugate pair `β ± i γ` in a
convergent Euler product `∏_k (1 - q_k^{-s})^{-1} = ∑_n a_n n^{-s}` with natural norms `q_k ≥ 2`,
natural coefficients `a_n`, linear counting `∑_{n<N} a_n ∼ A N`, and zero-free continuation across
`Re s = 1/2`. Because that witness has only finitely many off-line zeros (`Θ_∞ = 1/2`), it satisfies
`ExtremeDeuringHeilbronn` (`¬AAL → FiniteOffLine`) while violating `LinearAbscissaLaw`.

Here we construct, for **every** wave datum (`WaveSpec`: a top pair `β ± i γ`, `β < 2/3`, `γ > 0`,
and remainder real parts `½ < θ_n ≤ θ₂ < β`), a convergent integer-norm Euler product with linear
counting and critical-line continuation whose zeros on `{Re s > 1/3, s ≠ 1}` consist of the top pair
together with the higher-ordinate conjugate pairs `θ_n ± i ω_n` (`ω_n > γ`, `ω_n → ∞`); its
asymptotic abscissa is `lim θ_n` whenever the limit exists
(`zeroConfig_asymptoticAbscissa_of_tendsto`):

* **Entire cutoff-Frullani factors** (`differentiable_frullaniCutoffFactor`,
  `norm_frullaniCutoffLog_le_of_im_ne_zero`). Splitting Frullani's integral at `A > 0` defines an
  entire factor `F_A(z) = z exp(-J_A(z) - C_A)` with sole zero `z = 0`, equal on `Re z > 0` to
  `exp(-∫_{A}^∞ e^{-z t}/t dt)` and satisfying `‖Φ_A(z)‖ ≤ e^{-A Re z} / (A |Im z|)` off the real
  axis.
* **Continuous high-ordinate density perturbation** (`continuous_wRem`, `abs_wRem_le`,
  `differentiableOn_remFactor`). Choosing `ω_n = (π/2 + 2π M_n)/A_n` makes `cos(ω_n A_n) = 0`, so
  each cutoff wave `-2 e^{θ_n t} cos(ω_n t)/t · 1_{[A_n, ∞)}(t)` is continuous on `ℝ`, bounded in
  total sum by `(1/4) w₀(t)`, and exponentiates to a factor `remFactor` holomorphic on `Re s > 0`
  whose exact zero set there is `{θ_n ± i ω_n : n ∈ ℕ}`.
* **Wave Euler product and strip `ZeroConfig`** (`WaveSpec.exists_integer_norm_euler_product`).
  Prime-square quantile discretization and upward integer rounding preserve continuation to
  `{Re s > 1/3, s ≠ 1}`, Wiener–Ikehara linear counting, and nonvanishing on `Re s = 1/2`.
* **Two-scale instance** (`exists_two_scale_integer_norm_euler_product`,
  `twoScaleZeroConfig_properties`). `θ_0 = θ₂`, `θ_{n+1} = θ` realizes
  `(Θ, Θ₂, Θ_∞) = (β, θ₂, θ)`. In particular `θ = θ₂` attains `Θ_∞ = Θ₂`, refuting extreme,
  asymptotic, and sub-`Θ₂` graded Deuring–Heilbronn on positive integer-norm Euler products.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Complex
open scoped BigOperators
open GaloisForLFunctions.HTGeometry
open Zeta23 hiding Params
open RHTower.BeurlingOverRegularIntegers
open GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff
open GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa

namespace GaloisForLFunctions.ArithmeticPositiveDuality.TwoScaleIntegerNormOneOff

noncomputable section

/-! ### Cutoff-Frullani entire factors and horizontal-ray decay -/

/-- Truncated Frullani integral `J_A(z) = ∫_0^A (e^{-t} - e^{-z t}) / t dt`. -/
def frullaniHead (A : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..A, (cexp (-t) - cexp (-(z * t))) / t

/-- Real exponential-integral tail constant `C_A = ∫_A^∞ e^{-t} / t dt`. -/
def frullaniTailConst (A : ℝ) : ℝ :=
  ∫ t in Ioi A, Real.exp (-t) / t

/-- Entire cutoff-Frullani factor `F_A(z) = z exp(-J_A(z) - C_A)`, vanishing iff `z = 0`. -/
def frullaniCutoffFactor (A : ℝ) (z : ℂ) : ℂ :=
  z * cexp (-frullaniHead A z - (frullaniTailConst A : ℂ))

/-- Logarithmic exponent `Φ_A(z) = Log z - J_A(z) - C_A` on the slit plane. -/
def frullaniCutoffLog (A : ℝ) (z : ℂ) : ℂ :=
  Complex.log z - frullaniHead A z - (frullaniTailConst A : ℂ)

private theorem norm_frullaniIntegrand_le {A : ℝ} (_ : 0 < A) (z : ℂ) {t : ℝ}
    (ht0 : 0 < t) (htA : t ≤ A) :
    ‖(cexp (-t) - cexp (-(z * t))) / t‖ ≤ ‖z - 1‖ * Real.exp ((1 + ‖z‖) * A) := by
  rw [show (cexp (-t) - cexp (-(z * t))) / t = (cexp (-((1 : ℂ) * t)) - cexp (-(z * t))) / t by
    simp, ← intervalIntegral_seg_cexp (1 : ℂ) z ht0]
  have hpt : ∀ u ∈ uIoc (0 : ℝ) 1,
      ‖(z - 1) * cexp (-(seg 1 z u * t))‖ ≤ ‖z - 1‖ * Real.exp ((1 + ‖z‖) * A) := by
    intro u hu
    rw [uIoc_of_le zero_le_one] at hu
    rw [norm_mul, norm_cexp_neg_mul_ofReal]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have hre : -(seg 1 z u).re ≤ 1 + ‖z‖ := by
      rw [seg_re]
      simp only [Complex.one_re]
      have hzre : -z.re ≤ ‖z‖ := (neg_le_abs z.re).trans (Complex.abs_re_le_norm z)
      have hu0 : 0 ≤ u := hu.1.le
      have hu1 : u ≤ 1 := hu.2
      nlinarith [norm_nonneg z]
    calc -((seg 1 z u).re * t) = (-(seg 1 z u).re) * t := by ring
      _ ≤ (1 + ‖z‖) * t := mul_le_mul_of_nonneg_right hre ht0.le
      _ ≤ (1 + ‖z‖) * A := mul_le_mul_of_nonneg_left htA (by positivity)
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hpt

private theorem aestronglyMeasurable_frullaniIntegrand {A : ℝ} (hA : 0 < A) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => (cexp (-t) - cexp (-(z * t))) / t)
      (volume.restrict (uIoc 0 A)) := by
  rw [uIoc_of_le hA.le]
  refine (ContinuousOn.div (by fun_prop) Complex.continuous_ofReal.continuousOn ?_)
    |>.aestronglyMeasurable measurableSet_Ioc
  intro t ht
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt ht.1)

private theorem intervalIntegrable_frullaniIntegrand {A : ℝ} (hA : 0 < A) (z : ℂ) :
    IntervalIntegrable (fun t : ℝ => (cexp (-t) - cexp (-(z * t))) / t) volume 0 A := by
  refine intervalIntegrable_const (c := ‖z - 1‖ * Real.exp ((1 + ‖z‖) * A)).mono_fun'
    (aestronglyMeasurable_frullaniIntegrand hA z) ?_
  rw [uIoc_of_le hA.le]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact norm_frullaniIntegrand_le hA z ht.1 ht.2

/-- `frullaniHead A` is entire on `ℂ` with complex derivative `∫_0^A e^{-z t} dt`. -/
theorem hasDerivAt_frullaniHead {A : ℝ} (hA : 0 < A) (z₀ : ℂ) :
    HasDerivAt (frullaniHead A) (∫ t in (0 : ℝ)..A, cexp (-(z₀ * t))) z₀ := by
  let F : ℂ → ℝ → ℂ := fun z t => (cexp (-t) - cexp (-(z * t))) / t
  let F' : ℂ → ℝ → ℂ := fun z t => cexp (-(z * t))
  let B : ℝ := Real.exp ((‖z₀‖ + 1) * A)
  have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) (volume.restrict (uIoc 0 A)) :=
    Eventually.of_forall (aestronglyMeasurable_frullaniIntegrand hA)
  have hF'_meas : AEStronglyMeasurable (F' z₀) (volume.restrict (uIoc 0 A)) :=
    (continuous_cexp_neg_mul z₀).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂volume, t ∈ uIoc 0 A → ∀ z ∈ Metric.ball z₀ 1, ‖F' z t‖ ≤ B := by
    refine Eventually.of_forall fun t ht z hz => ?_
    rw [uIoc_of_le hA.le] at ht
    dsimp only [F', B]
    rw [norm_cexp_neg_mul_ofReal]
    apply Real.exp_le_exp.mpr
    have hzn : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have hd : ‖z - z₀‖ < 1 := by simpa only [dist_eq_norm] using Metric.mem_ball.mp hz
      have htri := norm_add_le (z - z₀) z₀
      rw [sub_add_cancel] at htri
      linarith
    have hzre : -z.re ≤ ‖z₀‖ + 1 :=
      ((neg_le_abs z.re).trans (Complex.abs_re_le_norm z)).trans hzn
    calc -(z.re * t) = (-z.re) * t := by ring
      _ ≤ (‖z₀‖ + 1) * t := mul_le_mul_of_nonneg_right hzre ht.1.le
      _ ≤ (‖z₀‖ + 1) * A := mul_le_mul_of_nonneg_left ht.2 (by positivity)
  have hderiv : ∀ᵐ t ∂volume, t ∈ uIoc 0 A → ∀ z ∈ Metric.ball z₀ 1,
      HasDerivAt (fun w => F w t) (F' z t) z := by
    refine Eventually.of_forall fun t ht z _ => ?_
    rw [uIoc_of_le hA.le] at ht
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht.1)
    have hlin : HasDerivAt (fun w : ℂ => -(w * (t : ℂ))) (-(1 * (t : ℂ))) z :=
      ((hasDerivAt_id z).mul_const (t : ℂ)).neg
    have hsub : HasDerivAt (fun w : ℂ => cexp (-t) - cexp (-(w * t)))
        (0 - cexp (-(z * t)) * (-(1 * (t : ℂ)))) z :=
      (hasDerivAt_const z (cexp (-t))).sub hlin.cexp
    refine (hsub.div_const (t : ℂ)).congr_deriv ?_
    dsimp only [F']
    field_simp
    ring
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ one_pos) hF_meas (intervalIntegrable_frullaniIntegrand hA z₀)
    hF'_meas hbound intervalIntegrable_const hderiv).2

theorem differentiable_frullaniHead {A : ℝ} (hA : 0 < A) :
    Differentiable ℂ (frullaniHead A) :=
  fun z => (hasDerivAt_frullaniHead hA z).differentiableAt

theorem differentiable_frullaniCutoffFactor {A : ℝ} (hA : 0 < A) :
    Differentiable ℂ (frullaniCutoffFactor A) := by
  intro z
  unfold frullaniCutoffFactor
  exact differentiableAt_id.mul
    (((differentiable_frullaniHead hA z).neg.sub_const _).cexp)

theorem frullaniCutoffFactor_eq_zero_iff (A : ℝ) (z : ℂ) :
    frullaniCutoffFactor A z = 0 ↔ z = 0 := by
  rw [frullaniCutoffFactor, mul_eq_zero, or_iff_left (Complex.exp_ne_zero _)]

theorem frullaniCutoffFactor_eq_cexp_of_ne_zero (A : ℝ) {z : ℂ} (hz : z ≠ 0) :
    frullaniCutoffFactor A z = cexp (frullaniCutoffLog A z) := by
  rw [frullaniCutoffLog, sub_sub, Complex.exp_sub, Complex.exp_log hz,
    frullaniCutoffFactor, div_eq_mul_inv, ← Complex.exp_neg]
  congr 2
  ring

private theorem intervalIntegral_cexp_neg_mul {A : ℝ} {z : ℂ} (hz : z ≠ 0) :
    ∫ t in (0 : ℝ)..A, cexp (-(z * t)) = (1 - cexp (-(z * A))) / z := by
  have hprim : ∀ t ∈ uIcc (0 : ℝ) A,
      HasDerivAt (fun r : ℝ => -(cexp (-(z * r)) / z)) (cexp (-(z * t))) t := by
    intro t _
    refine (((hasDerivAt_cexp_neg_mul z t).div_const z).neg).congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun t : ℝ => cexp (-(z * t))) volume 0 A :=
    (continuous_cexp_neg_mul z).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hprim hint]
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero]
  ring

theorem hasDerivAt_frullaniCutoffLog {A : ℝ} (hA : 0 < A) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (frullaniCutoffLog A) (cexp (-(z * A)) / z) z := by
  have hzne : z ≠ 0 := Complex.slitPlane_ne_zero hz
  have hlog : HasDerivAt Complex.log z⁻¹ z := Complex.hasDerivAt_log hz
  have hhead : HasDerivAt (frullaniHead A) ((1 - cexp (-(z * A))) / z) z := by
    rw [← intervalIntegral_cexp_neg_mul hzne]
    exact hasDerivAt_frullaniHead hA z
  unfold frullaniCutoffLog
  refine ((hlog.sub hhead).sub_const _).congr_deriv ?_
  field_simp
  ring

private theorem integral_Ioi_exp_neg_mul {A σ : ℝ} (hσ : 0 < σ) :
    ∫ t in Ioi A, Real.exp (-(σ * t)) = Real.exp (-(σ * A)) / σ := by
  let f : ℝ → ℝ := fun t => -(Real.exp (-(σ * t)) / σ)
  have hcont : ContinuousWithinAt f (Ici A) A := by
    dsimp only [f]; fun_prop
  have hderiv : ∀ t ∈ Ioi A, HasDerivAt f (Real.exp (-(σ * t))) t := by
    intro t _
    have h1 : HasDerivAt (fun r : ℝ => -(σ * r)) (-(σ * 1)) t :=
      ((hasDerivAt_id t).const_mul σ).neg
    refine ((h1.exp.div_const σ).neg).congr_deriv ?_
    field_simp
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(σ * t))) (Ioi A) := by
    simpa only [neg_mul] using exp_neg_integrableOn_Ioi A hσ
  have htend : Tendsto f atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => -(σ * t)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hσ tendsto_id)
    simpa [f] using (Real.tendsto_exp_atBot.comp h1).div_const σ |>.neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend]
  dsimp only [f]
  ring

private theorem integrableOn_cexp_div_Ioi {A : ℝ} (hA : 0 < A) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => cexp (-(z * t)) / t) (Ioi A) := by
  have hdom : IntegrableOn (fun t : ℝ => A⁻¹ * Real.exp (-(z.re * t))) (Ioi A) := by
    have h : IntegrableOn (fun t : ℝ => Real.exp (-z.re * t)) (Ioi A) :=
      exp_neg_integrableOn_Ioi A hz
    have hc : IntegrableOn (fun t : ℝ => A⁻¹ * Real.exp (-z.re * t)) (Ioi A) := h.const_mul A⁻¹
    exact hc.congr_fun (fun _ _ => by dsimp only; rw [neg_mul]) measurableSet_Ioi
  have hmeas : AEStronglyMeasurable (fun t : ℝ => cexp (-(z * t)) / t)
      (volume.restrict (Ioi A)) := by
    refine (ContinuousOn.div (continuous_cexp_neg_mul z).continuousOn
      Complex.continuous_ofReal.continuousOn ?_).aestronglyMeasurable measurableSet_Ioi
    intro t ht
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (hA.trans ht))
  refine hdom.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := hA.trans ht
  rw [norm_div, norm_cexp_neg_mul_ofReal, Complex.norm_real, Real.norm_of_nonneg ht0.le,
    div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hA ht.le) (Real.exp_pos _).le

/-- On `0 < z.re`, `Φ_A(z) = -∫_{t > A} e^{-z t} / t dt` by Frullani's integral. -/
theorem frullaniCutoffLog_eq_neg_integral_of_re_pos {A : ℝ} (hA : 0 < A) {z : ℂ}
    (hz : 0 < z.re) :
    frullaniCutoffLog A z = -∫ t in Ioi A, cexp (-(z * t)) / t := by
  have hfr := integral_frullani (a := (1 : ℂ)) (b := z) (by norm_num) hz
  simp only [one_mul, Complex.log_one, sub_zero] at hfr
  have hfint := integrableOn_frullani (a := (1 : ℂ)) (b := z) (by norm_num) hz
  simp only [one_mul] at hfint
  have hunion : Ioc (0 : ℝ) A ∪ Ioi A = Ioi 0 := Ioc_union_Ioi_eq_Ioi hA.le
  have hsplit : ∫ t in Ioi (0 : ℝ), (cexp (-t) - cexp (-(z * t))) / t =
      (∫ t in Ioc 0 A, (cexp (-t) - cexp (-(z * t))) / t) +
        ∫ t in Ioi A, (cexp (-t) - cexp (-(z * t))) / t := by
    rw [← hunion] at hfint ⊢
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hfint.mono_set subset_union_left) (hfint.mono_set subset_union_right)
  have hhead_eq : frullaniHead A z = ∫ t in Ioc 0 A, (cexp (-t) - cexp (-(z * t))) / t := by
    rw [frullaniHead, intervalIntegral.integral_of_le hA.le]
  have hi1 := integrableOn_cexp_div_Ioi hA (z := (1 : ℂ)) (by norm_num)
  simp only [one_mul] at hi1
  have hi2 := integrableOn_cexp_div_Ioi hA hz
  have htail : ∫ t in Ioi A, (cexp (-t) - cexp (-(z * t))) / t =
      (frullaniTailConst A : ℂ) - ∫ t in Ioi A, cexp (-(z * t)) / t := by
    have hpt : (fun t : ℝ => (cexp (-t) - cexp (-(z * t))) / t) =
        fun t : ℝ => cexp (-t) / t - cexp (-(z * t)) / t := by
      funext t; ring
    rw [hpt, integral_sub hi1 hi2]
    congr 1
    rw [frullaniTailConst, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    push_cast; rfl
  rw [frullaniCutoffLog, ← hfr, hsplit, hhead_eq, htail]
  ring

theorem norm_frullaniCutoffLog_le_of_re_pos {A : ℝ} (hA : 0 < A) {z : ℂ} (hz : 0 < z.re) :
    ‖frullaniCutoffLog A z‖ ≤ Real.exp (-(z.re * A)) / (A * z.re) := by
  rw [frullaniCutoffLog_eq_neg_integral_of_re_pos hA hz, norm_neg]
  have hdom : IntegrableOn (fun t : ℝ => A⁻¹ * Real.exp (-(z.re * t))) (Ioi A) := by
    have h : IntegrableOn (fun t : ℝ => Real.exp (-z.re * t)) (Ioi A) :=
      exp_neg_integrableOn_Ioi A hz
    have hc : IntegrableOn (fun t : ℝ => A⁻¹ * Real.exp (-z.re * t)) (Ioi A) := h.const_mul A⁻¹
    exact hc.congr_fun (fun _ _ => by dsimp only; rw [neg_mul]) measurableSet_Ioi
  have hb : ‖∫ t in Ioi A, cexp (-(z * t)) / t‖ ≤
      ∫ t in Ioi A, A⁻¹ * Real.exp (-(z.re * t)) := by
    refine norm_integral_le_of_norm_le hdom ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hA.trans ht
    rw [norm_div, norm_cexp_neg_mul_ofReal, Complex.norm_real, Real.norm_of_nonneg ht0.le,
      div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hA ht.le) (Real.exp_pos _).le
  refine hb.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_Ioi_exp_neg_mul hz]
  field_simp

/-- **Off-axis horizontal-ray bound.** Whenever `z.im ≠ 0` and `0 < A`, integrating `Φ_A'(z + x)`
along `x ∈ (0, ∞)` yields `‖Φ_A(z)‖ ≤ e^{-A z.re} / (A |z.im|)` at any real part `z.re ∈ ℝ`. -/
theorem norm_frullaniCutoffLog_le_of_im_ne_zero {A : ℝ} (hA : 0 < A) {z : ℂ} (hz : z.im ≠ 0) :
    ‖frullaniCutoffLog A z‖ ≤ Real.exp (-(z.re * A)) / (A * |z.im|) := by
  have him_pos : 0 < |z.im| := abs_pos.mpr hz
  let f : ℝ → ℂ := fun x => frullaniCutoffLog A (z + x)
  let g : ℝ → ℂ := fun x => cexp (-((z + x) * A)) / (z + x)
  have hslit : ∀ x : ℝ, z + (x : ℂ) ∈ Complex.slitPlane := fun x =>
    Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using hz))
  have hf_deriv : ∀ x : ℝ, HasDerivAt f (g x) x := by
    intro x
    have hc : HasDerivAt (fun w : ℂ => frullaniCutoffLog A (z + w)) (g x) (x : ℂ) :=
      ((hasDerivAt_frullaniCutoffLog hA (hslit x)).comp (x : ℂ)
        ((hasDerivAt_id (x : ℂ)).const_add z)).congr_deriv (mul_one _)
    exact hc.comp_ofReal
  have hcont : ContinuousWithinAt f (Ici 0) 0 := (hf_deriv 0).continuousAt.continuousWithinAt
  have hdom : IntegrableOn (fun x : ℝ =>
      (Real.exp (-(z.re * A)) / |z.im|) * Real.exp (-(A * x))) (Ioi 0) := by
    have h : IntegrableOn (fun x : ℝ => Real.exp (-A * x)) (Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 hA
    have hc : IntegrableOn (fun x : ℝ =>
        (Real.exp (-(z.re * A)) / |z.im|) * Real.exp (-A * x)) (Ioi 0) :=
      h.const_mul (Real.exp (-(z.re * A)) / |z.im|)
    exact hc.congr_fun (fun _ _ => by dsimp only; rw [neg_mul]) measurableSet_Ioi
  have hg_bound : ∀ x : ℝ, ‖g x‖ ≤
      (Real.exp (-(z.re * A)) / |z.im|) * Real.exp (-(A * x)) := by
    intro x
    dsimp only [g]
    rw [norm_div, norm_cexp_neg_mul_ofReal]
    have hre : -((z + (x : ℂ)).re * A) = -(z.re * A) + -(A * x) := by
      simp [Complex.add_re]; ring
    rw [hre, Real.exp_add]
    have hden : |z.im| ≤ ‖z + (x : ℂ)‖ := by
      have him : |(z + (x : ℂ)).im| = |z.im| := by simp
      rw [← him]
      exact Complex.abs_im_le_norm _
    calc Real.exp (-(z.re * A)) * Real.exp (-(A * x)) / ‖z + (x : ℂ)‖
        ≤ Real.exp (-(z.re * A)) * Real.exp (-(A * x)) / |z.im| :=
          div_le_div_of_nonneg_left (by positivity) him_pos hden
      _ = (Real.exp (-(z.re * A)) / |z.im|) * Real.exp (-(A * x)) := by ring
  have hg_int : IntegrableOn g (Ioi 0) := by
    have hmeas : AEStronglyMeasurable g (volume.restrict (Ioi 0)) := by
      refine (Continuous.div (by fun_prop) (by fun_prop) fun x => ?_).aestronglyMeasurable
      exact Complex.slitPlane_ne_zero (hslit x)
    exact hdom.mono' hmeas (Eventually.of_forall hg_bound)
  have htend : Tendsto f atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmaj : Tendsto (fun x : ℝ =>
        (Real.exp (-(z.re * A)) / A) * Real.exp (-(A * x))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => -(A * x)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hA tendsto_id)
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (Real.exp (-(z.re * A)) / A)
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
    filter_upwards [eventually_ge_atTop (|z.re| + 1)] with x hx
    have hre1 : 1 ≤ (z + (x : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith [neg_le_abs z.re]
    have hb := norm_frullaniCutoffLog_le_of_re_pos hA (lt_of_lt_of_le zero_lt_one hre1)
    dsimp only [f]
    refine hb.trans ?_
    have hre : -((z + (x : ℂ)).re * A) = -(z.re * A) + -(A * x) := by
      simp [Complex.add_re]; ring
    rw [hre, Real.exp_add]
    calc Real.exp (-(z.re * A)) * Real.exp (-(A * x)) / (A * (z + (x : ℂ)).re)
        ≤ Real.exp (-(z.re * A)) * Real.exp (-(A * x)) / (A * 1) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left hre1 hA.le)
      _ = (Real.exp (-(z.re * A)) / A) * Real.exp (-(A * x)) := by ring
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun x _ => hf_deriv x) hg_int htend
  have hf0 : frullaniCutoffLog A z = -∫ x in Ioi (0 : ℝ), g x := by
    have h0 : f 0 = frullaniCutoffLog A z := by simp [f]
    rw [h0, zero_sub] at hval
    exact neg_eq_iff_eq_neg.mp hval.symm
  rw [hf0, norm_neg]
  refine (norm_integral_le_of_norm_le hdom (Eventually.of_forall hg_bound)).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_Ioi_exp_neg_mul hA]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  field_simp

/-! ### Two-scale specification, continuous density perturbation, and `remFactor` -/

/-- Wave data: a top pair `β ± i γ` with `β < 2/3`, `γ > 0`, a ceiling `θ₂ < β`, and remainder
real parts `½ < θ_n ≤ θ₂`. -/
structure WaveSpec where
  θ₂ : ℝ
  β : ℝ
  γ : ℝ
  θSeq : ℕ → ℝ
  half_lt_θSeq : ∀ n, 1 / 2 < θSeq n
  θSeq_le_θ₂ : ∀ n, θSeq n ≤ θ₂
  hβ : θ₂ < β
  h23 : β < 2 / 3
  hγ : 0 < γ

namespace WaveSpec

variable (S : WaveSpec)

theorem half_lt_θ₂ : 1 / 2 < S.θ₂ := (S.half_lt_θSeq 0).trans_le (S.θSeq_le_θ₂ 0)

/-- Base single-pair Beurling parameters placing the top conjugate pair at `β ± i γ`. -/
def P : DiscreteOneOff.Params where
  μ := 1 - S.β
  ν := (3 * (1 - S.β) - 1) / 2
  γ := S.γ
  hμ1 := by linarith [S.h23]
  hμ2 := by linarith [S.half_lt_θ₂, S.hβ]
  hν0 := by linarith [S.h23]
  hν := by linarith [S.h23]

/-- Base density floor constant `c₀ = (1 - e^{-μ})^3 > 0`. -/
def c₀ : ℝ := (1 - Real.exp (-S.P.μ)) ^ 3

theorem c₀_pos : 0 < S.c₀ := S.P.c₀_pos
theorem c₀_le_one : S.c₀ ≤ 1 := S.P.c₀_le_one

/-- Initial logarithmic cutoff `U₀` ensuring `|w_∞(t)| ≤ (1/4) P.w(t)` for all `t > 0`. -/
def U₀ : ℝ := max 2 (32 / (S.c₀ * (1 - S.θ₂) ^ 2))

theorem two_le_U₀ : 2 ≤ S.U₀ := le_max_left _ _

/-- `n`-th logarithmic cutoff `A_n = U₀ + n + 1`. -/
def A (n : ℕ) : ℝ := S.U₀ + (n : ℝ) + 1

theorem three_le_A (n : ℕ) : 3 ≤ S.A n := by
  unfold A; linarith [S.two_le_U₀, Nat.cast_nonneg (α := ℝ) n]

theorem A_pos (n : ℕ) : 0 < S.A n := by linarith [S.three_le_A n]

/-- Integer frequency multiplier `M_n` making `cos(ω_n A_n) = 0` with `ω_n` exponentially large. -/
def M (n : ℕ) : ℕ :=
  ⌈S.A n * (S.γ + 4 + (n : ℝ) + (2 : ℝ) ^ n * Real.exp (2 * S.A n)) / (2 * Real.pi)⌉₊ + 1

/-- `n`-th remainder ordinate `ω_n = (π/2 + 2π M_n) / A_n`. -/
def ω (n : ℕ) : ℝ := (Real.pi / 2 + (S.M n : ℝ) * (2 * Real.pi)) / S.A n

theorem ω_gt_bound (n : ℕ) :
    S.γ + 4 + (n : ℝ) + (2 : ℝ) ^ n * Real.exp (2 * S.A n) < S.ω n := by
  have hAp := S.A_pos n
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hceil := Nat.le_ceil
    (S.A n * (S.γ + 4 + (n : ℝ) + (2 : ℝ) ^ n * Real.exp (2 * S.A n)) / (2 * Real.pi))
  have hM : S.A n * (S.γ + 4 + (n : ℝ) + (2 : ℝ) ^ n * Real.exp (2 * S.A n)) <
      (S.M n : ℝ) * (2 * Real.pi) := by
    have h1 := (div_le_iff₀ h2pi).mp hceil
    unfold M
    push_cast
    linarith [Real.pi_pos]
  rw [ω, lt_div_iff₀ hAp, mul_comm]
  linarith [Real.pi_pos]

theorem ω_gt_γ (n : ℕ) : S.γ < S.ω n := by
  have hb := S.ω_gt_bound n
  have hp : 0 ≤ (n : ℝ) + (2 : ℝ) ^ n * Real.exp (2 * S.A n) := by positivity
  linarith

theorem tendsto_ω_atTop : Tendsto S.ω atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  have hb := S.ω_gt_bound n
  have hp : 0 ≤ S.γ + (2 : ℝ) ^ n * Real.exp (2 * S.A n) := by
    have := S.hγ; positivity
  linarith

theorem cos_ω_mul_A (n : ℕ) : Real.cos (S.ω n * S.A n) = 0 := by
  have hmul : S.ω n * S.A n = Real.pi / 2 + (S.M n : ℝ) * (2 * Real.pi) :=
    div_mul_cancel₀ _ (S.A_pos n).ne'
  rw [hmul, Real.cos_add_nat_mul_two_pi, Real.cos_pi_div_two]

/-- `n`-th upper remainder zero `ρ_n = θ_n + i ω_n`. -/
def remZero (n : ℕ) : ℂ := (S.θSeq n : ℂ) + (S.ω n : ℂ) * I

theorem remZero_re (n : ℕ) : (S.remZero n).re = S.θSeq n := by simp [remZero]
theorem remZero_im (n : ℕ) : (S.remZero n).im = S.ω n := by simp [remZero]

/-- `n`-th continuous cutoff wave `-2 e^{θ_n t} cos(ω_n t) / t · 1_{[A_n, ∞)}(t)`. -/
def wave (n : ℕ) (t : ℝ) : ℝ :=
  if S.A n ≤ t then -2 * Real.exp (S.θSeq n * t) * Real.cos (S.ω n * t) / t else 0

theorem continuous_wave (n : ℕ) : Continuous (S.wave n) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rcases lt_trichotomy t₀ (S.A n) with hlt | rfl | hgt
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t₀).congr ?_
    filter_upwards [(isOpen_gt' (S.A n)).mem_nhds hlt] with t ht
    exact (if_neg (not_le.mpr ht)).symm
  · let g : ℝ → ℝ := fun t => -2 * Real.exp (S.θSeq n * t) * Real.cos (S.ω n * t) / t
    have hg0 : g (S.A n) = 0 := by
      dsimp only [g]
      rw [S.cos_ω_mul_A n, mul_zero, zero_div]
    have hw0 : S.wave n (S.A n) = 0 := by simp [wave, S.cos_ω_mul_A n]
    have hgc : ContinuousAt g (S.A n) := by
      dsimp only [g]
      exact (ContinuousAt.div (by fun_prop) continuousAt_id (S.A_pos n).ne')
    rw [ContinuousAt, hw0]
    refine squeeze_zero_norm (a := fun t => ‖g t‖) (fun t => ?_) ?_
    · dsimp only [wave]
      split_ifs
      · exact le_rfl
      · simp
    · simpa [hg0] using hgc.norm.tendsto
  · have ht₀ : 0 < t₀ := (S.A_pos n).trans hgt
    have hgc : ContinuousAt
        (fun t : ℝ => -2 * Real.exp (S.θSeq n * t) * Real.cos (S.ω n * t) / t) t₀ :=
      ContinuousAt.div (by fun_prop) continuousAt_id ht₀.ne'
    refine hgc.congr ?_
    filter_upwards [(isOpen_lt' (S.A n)).mem_nhds hgt] with t ht
    exact (if_pos ht.le).symm

/-- Added infinite-remainder prime density `w_∞(t) = ∑' n, wave n t`. -/
def wRem (t : ℝ) : ℝ := ∑' n : ℕ, S.wave n t

theorem wRem_eq_sum_of_lt {N : ℕ} {t : ℝ} (ht : t < S.A N) :
    S.wRem t = ∑ n ∈ Finset.range N, S.wave n t := by
  unfold wRem
  refine tsum_eq_sum fun n hn => ?_
  have hN : N ≤ n := not_lt.mp (Finset.mem_range.not.mp hn)
  have hn' : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hN
  have hAn : S.A N ≤ S.A n := by unfold A; linarith
  exact if_neg (not_le.mpr (ht.trans_le hAn))

theorem wRem_eq_zero_of_lt {t : ℝ} (ht : t < S.A 0) : S.wRem t = 0 := by
  rw [S.wRem_eq_sum_of_lt ht, Finset.range_zero, Finset.sum_empty]

theorem continuous_wRem : Continuous S.wRem := by
  rw [continuous_iff_continuousAt]
  intro t₀
  let N : ℕ := ⌊max t₀ 0⌋₊ + 1
  have htN : t₀ < S.A N := by
    have h1 : t₀ ≤ max t₀ 0 := le_max_left _ _
    have h2 : max t₀ 0 < (N : ℝ) := by exact_mod_cast Nat.lt_floor_add_one (max t₀ 0)
    have hU := S.two_le_U₀
    unfold A
    linarith
  have hc : Continuous (fun t : ℝ => ∑ n ∈ Finset.range N, S.wave n t) :=
    continuous_finsetSum _ fun n _ => S.continuous_wave n
  refine hc.continuousAt.congr ?_
  filter_upwards [(isOpen_gt' (S.A N)).mem_nhds htN] with t ht
  exact (S.wRem_eq_sum_of_lt ht).symm

/-- Smallness of the infinite-remainder wave sum: `|w_∞(t)| ≤ (1/4) P.w(t)` for every `t > 0`. -/
theorem abs_wRem_le {t : ℝ} (ht : 0 < t) : |S.wRem t| ≤ (1 / 4) * S.P.w t := by
  by_cases h0 : t < S.A 0
  · rw [S.wRem_eq_zero_of_lt h0, abs_zero]
    exact mul_nonneg (by norm_num) (S.P.w_pos ht).le
  · push Not at h0
    have htU : S.U₀ ≤ t := by unfold A at h0; linarith
    have ht1 : 1 ≤ t := by linarith [S.two_le_U₀, htU]
    let N : ℕ := ⌊t⌋₊
    have htA : t < S.A N := by
      have hf : t < (N : ℝ) + 1 := Nat.lt_floor_add_one t
      unfold A
      linarith [S.two_le_U₀]
    rw [S.wRem_eq_sum_of_lt htA]
    have hterm : ∀ n ∈ Finset.range N, |S.wave n t| ≤ 2 * Real.exp (S.θ₂ * t) / t := by
      intro n _
      dsimp only [wave]
      split_ifs with hAn
      · rw [abs_div, abs_of_pos ht, abs_mul, abs_mul, abs_neg, abs_of_pos two_pos,
          abs_of_pos (Real.exp_pos _)]
        have hc : |Real.cos (S.ω n * t)| ≤ 1 := Real.abs_cos_le_one _
        have he : Real.exp (S.θSeq n * t) ≤ Real.exp (S.θ₂ * t) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (S.θSeq_le_θ₂ n) ht.le)
        refine div_le_div_of_nonneg_right ?_ ht.le
        nlinarith [Real.exp_pos (S.θSeq n * t)]
      · rw [abs_zero]
        positivity
    have hsum_le : |∑ n ∈ Finset.range N, S.wave n t| ≤ 2 * Real.exp (S.θ₂ * t) := by
      calc |∑ n ∈ Finset.range N, S.wave n t|
          ≤ ∑ n ∈ Finset.range N, |S.wave n t| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ Finset.range N, (2 * Real.exp (S.θ₂ * t) / t) := Finset.sum_le_sum hterm
        _ = (N : ℝ) * (2 * Real.exp (S.θ₂ * t) / t) := by simp
        _ ≤ t * (2 * Real.exp (S.θ₂ * t) / t) :=
          mul_le_mul_of_nonneg_right (Nat.floor_le ht.le) (by positivity)
        _ = 2 * Real.exp (S.θ₂ * t) := mul_div_cancel₀ _ ht.ne'
    refine hsum_le.trans ?_
    have hgap : 0 < 1 - S.θ₂ := by linarith [S.hβ, S.h23]
    have hU32 : 32 / (S.c₀ * (1 - S.θ₂) ^ 2) ≤ t := (le_max_right 2 _).trans htU
    have hcpos : 0 < S.c₀ * (1 - S.θ₂) ^ 2 := mul_pos S.c₀_pos (sq_pos_of_pos hgap)
    have hquad : 32 ≤ t * (S.c₀ * (1 - S.θ₂) ^ 2) := (div_le_iff₀ hcpos).mp hU32
    have hexp_sq : ((1 - S.θ₂) * t) ^ 2 / 4 ≤ Real.exp ((1 - S.θ₂) * t) := by
      have hhalf := Real.add_one_le_exp (((1 - S.θ₂) * t) / 2)
      have h0 : 0 ≤ (1 - S.θ₂) * t / 2 + 1 := by positivity
      have hsq := pow_le_pow_left₀ h0 hhalf 2
      have he2 : Real.exp ((1 - S.θ₂) * t / 2) ^ 2 = Real.exp ((1 - S.θ₂) * t) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      rw [he2] at hsq
      nlinarith
    have h8t : 8 * t ≤ S.c₀ * Real.exp ((1 - S.θ₂) * t) := by
      have h1 : 8 * t ≤ S.c₀ * (((1 - S.θ₂) * t) ^ 2 / 4) := by nlinarith [hquad, ht]
      exact h1.trans (mul_le_mul_of_nonneg_left hexp_sq S.c₀_pos.le)
    have hdom : 2 * Real.exp (S.θ₂ * t) ≤ (1 / 4) * (S.c₀ * Real.exp t / t) := by
      rw [mul_div_assoc', le_div_iff₀ ht]
      have hmul := mul_le_mul_of_nonneg_right h8t (Real.exp_pos (S.θ₂ * t)).le
      have hex : S.c₀ * Real.exp ((1 - S.θ₂) * t) * Real.exp (S.θ₂ * t) =
          S.c₀ * Real.exp t := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      rw [hex] at hmul
      linarith
    exact hdom.trans (mul_le_mul_of_nonneg_left (S.P.w_ge ht1) (by norm_num))

/-- Total two-scale logarithmic prime density `w(t) = P.w(t) + w_∞(t)`. -/
def w (t : ℝ) : ℝ := S.P.w t + S.wRem t

theorem w_bounds {t : ℝ} (ht : 0 < t) :
    (3 / 4) * S.P.w t ≤ S.w t ∧ S.w t ≤ (5 / 4) * S.P.w t := by
  have hb := abs_le.mp (S.abs_wRem_le ht)
  unfold w
  constructor <;> linarith

theorem w_pos {t : ℝ} (ht : 0 < t) : 0 < S.w t :=
  lt_of_lt_of_le (mul_pos (by norm_num) (S.P.w_pos ht)) (S.w_bounds ht).1

theorem continuousOn_w : ContinuousOn S.w (Ioi 0) :=
  S.P.continuousOn_w.add S.continuous_wRem.continuousOn

theorem measurable_w : Measurable S.w := S.P.measurable_w.add S.continuous_wRem.measurable

/-- `K`-th patched remainder factor on `{Re s > 0, |Im s| < K + 2}`. -/
def patch (K : ℕ) (s : ℂ) : ℂ :=
  (∏ n ∈ Finset.range K,
      frullaniCutoffFactor (S.A n) (s - S.remZero n) *
        frullaniCutoffFactor (S.A n) (s - starRingEnd ℂ (S.remZero n))) *
    cexp (∑' m : ℕ,
      (frullaniCutoffLog (S.A (m + K)) (s - S.remZero (m + K)) +
        frullaniCutoffLog (S.A (m + K)) (s - starRingEnd ℂ (S.remZero (m + K)))))

/-- Global analytic continuation of the infinite-remainder Euler factor to `{Re s > 0}`. -/
def remFactor (s : ℂ) : ℂ := S.patch (⌈|s.im|⌉₊ + 1) s

private theorem norm_tailTerm_le {K m : ℕ} {s : ℂ} (hs0 : 0 < s.re)
    (hsim : |s.im| < (K : ℝ) + 2) :
    ‖frullaniCutoffLog (S.A (m + K)) (s - S.remZero (m + K)) +
        frullaniCutoffLog (S.A (m + K)) (s - starRingEnd ℂ (S.remZero (m + K)))‖ ≤
      2 * (1 / 2 : ℝ) ^ (m + K) := by
  let n : ℕ := m + K
  have hnK : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_add_left K m
  have hω : S.γ + 4 + (n : ℝ) + (2 : ℝ) ^ n * Real.exp (2 * S.A n) < S.ω n := S.ω_gt_bound n
  have hp : 0 < (2 : ℝ) ^ n * Real.exp (2 * S.A n) := by positivity
  have hgap : (2 : ℝ) ^ n * Real.exp (2 * S.A n) < S.ω n - |s.im| := by
    linarith [S.hγ, hsim, hnK, hω]
  have hgap_pos : 0 < S.ω n - |s.im| := hp.trans hgap
  have him1 : (2 : ℝ) ^ n * Real.exp (2 * S.A n) < |(s - S.remZero n).im| := by
    have h1 : (s - S.remZero n).im = s.im - S.ω n := by simp [remZero]
    have ha1 : |s.im - S.ω n| = -(s.im - S.ω n) :=
      abs_of_neg (by linarith [le_abs_self s.im, hgap_pos])
    have h2 : S.ω n - |s.im| ≤ |s.im - S.ω n| := by
      rw [ha1]
      linarith [le_abs_self s.im]
    rw [h1]
    exact hgap.trans_le h2
  have him2 : (2 : ℝ) ^ n * Real.exp (2 * S.A n) < |(s - starRingEnd ℂ (S.remZero n)).im| := by
    have h1 : (s - starRingEnd ℂ (S.remZero n)).im = s.im + S.ω n := by simp [remZero]
    have ha2 : |s.im + S.ω n| = s.im + S.ω n :=
      abs_of_pos (by linarith [neg_le_abs s.im, hgap_pos])
    have h2 : S.ω n - |s.im| ≤ |s.im + S.ω n| := by
      rw [ha2]
      linarith [neg_le_abs s.im]
    rw [h1]
    exact hgap.trans_le h2
  have hexp_le : ∀ z : ℂ, z.re = s.re - S.θSeq n →
      Real.exp (-(z.re * S.A n)) ≤ Real.exp (2 * S.A n) := by
    intro z hz
    apply Real.exp_le_exp.mpr
    have hθ : S.θSeq n < 2 := (S.θSeq_le_θ₂ n).trans_lt (S.hβ.trans (S.h23.trans (by norm_num)))
    have hAp := S.A_pos n
    rw [hz]
    nlinarith
  have hA1 : 1 ≤ S.A n := by linarith [S.three_le_A n]
  have hb1 : ‖frullaniCutoffLog (S.A n) (s - S.remZero n)‖ ≤ (1 / 2 : ℝ) ^ n := by
    have hne : (s - S.remZero n).im ≠ 0 := by
      intro h0; rw [h0, abs_zero] at him1; linarith
    refine (norm_frullaniCutoffLog_le_of_im_ne_zero (S.A_pos n) hne).trans ?_
    have he := hexp_le (s - S.remZero n) (by simp [remZero])
    have hd : (2 : ℝ) ^ n * Real.exp (2 * S.A n) ≤ S.A n * |(s - S.remZero n).im| :=
      calc (2 : ℝ) ^ n * Real.exp (2 * S.A n)
          = 1 * ((2 : ℝ) ^ n * Real.exp (2 * S.A n)) := (one_mul _).symm
        _ ≤ S.A n * |(s - S.remZero n).im| := mul_le_mul hA1 him1.le hp.le (by linarith)
    calc Real.exp (-((s - S.remZero n).re * S.A n)) / (S.A n * |(s - S.remZero n).im|)
        ≤ Real.exp (2 * S.A n) / ((2 : ℝ) ^ n * Real.exp (2 * S.A n)) :=
          div_le_div₀ (by positivity) he hp hd
      _ = (1 / 2 : ℝ) ^ n := by
          rw [one_div_pow]
          field_simp
  have hb2 : ‖frullaniCutoffLog (S.A n) (s - starRingEnd ℂ (S.remZero n))‖ ≤ (1 / 2 : ℝ) ^ n := by
    have hne : (s - starRingEnd ℂ (S.remZero n)).im ≠ 0 := by
      intro h0; rw [h0, abs_zero] at him2; linarith
    refine (norm_frullaniCutoffLog_le_of_im_ne_zero (S.A_pos n) hne).trans ?_
    have he := hexp_le (s - starRingEnd ℂ (S.remZero n)) (by simp [remZero])
    have hd : (2 : ℝ) ^ n * Real.exp (2 * S.A n) ≤
        S.A n * |(s - starRingEnd ℂ (S.remZero n)).im| :=
      calc (2 : ℝ) ^ n * Real.exp (2 * S.A n)
          = 1 * ((2 : ℝ) ^ n * Real.exp (2 * S.A n)) := (one_mul _).symm
        _ ≤ S.A n * |(s - starRingEnd ℂ (S.remZero n)).im| :=
          mul_le_mul hA1 him2.le hp.le (by linarith)
    calc Real.exp (-((s - starRingEnd ℂ (S.remZero n)).re * S.A n)) /
          (S.A n * |(s - starRingEnd ℂ (S.remZero n)).im|)
        ≤ Real.exp (2 * S.A n) / ((2 : ℝ) ^ n * Real.exp (2 * S.A n)) :=
          div_le_div₀ (by positivity) he hp hd
      _ = (1 / 2 : ℝ) ^ n := by
          rw [one_div_pow]
          field_simp
  exact (norm_add_le _ _).trans (by dsimp only [n] at hb1 hb2; linarith)

private theorem summable_tailTerm {K : ℕ} {s : ℂ} (hs0 : 0 < s.re)
    (hsim : |s.im| < (K : ℝ) + 2) :
    Summable fun m : ℕ =>
      frullaniCutoffLog (S.A (m + K)) (s - S.remZero (m + K)) +
        frullaniCutoffLog (S.A (m + K)) (s - starRingEnd ℂ (S.remZero (m + K))) := by
  have hmaj : Summable fun m : ℕ => (2 * (1 / 2 : ℝ) ^ K) * (1 / 2 : ℝ) ^ m :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine Summable.of_norm_bounded hmaj fun m => ?_
  refine (S.norm_tailTerm_le hs0 hsim).trans (le_of_eq ?_)
  rw [pow_add]
  ring

private theorem patch_eq_succ {K : ℕ} {s : ℂ} (hs0 : 0 < s.re) (hsim : |s.im| < (K : ℝ) + 2) :
    S.patch K s = S.patch (K + 1) s := by
  have hω : S.γ + 4 + (K : ℝ) + (2 : ℝ) ^ K * Real.exp (2 * S.A K) < S.ω K := S.ω_gt_bound K
  have hp : 0 ≤ S.γ + (2 : ℝ) ^ K * Real.exp (2 * S.A K) := by have := S.hγ; positivity
  have him_lt : |s.im| < S.ω K := by linarith
  have hne1 : s - S.remZero K ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    simp only [Complex.sub_im, remZero_im, Complex.zero_im] at him
    linarith [le_abs_self s.im]
  have hne2 : s - starRingEnd ℂ (S.remZero K) ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, remZero_im, Complex.zero_im] at him
    linarith [neg_le_abs s.im]
  have hsum := S.summable_tailTerm hs0 hsim
  have htsum : (∑' m : ℕ,
      (frullaniCutoffLog (S.A (m + K)) (s - S.remZero (m + K)) +
        frullaniCutoffLog (S.A (m + K)) (s - starRingEnd ℂ (S.remZero (m + K))))) =
      (frullaniCutoffLog (S.A K) (s - S.remZero K) +
        frullaniCutoffLog (S.A K) (s - starRingEnd ℂ (S.remZero K))) +
      ∑' m : ℕ,
        (frullaniCutoffLog (S.A (m + (K + 1))) (s - S.remZero (m + (K + 1))) +
          frullaniCutoffLog (S.A (m + (K + 1))) (s - starRingEnd ℂ (S.remZero (m + (K + 1))))) := by
    rw [hsum.tsum_eq_zero_add]
    simp only [zero_add]
    congr 1
    exact tsum_congr fun m => by rw [show m + 1 + K = m + (K + 1) by omega]
  unfold patch
  rw [Finset.prod_range_succ, htsum, Complex.exp_add, Complex.exp_add,
    ← frullaniCutoffFactor_eq_cexp_of_ne_zero (S.A K) hne1,
    ← frullaniCutoffFactor_eq_cexp_of_ne_zero (S.A K) hne2]
  ring

private theorem patch_eq_of_le {J K : ℕ} (hJK : J ≤ K) {s : ℂ} (hs0 : 0 < s.re)
    (hsim : |s.im| < (J : ℝ) + 2) :
    S.patch J s = S.patch K s := by
  induction K, hJK using Nat.le_induction with
  | base => rfl
  | succ k hJk ih =>
      have hk : |s.im| < (k : ℝ) + 2 := hsim.trans_le (by exact_mod_cast Nat.add_le_add_right hJk 2)
      exact ih.trans (S.patch_eq_succ hs0 hk)

private theorem differentiableOn_patch (K : ℕ) :
    DifferentiableOn ℂ (S.patch K) {s : ℂ | 0 < s.re ∧ |s.im| < (K : ℝ) + 2} := by
  set U : Set ℂ := {s : ℂ | 0 < s.re ∧ |s.im| < (K : ℝ) + 2}
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  have hhead : DifferentiableOn ℂ
      (fun s : ℂ => ∏ n ∈ Finset.range K,
        frullaniCutoffFactor (S.A n) (s - S.remZero n) *
          frullaniCutoffFactor (S.A n) (s - starRingEnd ℂ (S.remZero n))) U :=
    (Differentiable.fun_finsetProd fun n _ =>
      ((differentiable_frullaniCutoffFactor (S.A_pos n)).comp
        (differentiable_id.sub_const _)).mul
      ((differentiable_frullaniCutoffFactor (S.A_pos n)).comp
        (differentiable_id.sub_const _))).differentiableOn
  have hmaj : Summable fun m : ℕ => (2 * (1 / 2 : ℝ) ^ K) * (1 / 2 : ℝ) ^ m :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hterm_diff : ∀ m : ℕ, DifferentiableOn ℂ
      (fun s : ℂ => frullaniCutoffLog (S.A (m + K)) (s - S.remZero (m + K)) +
        frullaniCutoffLog (S.A (m + K)) (s - starRingEnd ℂ (S.remZero (m + K)))) U := by
    intro m s hs
    let n : ℕ := m + K
    have hnK : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_add_left K m
    have hω := S.ω_gt_bound n
    have hp : 0 ≤ S.γ + (2 : ℝ) ^ n * Real.exp (2 * S.A n) := by have := S.hγ; positivity
    have him_lt : |s.im| < S.ω n := by linarith [hs.2, hnK, hω]
    have hslit1 : s - S.remZero n ∈ Complex.slitPlane := by
      refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
      simp only [Complex.sub_im, remZero_im]
      linarith [le_abs_self s.im]
    have hslit2 : s - starRingEnd ℂ (S.remZero n) ∈ Complex.slitPlane := by
      refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
      simp only [Complex.sub_im, Complex.conj_im, remZero_im]
      linarith [neg_le_abs s.im]
    have hd1 := (hasDerivAt_frullaniCutoffLog (S.A_pos n) hslit1).differentiableAt.comp s
      (differentiableAt_id.sub_const _)
    have hd2 := (hasDerivAt_frullaniCutoffLog (S.A_pos n) hslit2).differentiableAt.comp s
      (differentiableAt_id.sub_const _)
    exact (hd1.add hd2).differentiableWithinAt
  have hbound : ∀ m : ℕ, ∀ s ∈ U,
      ‖frullaniCutoffLog (S.A (m + K)) (s - S.remZero (m + K)) +
        frullaniCutoffLog (S.A (m + K)) (s - starRingEnd ℂ (S.remZero (m + K)))‖ ≤
        (2 * (1 / 2 : ℝ) ^ K) * (1 / 2 : ℝ) ^ m := by
    intro m s hs
    refine (S.norm_tailTerm_le hs.1 hs.2).trans (le_of_eq ?_)
    rw [pow_add]; ring
  have htail := differentiableOn_tsum_of_summable_norm hmaj hterm_diff hUo hbound
  exact hhead.mul htail.cexp

/-- `remFactor` is holomorphic on `{s : ℂ | 0 < s.re}`. -/
theorem differentiableOn_remFactor :
    DifferentiableOn ℂ S.remFactor {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 0 < s₀.re := hs₀
  let K : ℕ := ⌈|s₀.im|⌉₊ + 1
  set U : Set ℂ := {s : ℂ | 0 < s.re ∧ |s.im| < (K : ℝ)}
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  have hs₀U : s₀ ∈ U := by
    refine ⟨hs₀', ?_⟩
    have hc : |s₀.im| ≤ (⌈|s₀.im|⌉₊ : ℝ) := Nat.le_ceil _
    dsimp only [K]; push_cast; linarith
  have heq : S.remFactor =ᶠ[𝓝 s₀] S.patch (K + 1) := by
    filter_upwards [hUo.mem_nhds hs₀U] with s hs
    unfold remFactor
    have hceil : ⌈|s.im|⌉₊ ≤ K := Nat.ceil_le.mpr hs.2.le
    have hsim : |s.im| < ((⌈|s.im|⌉₊ + 1 : ℕ) : ℝ) + 2 := by
      have hc : |s.im| ≤ (⌈|s.im|⌉₊ : ℝ) := Nat.le_ceil _
      push_cast; linarith
    exact S.patch_eq_of_le (Nat.add_le_add_right hceil 1) hs.1 hsim
  have hU_sub : U ⊆ {s : ℂ | 0 < s.re ∧ |s.im| < ((K + 1 : ℕ) : ℝ) + 2} := by
    intro s hs
    exact ⟨hs.1, hs.2.trans (by push_cast; linarith)⟩
  have hd : DifferentiableAt ℂ (S.patch (K + 1)) s₀ :=
    ((S.differentiableOn_patch (K + 1)).mono hU_sub).differentiableAt (hUo.mem_nhds hs₀U)
  exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt

/-- On `0 < s.re`, `remFactor s = 0` iff `s` is one of `ρ_n` or `conj ρ_n`. -/
theorem remFactor_eq_zero_iff {s : ℂ} (hs : 0 < s.re) :
    S.remFactor s = 0 ↔ ∃ n : ℕ, s = S.remZero n ∨ s = starRingEnd ℂ (S.remZero n) := by
  unfold remFactor patch
  rw [mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), Finset.prod_eq_zero_iff]
  simp only [Finset.mem_range, mul_eq_zero, frullaniCutoffFactor_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro ⟨n, _, h⟩
    exact ⟨n, h⟩
  · rintro ⟨n, h⟩
    refine ⟨n, ?_, h⟩
    by_contra hge
    have hn : ⌈|s.im|⌉₊ + 1 ≤ n := not_lt.mp hge
    have hω := S.ω_gt_bound n
    have hp : 0 ≤ S.γ + (2 : ℝ) ^ n * Real.exp (2 * S.A n) := by have := S.hγ; positivity
    have hc : |s.im| ≤ (⌈|s.im|⌉₊ : ℝ) := Nat.le_ceil _
    have hn' : (⌈|s.im|⌉₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have him : |s.im| = S.ω n := by
      rcases h with rfl | rfl <;> simp [remZero, abs_of_pos (S.hγ.trans (S.ω_gt_γ n))]
    linarith

/-- On `1 < s.re`, `remFactor s = exp (∫_{t > 0} e^{-s t} w_∞(t) dt)`. -/
theorem remFactor_eq_cexp_integral {s : ℂ} (hs : 1 < s.re) :
    S.remFactor s = cexp (∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (S.wRem t : ℂ)) := by
  let K : ℕ := ⌈|s.im|⌉₊ + 1
  have hK : ∀ n < K,
      frullaniCutoffFactor (S.A n) (s - S.remZero n) *
        frullaniCutoffFactor (S.A n) (s - starRingEnd ℂ (S.remZero n)) =
      cexp (frullaniCutoffLog (S.A n) (s - S.remZero n) +
        frullaniCutoffLog (S.A n) (s - starRingEnd ℂ (S.remZero n))) := by
    intro n _
    have hθ : S.θSeq n < 1 := (S.θSeq_le_θ₂ n).trans_lt (S.hβ.trans (S.h23.trans (by norm_num)))
    have hr1 : 0 < (s - S.remZero n).re := by simp [remZero]; linarith
    have hr2 : 0 < (s - starRingEnd ℂ (S.remZero n)).re := by simp [remZero]; linarith
    have hne1 : s - S.remZero n ≠ 0 := by intro h0; rw [h0] at hr1; simp at hr1
    have hne2 : s - starRingEnd ℂ (S.remZero n) ≠ 0 := by intro h0; rw [h0] at hr2; simp at hr2
    rw [frullaniCutoffFactor_eq_cexp_of_ne_zero _ hne1,
      frullaniCutoffFactor_eq_cexp_of_ne_zero _ hne2, ← Complex.exp_add]
  let φ : ℕ → ℂ := fun n =>
    frullaniCutoffLog (S.A n) (s - S.remZero n) +
      frullaniCutoffLog (S.A n) (s - starRingEnd ℂ (S.remZero n))
  let δ : ℝ := s.re - S.θ₂
  have hδ : 0 < δ := by dsimp only [δ]; linarith [S.hβ, S.h23, hs]
  let G : ℕ → ℝ → ℂ := fun n t => cexp (-(s * t)) * (S.wave n t : ℂ)
  have hG_eq : ∀ n : ℕ, ∫ t in Ioi (0 : ℝ), G n t = φ n := by
    intro n
    have hθ : S.θSeq n < 1 := (S.θSeq_le_θ₂ n).trans_lt (S.hβ.trans (S.h23.trans (by norm_num)))
    have hr1 : 0 < (s - S.remZero n).re := by simp [remZero]; linarith
    have hr2 : 0 < (s - starRingEnd ℂ (S.remZero n)).re := by simp [remZero]; linarith
    dsimp only [φ]
    rw [frullaniCutoffLog_eq_neg_integral_of_re_pos (S.A_pos n) hr1,
      frullaniCutoffLog_eq_neg_integral_of_re_pos (S.A_pos n) hr2,
      ← neg_add, ← integral_add (integrableOn_cexp_div_Ioi (S.A_pos n) hr1)
        (integrableOn_cexp_div_Ioi (S.A_pos n) hr2), ← integral_neg]
    have hind : ∀ t : ℝ, G n t = (Ici (S.A n)).indicator
        (fun u : ℝ => -(cexp (-((s - S.remZero n) * u)) / u +
          cexp (-((s - starRingEnd ℂ (S.remZero n)) * u)) / u)) t := by
      intro t
      dsimp only [G, wave]
      by_cases ht : S.A n ≤ t
      · rw [if_pos ht, Set.indicator_of_mem (mem_Ici.mpr ht)]
        have ecos : cexp (((S.ω n : ℂ) * t) * I) + cexp (-(((S.ω n : ℂ) * t) * I)) =
            2 * Complex.cos ((S.ω n : ℂ) * t) := by
          rw [Complex.exp_mul_I, show -(((S.ω n : ℂ) * t) * I) = (-((S.ω n : ℂ) * t)) * I by ring,
            Complex.exp_mul_I]
          simp [Complex.cos_neg, Complex.sin_neg]; ring
        have e1 : cexp (-((s - S.remZero n) * t)) =
            cexp (-(s * t)) * (cexp ((S.θSeq n : ℂ) * t) * cexp (((S.ω n : ℂ) * t) * I)) := by
          rw [← Complex.exp_add, ← Complex.exp_add]; simp [remZero]; ring_nf
        have e2 : cexp (-((s - starRingEnd ℂ (S.remZero n)) * t)) =
            cexp (-(s * t)) * (cexp ((S.θSeq n : ℂ) * t) * cexp (-(((S.ω n : ℂ) * t) * I))) := by
          rw [← Complex.exp_add, ← Complex.exp_add]; simp [remZero]; ring_nf
        push_cast
        rw [e1, e2, mul_div_assoc', ← add_div, ← neg_div]
        congr 1
        linear_combination (cexp (-(s * t)) * cexp ((S.θSeq n : ℂ) * t)) * ecos
      · rw [if_neg ht, Set.indicator_of_notMem (show t ∉ Ici (S.A n) from ht),
          Complex.ofReal_zero, mul_zero]
    simp_rw [hind]
    rw [setIntegral_indicator measurableSet_Ici,
      inter_eq_right.mpr (Ici_subset_Ioi.mpr (S.A_pos n)),
      integral_Ici_eq_integral_Ioi]
  have hG_int : ∀ n : ℕ, Integrable (G n) (volume.restrict (Ioi 0)) := by
    intro n
    have hmeas : AEStronglyMeasurable (G n) (volume.restrict (Ioi 0)) :=
      ((continuous_cexp_neg_mul s).mul (Complex.continuous_ofReal.comp (S.continuous_wave n)))
        |>.aestronglyMeasurable
    have hdom : IntegrableOn
        (fun t : ℝ => (Ici (S.A n)).indicator (fun u : ℝ => 2 * Real.exp (-(δ * u))) t) (Ioi 0) := by
      have hi : IntegrableOn (fun u : ℝ => 2 * Real.exp (-(δ * u))) (Ici (S.A n)) := by
        rw [integrableOn_Ici_iff_integrableOn_Ioi]
        have h := exp_neg_integrableOn_Ioi (S.A n) hδ
        have hc : IntegrableOn (fun u : ℝ => 2 * Real.exp (-δ * u)) (Ioi (S.A n)) := h.const_mul 2
        exact hc.congr_fun (fun _ _ => by dsimp only; rw [neg_mul]) measurableSet_Ioi
      exact (hi.integrable_indicator measurableSet_Ici).restrict
    refine hdom.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    dsimp only [G, wave]
    by_cases ht : S.A n ≤ t
    · rw [if_pos ht, Set.indicator_of_mem (mem_Ici.mpr ht), norm_mul, norm_cexp_neg_mul_ofReal,
        Complex.norm_real, Real.norm_eq_abs, abs_div]
      have ht1 : 1 ≤ t := (by linarith [S.three_le_A n] : (1 : ℝ) ≤ S.A n).trans ht
      have ht0 : 0 < t := by linarith
      rw [abs_of_pos ht0, abs_mul, abs_mul, abs_neg, abs_of_pos two_pos,
        abs_of_pos (Real.exp_pos _)]
      have hc : |Real.cos (S.ω n * t)| ≤ 1 := Real.abs_cos_le_one _
      have hnum : 2 * Real.exp (S.θSeq n * t) * |Real.cos (S.ω n * t)| / t ≤
          2 * Real.exp (S.θ₂ * t) := by
        calc 2 * Real.exp (S.θSeq n * t) * |Real.cos (S.ω n * t)| / t
            ≤ 2 * Real.exp (S.θ₂ * t) * 1 / 1 := by
              refine div_le_div₀ (by positivity) ?_ zero_lt_one ht1
              exact mul_le_mul (mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (S.θSeq_le_θ₂ n) ht0.le)) two_pos.le)
                hc (abs_nonneg _) (by positivity)
          _ = 2 * Real.exp (S.θ₂ * t) := by ring
      calc Real.exp (-(s.re * t)) * (2 * Real.exp (S.θSeq n * t) * |Real.cos (S.ω n * t)| / t)
          ≤ Real.exp (-(s.re * t)) * (2 * Real.exp (S.θ₂ * t)) :=
            mul_le_mul_of_nonneg_left hnum (Real.exp_pos _).le
        _ = 2 * Real.exp (-(δ * t)) := by
            rw [mul_left_comm, ← Real.exp_add]; congr 2; dsimp only [δ]; ring
    · rw [if_neg ht, Set.indicator_of_notMem (show t ∉ Ici (S.A n) from ht),
        Complex.ofReal_zero, mul_zero, norm_zero]
  have hG_sum : Summable fun n : ℕ => ∫ t in Ioi (0 : ℝ), ‖G n t‖ := by
    have hgeom : Summable fun n : ℕ =>
        (2 * Real.exp (-(δ * (S.U₀ + 1))) / δ) * (Real.exp (-δ)) ^ n := by
      refine (summable_geometric_of_lt_one (Real.exp_pos _).le ?_).mul_left _
      exact Real.exp_lt_one_iff.mpr (by linarith)
    refine Summable.of_nonneg_of_le (fun _ => setIntegral_nonneg measurableSet_Ioi fun _ _ =>
      norm_nonneg _) (fun n => ?_) hgeom
    have hdom_int : ∫ t in Ioi (0 : ℝ),
        (Ici (S.A n)).indicator (fun u : ℝ => 2 * Real.exp (-(δ * u))) t =
        (2 * Real.exp (-(δ * (S.U₀ + 1))) / δ) * (Real.exp (-δ)) ^ n := by
      rw [setIntegral_indicator measurableSet_Ici,
        inter_eq_right.mpr (Ici_subset_Ioi.mpr (S.A_pos n)),
        integral_Ici_eq_integral_Ioi, integral_const_mul, integral_Ioi_exp_neg_mul hδ,
        ← Real.exp_nat_mul]
      have hex : -(δ * S.A n) = -(δ * (S.U₀ + 1)) + (n : ℝ) * (-δ) := by unfold A; ring
      rw [hex, Real.exp_add]
      ring
    rw [← hdom_int]
    have hdom : IntegrableOn
        (fun t : ℝ => (Ici (S.A n)).indicator (fun u : ℝ => 2 * Real.exp (-(δ * u))) t) (Ioi 0) := by
      have hi : IntegrableOn (fun u : ℝ => 2 * Real.exp (-(δ * u))) (Ici (S.A n)) := by
        rw [integrableOn_Ici_iff_integrableOn_Ioi]
        have h := exp_neg_integrableOn_Ioi (S.A n) hδ
        have hc : IntegrableOn (fun u : ℝ => 2 * Real.exp (-δ * u)) (Ioi (S.A n)) := h.const_mul 2
        exact hc.congr_fun (fun _ _ => by dsimp only; rw [neg_mul]) measurableSet_Ioi
      exact (hi.integrable_indicator measurableSet_Ici).restrict
    refine setIntegral_mono_on (hG_int n).norm hdom measurableSet_Ioi fun t _ => ?_
    dsimp only [G, wave]
    by_cases ht : S.A n ≤ t
    · rw [if_pos ht, Set.indicator_of_mem (mem_Ici.mpr ht), norm_mul, norm_cexp_neg_mul_ofReal,
        Complex.norm_real, Real.norm_eq_abs, abs_div]
      have ht1 : 1 ≤ t := (by linarith [S.three_le_A n] : (1 : ℝ) ≤ S.A n).trans ht
      have ht0 : 0 < t := by linarith
      rw [abs_of_pos ht0, abs_mul, abs_mul, abs_neg, abs_of_pos two_pos,
        abs_of_pos (Real.exp_pos _)]
      have hc : |Real.cos (S.ω n * t)| ≤ 1 := Real.abs_cos_le_one _
      have hnum : 2 * Real.exp (S.θSeq n * t) * |Real.cos (S.ω n * t)| / t ≤
          2 * Real.exp (S.θ₂ * t) := by
        calc 2 * Real.exp (S.θSeq n * t) * |Real.cos (S.ω n * t)| / t
            ≤ 2 * Real.exp (S.θ₂ * t) * 1 / 1 := by
              refine div_le_div₀ (by positivity) ?_ zero_lt_one ht1
              exact mul_le_mul (mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (S.θSeq_le_θ₂ n) ht0.le)) two_pos.le)
                hc (abs_nonneg _) (by positivity)
          _ = 2 * Real.exp (S.θ₂ * t) := by ring
      calc Real.exp (-(s.re * t)) * (2 * Real.exp (S.θSeq n * t) * |Real.cos (S.ω n * t)| / t)
          ≤ Real.exp (-(s.re * t)) * (2 * Real.exp (S.θ₂ * t)) :=
            mul_le_mul_of_nonneg_left hnum (Real.exp_pos _).le
        _ = 2 * Real.exp (-(δ * t)) := by
            rw [mul_left_comm, ← Real.exp_add]; congr 2; dsimp only [δ]; ring
    · rw [if_neg ht, Set.indicator_of_notMem (show t ∉ Ici (S.A n) from ht),
        Complex.ofReal_zero, mul_zero, norm_zero]
  have hswap := integral_tsum_of_summable_integral_norm hG_int hG_sum
  have hφ_sum : Summable φ := by
    refine Summable.of_norm_bounded hG_sum fun n => ?_
    rw [← hG_eq n]
    exact norm_integral_le_integral_norm _
  have hpt : ∀ t : ℝ, (∑' n : ℕ, G n t) = cexp (-(s * t)) * (S.wRem t : ℂ) := by
    intro t
    dsimp only [G, wRem]
    rw [Complex.ofReal_tsum, ← tsum_mul_left]
  have hrem_patch0 : S.remFactor s = S.patch 0 s := by
    change S.patch K s = S.patch 0 s
    unfold patch
    rw [Finset.range_zero, Finset.prod_empty, one_mul,
      Finset.prod_congr rfl fun n hn => hK n (Finset.mem_range.mp hn), ← Complex.exp_sum,
      ← Complex.exp_add]
    congr 1
    exact hφ_sum.sum_add_tsum_nat_add K
  rw [hrem_patch0]
  unfold patch
  rw [Finset.range_zero, Finset.prod_empty, one_mul]
  congr 1
  calc (∑' m : ℕ, φ m) = ∑' m : ℕ, ∫ t in Ioi (0 : ℝ), G m t := tsum_congr fun m => (hG_eq m).symm
    _ = ∫ t in Ioi (0 : ℝ), ∑' m : ℕ, G m t := hswap
    _ = ∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (S.wRem t : ℂ) := by simp_rw [hpt]

/-! ### Prime-square quantile discretization and integer-norm rounding -/

/-- Continuous distribution `W(x) = ∫_{(0, x]} w`. -/
def W (x : ℝ) : ℝ := distribution S.w x

/-- `w` extended by `0` outside `(0, ∞)`. -/
def wt : ℝ → ℝ := (Ioi (0 : ℝ)).indicator S.w

theorem integrableOn_exp_mul_w {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun u : ℝ => Real.exp (-(σ * u)) * S.w u) (Ioi 0) := by
  have hdom := (S.P.integrableOn_exp_mul_w hσ).const_mul (5 / 4 : ℝ)
  have hmeas : AEStronglyMeasurable (fun u : ℝ => Real.exp (-(σ * u)) * S.w u)
      (volume.restrict (Ioi 0)) :=
    ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(σ * u))).measurable.mul S.measurable_w)
      |>.aestronglyMeasurable
  refine hdom.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (S.w_pos hu).le)]
  have hb := (S.w_bounds hu).2
  nlinarith [Real.exp_pos (-(σ * u))]

theorem integrableOn_w_Ioc (b : ℝ) : IntegrableOn S.w (Ioc 0 b) := by
  have h := (S.integrableOn_exp_mul_w (σ := 2) (by norm_num)).mono_set
    (Ioc_subset_Ioi_self : Ioc (0 : ℝ) b ⊆ Ioi 0)
  have hIcc : IntegrableOn (fun u => Real.exp (-(2 * u)) * S.w u) (Icc 0 b) :=
    Iff.mpr integrableOn_Icc_iff_integrableOn_Ioc h
  have hc : ContinuousOn (fun u : ℝ => Real.exp (2 * u)) (Icc 0 b) := by fun_prop
  have h2 := (hIcc.mul_continuousOn hc isCompact_Icc).mono_set Ioc_subset_Icc_self
  refine h2.congr_fun (fun u _ => ?_) measurableSet_Ioc
  show Real.exp (-(2 * u)) * S.w u * Real.exp (2 * u) = S.w u
  rw [mul_right_comm, ← Real.exp_add]; simp

theorem integrableOn_wt_Icc (b : ℝ) : IntegrableOn S.wt (Icc 0 b) := by
  refine Iff.mpr integrableOn_Icc_iff_integrableOn_Ioc ?_
  refine (S.integrableOn_w_Ioc b).congr_fun (fun u hu => ?_) measurableSet_Ioc
  simp [wt, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu.1)]

theorem W_eq_intervalIntegral {x : ℝ} (hx : 0 ≤ x) : S.W x = ∫ u in (0 : ℝ)..x, S.wt u := by
  rw [intervalIntegral.integral_of_le hx, W, distribution]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  simp [wt, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu.1)]

theorem W_of_nonpos {x : ℝ} (hx : x ≤ 0) : S.W x = 0 := by
  rw [W, distribution, Ioc_eq_empty (not_lt.mpr hx)]; simp

theorem W_nonneg (x : ℝ) : 0 ≤ S.W x :=
  setIntegral_nonneg measurableSet_Ioc fun _ hu => (S.w_pos hu.1).le

theorem intervalIntegrable_wt {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable S.wt volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    ((S.integrableOn_wt_Icc b).mono_set (Icc_subset_Icc_left ha))

theorem continuousOn_W {M : ℝ} (hM : 0 ≤ M) : ContinuousOn S.W (Icc 0 M) := by
  have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := M)
    (f := S.wt) (by rw [uIcc_of_le hM]; exact S.integrableOn_wt_Icc M)
  rw [uIcc_of_le hM] at h
  exact h.congr fun x hx => S.W_eq_intervalIntegral hx.1

theorem W_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : S.W a < S.W b := by
  rw [S.W_eq_intervalIntegral ha, S.W_eq_intervalIntegral (ha.trans hab.le)]
  have hpos : 0 < ∫ u in a..b, S.wt u := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (S.intervalIntegrable_wt ha hab.le)
      (fun u hu => ?_) hab
    have hu0 : 0 < u := lt_of_le_of_lt ha hu.1
    simp only [wt, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu0)]
    exact S.w_pos hu0
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (S.intervalIntegrable_wt le_rfl ha) (S.intervalIntegrable_wt ha hab.le)
  linarith

theorem W_le_W {a b : ℝ} (hab : a ≤ b) : S.W a ≤ S.W b := by
  rcases le_or_gt a 0 with ha | ha
  · rw [S.W_of_nonpos ha]; exact S.W_nonneg b
  · rcases hab.lt_or_eq with h | rfl
    · exact (S.W_lt ha.le h).le
    · exact le_rfl

theorem three_quarters_PW_le_W (x : ℝ) : (3 / 4) * S.P.W x ≤ S.W x := by
  rw [W, Params.W, distribution, distribution, ← integral_const_mul]
  exact setIntegral_mono_on ((S.P.integrableOn_w_Ioc x).const_mul _) (S.integrableOn_w_Ioc x)
    measurableSet_Ioc fun u hu => (S.w_bounds hu.1).1

theorem W_le_exp {b : ℝ} (hb : 1 < b) (x : ℝ) :
    S.W x ≤ Real.exp (b * x) * ∫ u in Ioi (0 : ℝ), Real.exp (-(b * u)) * S.w u := by
  have hint := S.integrableOn_exp_mul_w hb
  have hstep : S.W x ≤ ∫ u in Ioc 0 x, Real.exp (b * x) * (Real.exp (-(b * u)) * S.w u) := by
    refine setIntegral_mono_on (S.integrableOn_w_Ioc x)
      ((hint.mono_set Ioc_subset_Ioi_self).const_mul _) measurableSet_Ioc fun u hu => ?_
    have hw := (S.w_pos hu.1).le
    have he : 1 ≤ Real.exp (b * x) * Real.exp (-(b * u)) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith [hu.2])
    nlinarith
  rw [integral_const_mul] at hstep
  refine hstep.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  refine setIntegral_mono_set hint ?_ (Eventually.of_forall Ioc_subset_Ioi_self)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact mul_nonneg (Real.exp_pos _).le (S.w_pos hu).le

/-- Threshold `u₁ = 2 log(9 / c₀) + 2` beyond which `w(u) - w(u/2)/4 > 0`. -/
def u₁ : ℝ := 2 * Real.log (9 / S.c₀) + 2

theorem two_le_u₁ : 2 ≤ S.u₁ := by
  have h : 1 ≤ 9 / S.c₀ := by rw [le_div_iff₀ S.c₀_pos]; linarith [S.c₀_le_one]
  unfold u₁
  linarith [Real.log_nonneg h]

theorem correctedDensity_pos {u : ℝ} (hu : S.u₁ ≤ u) : 0 < S.w u - S.w (u / 2) / 4 := by
  have hc0 := S.c₀_pos
  have hu2 : 2 ≤ u := S.two_le_u₁.trans hu
  have hu0 : 0 < u := by linarith
  let y : ℝ := Real.exp (u / 2)
  have hy0 : 0 < y := Real.exp_pos _
  have hyy : Real.exp u = y * y := by dsimp only [y]; rw [← Real.exp_add]; congr 1; ring
  have hcy : 9 ≤ S.c₀ * y := by
    have h9 : 9 / S.c₀ ≤ y := by
      have hlog : Real.log (9 / S.c₀) ≤ u / 2 := by unfold u₁ at hu; linarith
      calc 9 / S.c₀ = Real.exp (Real.log (9 / S.c₀)) := (Real.exp_log (by positivity)).symm
        _ ≤ y := Real.exp_le_exp.mpr hlog
    rwa [div_le_iff₀ hc0, mul_comm] at h9
  have hlow : (3 / 4) * (S.c₀ * (y * y) / u) ≤ S.w u := by
    have h1 := S.P.w_ge (t := u) (by linarith)
    rw [← hyy]
    exact (mul_le_mul_of_nonneg_left h1 (by norm_num)).trans (S.w_bounds hu0).1
  have hup : S.w (u / 2) ≤ (5 / 4) * (5 * y / (u / 2)) := by
    have h2 := S.P.w_le (t := u / 2) (by linarith)
    exact (S.w_bounds (by linarith)).2.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))
  have key : (5 / 4) * (5 * y / (u / 2)) / 4 < (3 / 4) * (S.c₀ * (y * y) / u) := by
    rw [mul_div_assoc', mul_div_assoc', div_div, div_lt_div_iff₀ (by positivity) hu0]
    nlinarith [mul_le_mul_of_nonneg_left hcy (mul_pos hy0 hu0).le, mul_pos hy0 hu0]
  linarith

/-- Prime-square corrected count `V(x) = W(x) - W(x/2)/2 + W(min(x, u₁)/2)/2`. -/
def V (x : ℝ) : ℝ := S.W x - S.W (x / 2) / 2 + S.W (min x S.u₁ / 2) / 2

theorem V_of_le {x : ℝ} (hx : x ≤ S.u₁) : S.V x = S.W x := by
  rw [V, min_eq_left hx]; ring

theorem V_of_ge {x : ℝ} (hx : S.u₁ ≤ x) :
    S.V x = S.W x - S.W (x / 2) / 2 + S.W (S.u₁ / 2) / 2 := by
  rw [V, min_eq_right hx]

theorem W_half_le (x : ℝ) : S.W (x / 2) ≤ S.W x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [S.W_of_nonpos (by linarith), S.W_of_nonpos hx]
  · exact S.W_le_W (by linarith)

theorem half_W_le_V (x : ℝ) : S.W x / 2 ≤ S.V x := by
  have h1 := S.W_half_le x
  have h2 := S.W_nonneg (min x S.u₁ / 2)
  rw [V]; linarith

theorem V_le_W (x : ℝ) : S.V x ≤ S.W x := by
  have h1 : S.W (min x S.u₁ / 2) ≤ S.W (x / 2) := S.W_le_W (by linarith [min_le_left x S.u₁])
  rw [V]; linarith

theorem V_nonneg (x : ℝ) : 0 ≤ S.V x := by
  linarith [S.half_W_le_V x, S.W_nonneg x]

theorem V_of_nonpos {x : ℝ} (hx : x ≤ 0) : S.V x = 0 := by
  rw [S.V_of_le (by linarith [S.two_le_u₁]), S.W_of_nonpos hx]

theorem W_sub_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    S.W b - S.W a = ∫ u in a..b, S.w u := by
  rw [S.W_eq_intervalIntegral (by linarith), S.W_eq_intervalIntegral ha.le,
    intervalIntegral.integral_interval_sub_left (S.intervalIntegrable_wt le_rfl (by linarith))
      (S.intervalIntegrable_wt le_rfl ha.le)]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hab] at hu
  simp [wt, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from lt_of_lt_of_le ha hu.1)]

theorem V_sub_of_ge {a b : ℝ} (ha : S.u₁ ≤ a) (hab : a ≤ b) :
    S.V b - S.V a = ∫ u in a..b, (S.w u - S.w (u / 2) / 4) := by
  have ha0 : 0 < a := by linarith [S.two_le_u₁]
  have hcw : ContinuousOn S.w (uIcc a b) :=
    S.continuousOn_w.mono fun u hu => by
      rw [uIcc_of_le hab] at hu; exact lt_of_lt_of_le ha0 hu.1
  have hcw2 : ContinuousOn (fun u => S.w (u / 2)) (uIcc a b) :=
    S.continuousOn_w.comp (continuousOn_id.div_const 2) fun u hu => by
      rw [uIcc_of_le hab] at hu; show 0 < u / 2; linarith [hu.1]
  have hi1 : IntervalIntegrable S.w volume a b := hcw.intervalIntegrable
  have hi2 : IntervalIntegrable (fun u => S.w (u / 2) / 4) volume a b :=
    (hcw2.div_const 4).intervalIntegrable
  have hhalf : S.W (b / 2) - S.W (a / 2) = (∫ u in a..b, S.w (u / 2)) / 2 := by
    rw [S.W_sub_eq (by linarith) (by linarith), intervalIntegral.integral_comp_div
      (fun u => S.w u) (two_ne_zero : (2 : ℝ) ≠ 0), smul_eq_mul]
    ring
  rw [S.V_of_ge (ha.trans hab), S.V_of_ge ha, intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_div, ← S.W_sub_eq ha0 hab]
  linarith

theorem V_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : S.V a < S.V b := by
  have hlow : ∀ {a b : ℝ}, 0 ≤ a → a < b → b ≤ S.u₁ → S.V a < S.V b := by
    intro a b ha hab hb
    rw [S.V_of_le (by linarith), S.V_of_le hb]
    exact S.W_lt ha hab
  have hhigh : ∀ {a b : ℝ}, S.u₁ ≤ a → a < b → S.V a < S.V b := by
    intro a b ha hab
    have h := S.V_sub_of_ge ha hab.le
    have hpos : 0 < ∫ u in a..b, (S.w u - S.w (u / 2) / 4) := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_
        (fun u hu => S.correctedDensity_pos (by linarith [hu.1])) hab
      have ha0 : 0 < a := by linarith [S.two_le_u₁]
      have hc : ContinuousOn (fun u => S.w u - S.w (u / 2) / 4) (uIcc a b) := by
        refine (S.continuousOn_w.mono fun u hu => ?_).sub
          ((S.continuousOn_w.comp (continuousOn_id.div_const 2) fun u hu => ?_).div_const 4)
        · rw [uIcc_of_le hab.le] at hu; exact lt_of_lt_of_le ha0 hu.1
        · rw [uIcc_of_le hab.le] at hu; show 0 < u / 2; linarith [hu.1]
      exact hc.intervalIntegrable
    linarith
  by_cases hb : b ≤ S.u₁
  · exact hlow ha hab hb
  · push Not at hb
    by_cases ha' : S.u₁ ≤ a
    · exact hhigh ha' hab
    · push Not at ha'
      exact (hlow ha ha' le_rfl).trans (hhigh le_rfl hb)

theorem V_le_V {a b : ℝ} (hab : a ≤ b) : S.V a ≤ S.V b := by
  rcases le_or_gt a 0 with ha | ha
  · rw [S.V_of_nonpos ha]; exact S.V_nonneg b
  · rcases hab.lt_or_eq with h | rfl
    · exact (S.V_lt ha.le h).le
    · exact le_rfl

theorem continuousOn_V {M : ℝ} (hM : 0 ≤ M) : ContinuousOn S.V (Icc 0 M) := by
  have hW := S.continuousOn_W hM
  have h2 : ContinuousOn (fun x => S.W (x / 2)) (Icc 0 M) :=
    hW.comp (continuousOn_id.div_const 2) fun x hx =>
      ⟨by show 0 ≤ x / 2; linarith [hx.1], by show x / 2 ≤ M; linarith [hx.1, hx.2]⟩
  have h3 : ContinuousOn (fun x => S.W (min x S.u₁ / 2)) (Icc 0 M) :=
    hW.comp ((continuous_id.min continuous_const).continuousOn.div_const 2) fun x hx => by
      have hu := S.two_le_u₁
      have h1 : min x S.u₁ ≤ x := min_le_left _ _
      have h0 : 0 ≤ min x S.u₁ := le_min hx.1 (by linarith)
      exact ⟨by show 0 ≤ min x S.u₁ / 2; linarith,
        by show min x S.u₁ / 2 ≤ M; linarith [hx.2]⟩
  exact (hW.sub (h2.div_const 2)).add (h3.div_const 2)

theorem exists_catom (k : ℕ) : ∃ x, 0 < x ∧ S.V x = k + 1 := by
  have hc0 := S.c₀_pos
  let B : ℝ := 1 + 8 * ((k : ℝ) + 1) / (3 * S.c₀)
  have hB1 : 1 ≤ B := by dsimp only [B]; linarith [show (0 : ℝ) ≤ 8 * (k + 1) / (3 * S.c₀) by positivity]
  have hVB : (k : ℝ) + 1 ≤ S.V B := by
    have h1 := S.P.W_ge hB1
    have h2 := S.three_quarters_PW_le_W B
    have h3 := S.half_W_le_V B
    have heq : (3 / 8 : ℝ) * (S.c₀ * (B - 1)) = (k : ℝ) + 1 := by
      dsimp only [B]; field_simp; ring
    change S.c₀ * (B - 1) ≤ S.P.W B at h1
    linarith
  obtain ⟨x, hx, hVx⟩ := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ B)
    (S.continuousOn_V (by linarith)) ⟨by rw [S.V_of_nonpos le_rfl]; positivity, hVB⟩
  refine ⟨x, ?_, hVx⟩
  rcases hx.1.lt_or_eq with h | h
  · exact h
  · rw [← h, S.V_of_nonpos le_rfl] at hVx
    have : (0 : ℝ) < k + 1 := by positivity
    linarith

/-- `k`-th discrete logarithmic prime `t_k` with `V(t_k) = k + 1`. -/
def catom (k : ℕ) : ℝ := (S.exists_catom k).choose

theorem catom_pos (k : ℕ) : 0 < S.catom k := (S.exists_catom k).choose_spec.1
theorem V_catom (k : ℕ) : S.V (S.catom k) = k + 1 := (S.exists_catom k).choose_spec.2

theorem catom_le_iff (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : S.catom k ≤ x ↔ (k : ℝ) + 1 ≤ S.V x := by
  constructor
  · intro h; rw [← S.V_catom k]; exact S.V_le_V h
  · intro h
    by_contra hlt
    have := S.V_lt hx (not_le.mp hlt)
    rw [S.V_catom] at this
    linarith

theorem catom_strictMono : StrictMono S.catom := by
  intro j k hjk
  by_contra hle
  have h := S.V_le_V (not_lt.mp hle)
  rw [S.V_catom, S.V_catom] at h
  have : (j : ℝ) < k := by exact_mod_cast hjk
  linarith

theorem catom_zero_le (k : ℕ) : S.catom 0 ≤ S.catom k :=
  S.catom_strictMono.monotone (Nat.zero_le k)

theorem catomCount_eq (x : ℝ) : atomCount S.catom x = (⌊S.V x⌋₊ : ℝ) := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [S.V_of_nonpos hx.le, atomCount]
    simp only [Nat.floor_zero, Nat.cast_zero]
    convert tsum_zero with k
    rw [if_neg (not_le.mpr (lt_trans hx (S.catom_pos k)))]
  · have hiff : ∀ k : ℕ, S.catom k ≤ x ↔ k < ⌊S.V x⌋₊ := fun k => by
      rw [S.catom_le_iff k hx, Nat.lt_iff_add_one_le, Nat.le_floor_iff (S.V_nonneg x)]
      push_cast; rfl
    rw [atomCount, tsum_eq_sum (s := Finset.range ⌊S.V x⌋₊) fun k hk => by
      rw [if_neg (by rw [hiff]; simpa using hk)]]
    rw [Finset.sum_congr rfl fun k hk => if_pos ((hiff k).mpr (Finset.mem_range.mp hk))]
    simp

theorem summable_exp_catom {a : ℝ} (ha : 1 < a) :
    Summable fun k => Real.exp (-(a * S.catom k)) := by
  refine summable_exp_of_count (fun b hb => ?_) ha
  refine ⟨∫ u in Ioi (0 : ℝ), Real.exp (-(b * u)) * S.w u,
    setIntegral_nonneg measurableSet_Ioi fun u hu => mul_nonneg (Real.exp_pos _).le (S.w_pos hu).le,
    fun k => ?_⟩
  have h := S.W_le_exp hb (S.catom k)
  have h2 := S.V_le_W (S.catom k)
  rw [S.V_catom] at h2
  linarith

/-- Discrepancy `N(x) - (W(x) - W(x/2)/2)`. -/
def cerror (x : ℝ) : ℝ := atomCount S.catom x - (S.W x - S.W (x / 2) / 2)

/-- Discrepancy bound `1 + W(u₁ / 2) / 2`. -/
def cbound : ℝ := 1 + S.W (S.u₁ / 2) / 2

theorem cbound_pos : 0 < S.cbound := by unfold cbound; linarith [S.W_nonneg (S.u₁ / 2)]

theorem abs_cerror_le (x : ℝ) : |S.cerror x| ≤ S.cbound := by
  have h1 := Nat.floor_le (S.V_nonneg x)
  have h2 := Nat.lt_floor_add_one (S.V x)
  have h3 := S.W_nonneg (min x S.u₁ / 2)
  have h4 : S.W (min x S.u₁ / 2) ≤ S.W (S.u₁ / 2) :=
    S.W_le_W (by linarith [min_le_right x S.u₁])
  have hV : S.V x = S.W x - S.W (x / 2) / 2 + S.W (min x S.u₁ / 2) / 2 := rfl
  rw [cerror, S.catomCount_eq, cbound, abs_le]
  constructor <;> linarith

theorem measurable_cerror : Measurable S.cerror := by
  have hW : Monotone S.W := fun _ _ h => S.W_le_W h
  have hW2 : Monotone fun x => S.W (x / 2) := fun _ _ h => S.W_le_W (by linarith)
  have hF : Monotone fun x => (⌊S.V x⌋₊ : ℝ) := fun _ _ h =>
    Nat.cast_le.mpr (Nat.floor_le_floor (S.V_le_V h))
  have heq : S.cerror = fun x => (⌊S.V x⌋₊ : ℝ) - (S.W x - S.W (x / 2) / 2) := by
    funext x; rw [cerror, S.catomCount_eq]
  rw [heq]
  exact hF.measurable.sub (hW.measurable.sub (hW2.measurable.div_const 2))

/-- Continuous Laplace transform `L(z) = ∫_{u > 0} e^{-z u} w(u) du`. -/
def logZeta (z : ℂ) : ℂ := ∫ u in Ioi (0 : ℝ), cexp (-(z * u)) * (S.w u : ℂ)

theorem logZeta_eq {z : ℂ} (hz : 1 < z.re) :
    IntegrableOn (fun x : ℝ => cexp (-(z * x)) * (S.W x : ℂ)) (Ioi 0) ∧
      S.logZeta z = z * ∫ x in Ioi (0 : ℝ), cexp (-(z * x)) * (S.W x : ℂ) :=
  integral_cexp_density S.measurable_w (fun _ hu => (S.w_pos hu).le) (by linarith)
    (S.integrableOn_exp_mul_w hz)

theorem measurable_W : Measurable S.W := Monotone.measurable fun _ _ h => S.W_le_W h

theorem differentiableOn_logZeta : DifferentiableOn ℂ S.logZeta {z : ℂ | 1 < z.re} := by
  intro z₀ hz₀
  have hz₀' : 1 < z₀.re := hz₀
  let b : ℝ := (1 + z₀.re) / 2
  have hb1 : 1 < b := by dsimp only [b]; linarith
  let C : ℝ := ∫ u in Ioi (0 : ℝ), Real.exp (-(b * u)) * S.w u
  have hC0 : 0 ≤ C := setIntegral_nonneg measurableSet_Ioi fun u hu =>
    mul_nonneg (Real.exp_pos _).le (S.w_pos hu).le
  let E : ℝ → ℝ := fun x => S.W x * Real.exp (-(b * x))
  have hEm : Measurable E := S.measurable_W.mul (by fun_prop)
  have hEb : ∀ x, |E x| ≤ C + 1 := by
    intro x
    have h := S.W_le_exp hb1 x
    have he : Real.exp (b * x) * Real.exp (-(b * x)) = 1 := by rw [← Real.exp_add]; simp
    have hW0 := S.W_nonneg x
    have hEx : E x ≤ C := by dsimp only [E, C]; nlinarith [Real.exp_pos (-(b * x)), Real.exp_pos (b * x)]
    rw [abs_of_nonneg (mul_nonneg hW0 (Real.exp_pos _).le)]
    linarith
  let g : ℂ → ℂ := fun z => z * boundedLaplace E (z - b)
  have hU : IsOpen {z : ℂ | b < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hz₀U : z₀ ∈ {z : ℂ | b < z.re} := by show b < z₀.re; dsimp only [b]; linarith
  have heq : S.logZeta =ᶠ[𝓝 z₀] g := by
    filter_upwards [hU.mem_nhds hz₀U] with z hz
    have hz' : b < z.re := hz
    rw [(S.logZeta_eq (by linarith)).2]
    dsimp only [g]
    congr 1
    unfold boundedLaplace
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    dsimp only [E]; push_cast
    have hsp : cexp (-(z * x)) = cexp (-((z - b) * x)) * cexp (-(b * x)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [hsp]; ring
  have hgd : DifferentiableAt ℂ g z₀ := by
    have hL := (differentiableOn_boundedLaplace_of_le hEm (by linarith : (0 : ℝ) < C + 1)
      hEb).differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (0 : ℝ) < (z₀ - (b : ℂ)).re by simp [b]; linarith))
    have hsub : DifferentiableAt ℂ (fun z : ℂ => z - (b : ℂ)) z₀ :=
      differentiableAt_id.sub_const _
    have hcomp := DifferentiableAt.comp (𝕜 := ℂ) (g := boundedLaplace E)
      (f := fun z : ℂ => z - (b : ℂ)) z₀ hL hsub
    exact differentiableAt_id.mul hcomp
  exact (hgd.congr_of_eventuallyEq heq).differentiableWithinAt

private theorem integral_cexp_W_half (z : ℂ) :
    ∫ x in Ioi (0 : ℝ), cexp (-(z * x)) * (S.W (x / 2) : ℂ) =
      2 * ∫ y in Ioi (0 : ℝ), cexp (-((2 * z) * y)) * (S.W y : ℂ) := by
  have h := integral_comp_mul_left_Ioi
    (fun y : ℝ => cexp (-((2 * z) * y)) * (S.W y : ℂ)) 0 (by norm_num : (0 : ℝ) < 1 / 2)
  simp only [mul_zero] at h
  rw [show ((1 / 2 : ℝ))⁻¹ = 2 by norm_num] at h
  rw [show (2 : ℂ) * ∫ y in Ioi (0 : ℝ), cexp (-((2 * z) * y)) * (S.W y : ℂ) =
      (2 : ℝ) • ∫ y in Ioi (0 : ℝ), cexp (-((2 * z) * y)) * (S.W y : ℂ) by
    rw [Complex.real_smul]; push_cast; ring, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [show (1 / 2 * x : ℝ) = x / 2 by ring]; push_cast
  rw [show -(2 * z * ((x : ℂ) / 2)) = -(z * x) by ring]

private theorem mul_integral_cexp_catomCount {z : ℂ} (hz : 1 < z.re) :
    z * ∫ x in Ioi (0 : ℝ), cexp (-(z * x)) * (atomCount S.catom x : ℂ) =
      z * boundedLaplace S.cerror z + S.logZeta z - S.logZeta (2 * z) / 2 := by
  obtain ⟨hWint, hL1⟩ := S.logZeta_eq hz
  have hz2 : 1 < (2 * z).re := by simp; linarith
  obtain ⟨-, hL2⟩ := S.logZeta_eq hz2
  have hEint : IntegrableOn (fun x : ℝ => cexp (-(z * x)) * (S.cerror x : ℂ)) (Ioi 0) := by
    have hb : IntegrableOn (fun x : ℝ => S.cbound * Real.exp (-z.re * x)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 (by linarith : 0 < z.re)).const_mul _
    refine hb.mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact ((by fun_prop : Continuous fun x : ℝ => cexp (-(z * x))).measurable.mul
        (Complex.measurable_ofReal.comp S.measurable_cerror)).aestronglyMeasurable
    · rw [norm_mul, norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs,
        show -z.re * x = -(z.re * x) by ring, mul_comm]
      exact mul_le_mul_of_nonneg_right (S.abs_cerror_le x) (Real.exp_pos _).le
  have hW2int : IntegrableOn (fun x : ℝ => cexp (-(z * x)) * (S.W (x / 2) : ℂ)) (Ioi 0) := by
    refine hWint.norm.mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact ((by fun_prop : Continuous fun x : ℝ => cexp (-(z * x))).measurable.mul
        (Complex.measurable_ofReal.comp (S.measurable_W.comp
          (measurable_id.div_const 2)))).aestronglyMeasurable
    · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (S.W_nonneg _), abs_of_nonneg (S.W_nonneg _)]
      exact mul_le_mul_of_nonneg_left (S.W_half_le x) (norm_nonneg _)
  have hsplit : ∫ x in Ioi (0 : ℝ), cexp (-(z * x)) * (atomCount S.catom x : ℂ) =
      boundedLaplace S.cerror z + (∫ x in Ioi (0 : ℝ), cexp (-(z * x)) * (S.W x : ℂ)) -
        (∫ x in Ioi (0 : ℝ), cexp (-(z * x)) * (S.W (x / 2) : ℂ)) / 2 := by
    have hAB : IntegrableOn (fun x : ℝ =>
        cexp (-(z * x)) * (S.cerror x : ℂ) + cexp (-(z * x)) * (S.W x : ℂ)) (Ioi 0) :=
      hEint.add hWint
    have hC : IntegrableOn (fun x : ℝ =>
        cexp (-(z * x)) * (S.W (x / 2) : ℂ) / 2) (Ioi 0) :=
      hW2int.div_const 2
    have hpt : (fun x : ℝ => cexp (-(z * x)) * (atomCount S.catom x : ℂ)) = fun x : ℝ =>
        (cexp (-(z * x)) * (S.cerror x : ℂ) + cexp (-(z * x)) * (S.W x : ℂ)) -
          cexp (-(z * x)) * (S.W (x / 2) : ℂ) / 2 := by
      funext x; simp only [cerror]; push_cast; ring
    rw [hpt, integral_sub hAB hC, integral_add hEint hWint, integral_div, boundedLaplace]
  rw [hsplit, S.integral_cexp_W_half, hL1, hL2]
  ring

private theorem cexp_logZeta_eq {s : ℂ} (hs : 1 < s.re) :
    cexp (S.logZeta s) = overRegularZeta S.P.μ S.P.ν S.P.γ s * S.remFactor s := by
  have hi_tot : IntegrableOn (fun u : ℝ => cexp (-(s * u)) * (S.w u : ℂ)) (Ioi 0) := by
    refine (S.integrableOn_exp_mul_w hs).mono' ?_ ?_
    · exact ((continuous_cexp_neg_mul s).measurable.mul
        (Complex.measurable_ofReal.comp S.measurable_w)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [norm_mul, norm_cexp_neg_mul_ofReal, Complex.norm_real,
        Real.norm_of_nonneg (S.w_pos hu).le]
  have hi_P := S.P.integrableOn_cexp_mul_w hs
  have hi_rem : IntegrableOn (fun u : ℝ => cexp (-(s * u)) * (S.wRem u : ℂ)) (Ioi 0) := by
    refine (hi_tot.sub hi_P).congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [w, Pi.sub_apply]; push_cast; ring
  have hadd : S.logZeta s = S.P.logZeta s +
      ∫ u in Ioi (0 : ℝ), cexp (-(s * u)) * (S.wRem u : ℂ) := by
    unfold logZeta Params.logZeta
    rw [← integral_add hi_P hi_rem]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [w]; push_cast; ring
  rw [hadd, Complex.exp_add, S.remFactor_eq_cexp_integral hs]
  congr 1
  exact cexp_integral_primeDensity S.P.hlow S.P.hhigh S.P.h4 hs

/-- Natural-number norms `q_k = ⌈e^{t_k}⌉₊ ≥ 2` of the two-scale discrete primes. -/
def cPrimeNorm (k : ℕ) : ℕ := ⌈Real.exp (S.catom k)⌉₊

/-- Logarithmic norms `log q_k`. -/
def cRounded (k : ℕ) : ℝ := Real.log (S.cPrimeNorm k)

theorem cPrimeNorm_ge_two (k : ℕ) : 2 ≤ S.cPrimeNorm k := by
  have h : (1 : ℝ) < S.cPrimeNorm k :=
    (Real.one_lt_exp_iff.mpr (S.catom_pos k)).trans_le (Nat.le_ceil _)
  exact_mod_cast h

theorem catom_le_cRounded (k : ℕ) : S.catom k ≤ S.cRounded k := (roundedLog_bounds (S.catom k)).1
theorem cRounded_le (k : ℕ) : S.cRounded k ≤ S.catom k + Real.exp (-(S.catom k)) :=
  (roundedLog_bounds (S.catom k)).2
theorem cRounded_pos (k : ℕ) : 0 < S.cRounded k :=
  (S.catom_pos k).trans_le (S.catom_le_cRounded k)
theorem cRounded_zero_le (k : ℕ) : S.cRounded 0 ≤ S.cRounded k :=
  roundedLog_mono (S.catom_zero_le k)

theorem summable_exp_cRounded {a : ℝ} (ha : 1 < a) :
    Summable fun k => Real.exp (-(a * S.cRounded k)) := by
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun k => ?_)
    (S.summable_exp_catom ha)
  exact Real.exp_le_exp.mpr (by nlinarith only [ha, S.catom_le_cRounded k, S.catom_pos k])

/-- Integer-rounding correction exponent. -/
def roundingExponent (s : ℂ) : ℂ :=
  primeCorrection S.catom S.cRounded s + primeCorrection S.catom S.cRounded (2 * s) / 2 +
    primeCubeRemainder S.cRounded s - primeCubeRemainder S.catom s

/-- Discretization + rounding analytic exponent on `Re s > 1/3`. -/
def analyticExponent (s : ℂ) : ℂ :=
  -(S.logZeta (4 * s)) / 4 + s * boundedLaplace S.cerror s +
    s * boundedLaplace S.cerror (2 * s) + primeCubeRemainder S.catom s + S.roundingExponent s

/-- Analytic continuation of the two-scale integer-norm Euler product to `{Re s > 1/3, s ≠ 1}`. -/
def crContinuation (s : ℂ) : ℂ :=
  overRegularZeta S.P.μ S.P.ν S.P.γ s * S.remFactor s * cexp (S.analyticExponent s)

/-- Holomorphic pole-cleared numerator `H(s) = (s - 1) F(s)` on `{Re s > 1/3}`. -/
def crPoleFactor (s : ℂ) : ℂ :=
  (((s - (1 - S.P.μ)) ^ 2 + (S.P.γ : ℂ) ^ 2) * (s + (4 * S.P.μ - 1)) /
    ((s + (3 * S.P.μ - 1 - S.P.ν)) * (s + (3 * S.P.μ - 1 + S.P.ν)))) *
    S.remFactor s * cexp (S.analyticExponent s)

theorem genEulerLog_eq_crContinuation {s : ℂ} (hs : 1 < s.re) :
    cexp (genEulerLog S.cPrimeNorm s) = S.crContinuation s := by
  have hs0 : 0 < s.re := by linarith
  have hs2 : 1 < (2 * s).re := by simp; linarith
  obtain ⟨ht1, _⟩ := summable_neg_log S.catom_pos S.catom_zero_le
    (fun a ha => S.summable_exp_catom ha) hs
  obtain ⟨hu1, _⟩ := summable_neg_log S.cRounded_pos S.cRounded_zero_le
    (fun a ha => S.summable_exp_cRounded ha) hs
  obtain ⟨ht2, _⟩ := summable_neg_log S.catom_pos S.catom_zero_le
    (fun a ha => S.summable_exp_catom ha) hs2
  obtain ⟨hu2, _⟩ := summable_neg_log S.cRounded_pos S.cRounded_zero_le
    (fun a ha => S.summable_exp_cRounded ha) hs2
  have hc1 : primeCorrection S.catom S.cRounded s =
      (∑' k, cexp (-(s * S.cRounded k))) - ∑' k, cexp (-(s * S.catom k)) := hu1.tsum_sub ht1
  have hc2 : primeCorrection S.catom S.cRounded (2 * s) =
      (∑' k, cexp (-((2 * s) * S.cRounded k))) - ∑' k, cexp (-((2 * s) * S.catom k)) :=
    hu2.tsum_sub ht2
  have hd1 := tsum_cexp_atoms S.catom_pos hs0 (S.summable_exp_catom hs)
  have hd2 := tsum_cexp_atoms S.catom_pos (by linarith : 0 < (2 * s).re)
    (S.summable_exp_catom hs2)
  have hN1 := S.mul_integral_cexp_catomCount hs
  have hN2 := S.mul_integral_cexp_catomCount hs2
  rw [show 2 * (2 * s) = 4 * s by ring] at hN2
  have hlogu : genEulerLog S.cPrimeNorm s = ∑' k, -Complex.log (1 - cexp (-(s * S.cRounded k))) :=
    rfl
  rw [hlogu, tsum_neg_log_eq_cube S.cRounded_pos S.cRounded_zero_le
    (fun a ha => S.summable_exp_cRounded ha) hs, crContinuation, ← S.cexp_logZeta_eq hs,
    ← Complex.exp_add, analyticExponent, roundingExponent, hc1, hc2, hd1, hd2, hN1, hN2]
  congr 1
  ring

theorem hasProd_crContinuation {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun k => (1 - cexp (-(s * Real.log (S.cPrimeNorm k))))⁻¹) (S.crContinuation s) := by
  rw [← S.genEulerLog_eq_crContinuation hs]
  exact hasProd_euler S.cRounded_pos S.cRounded_zero_le
    (fun a ha => S.summable_exp_cRounded ha) hs

theorem differentiableOn_analyticExponent :
    DifferentiableOn ℂ S.analyticExponent {s : ℂ | 1 / 3 < s.re} := by
  intro s hs
  have hs' : 1 / 3 < s.re := hs
  have hopen : ∀ c : ℝ, ∀ z : ℂ, c < z.re → {w : ℂ | c < w.re} ∈ 𝓝 z := fun c z hz =>
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have hL : DifferentiableAt ℂ (fun s : ℂ => S.logZeta (4 * s)) s :=
    (S.differentiableOn_logZeta.differentiableAt (hopen 1 (4 * s) (by simp; linarith))).comp s
      (differentiableAt_id.const_mul 4)
  have hΛ := differentiableOn_boundedLaplace_of_le S.measurable_cerror S.cbound_pos S.abs_cerror_le
  have hΛ1 : DifferentiableAt ℂ (boundedLaplace S.cerror) s :=
    hΛ.differentiableAt (hopen 0 s (by linarith))
  have hΛ2 : DifferentiableAt ℂ (fun s : ℂ => boundedLaplace S.cerror (2 * s)) s :=
    (hΛ.differentiableAt (hopen 0 (2 * s) (by simp; linarith))).comp s
      (differentiableAt_id.const_mul 2)
  have hRt : DifferentiableAt ℂ (primeCubeRemainder S.catom) s :=
    (differentiableOn_primeCubeRemainder S.catom_pos S.catom_zero_le
      (fun a ha => S.summable_exp_catom ha)).differentiableAt (hopen (1 / 3) s hs')
  have hRu : DifferentiableAt ℂ (primeCubeRemainder S.cRounded) s :=
    (differentiableOn_primeCubeRemainder S.cRounded_pos S.cRounded_zero_le
      (fun a ha => S.summable_exp_cRounded ha)).differentiableAt (hopen (1 / 3) s hs')
  have hC := differentiableOn_primeCorrection S.catom_pos S.catom_le_cRounded S.cRounded_le
    (fun a ha => S.summable_exp_catom ha)
  have hC1 : DifferentiableAt ℂ (primeCorrection S.catom S.cRounded) s :=
    hC.differentiableAt (hopen 0 s (by linarith))
  have hC2 : DifferentiableAt ℂ (fun s : ℂ => primeCorrection S.catom S.cRounded (2 * s)) s :=
    (hC.differentiableAt (hopen 0 (2 * s) (by simp; linarith))).comp s
      (differentiableAt_id.const_mul 2)
  have hround : DifferentiableAt ℂ S.roundingExponent s :=
    (((hC1.add (hC2.div_const 2)).add hRu).sub hRt)
  exact (((((hL.neg.div_const 4).add (differentiableAt_id.mul hΛ1)).add
    (differentiableAt_id.mul hΛ2)).add hRt).add hround).differentiableWithinAt

theorem differentiableOn_crContinuation :
    DifferentiableOn ℂ S.crContinuation {s : ℂ | 1 / 3 < s.re ∧ s ≠ 1} := by
  rintro s ⟨hs, hs1⟩
  have hs' : 1 / 3 < s.re := hs
  have hopen : ∀ c : ℝ, ∀ z : ℂ, c < z.re → {w : ℂ | c < w.re} ∈ 𝓝 z := fun c z hz =>
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have hζ : DifferentiableAt ℂ (overRegularZeta S.P.μ S.P.ν S.P.γ) s := by
    unfold overRegularZeta
    exact DifferentiableAt.div (by fun_prop) (by fun_prop)
      (overRegularZeta_denom_ne_zero (μ := S.P.μ) S.P.hν0.le (by linarith [S.P.hlow]) hs1)
  have hrem : DifferentiableAt ℂ S.remFactor s :=
    S.differentiableOn_remFactor.differentiableAt (hopen 0 s (by linarith))
  have han : DifferentiableAt ℂ S.analyticExponent s :=
    S.differentiableOn_analyticExponent.differentiableAt (hopen (1 / 3) s hs')
  exact ((hζ.mul hrem).mul han.cexp).differentiableWithinAt

theorem crContinuation_eq_poleFactor (s : ℂ) :
    S.crContinuation s = S.crPoleFactor s / (s - 1) := by
  rw [crContinuation, crPoleFactor, overRegularZeta]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem differentiableOn_crPoleFactor :
    DifferentiableOn ℂ S.crPoleFactor {s : ℂ | 1 / 3 < s.re} := by
  intro s hs
  have hs' : 1 / 3 < s.re := hs
  have hopen : ∀ c : ℝ, ∀ z : ℂ, c < z.re → {w : ℂ | c < w.re} ∈ 𝓝 z := fun c z hz =>
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have hlow : s + (3 * S.P.μ - 1 - S.P.ν) ≠ 0 := by
    intro he; have hr := congrArg Complex.re he; norm_num at hr; linarith only [S.P.hlow, hs', hr]
  have hhigh : s + (3 * S.P.μ - 1 + S.P.ν) ≠ 0 := by
    intro he; have hr := congrArg Complex.re he; norm_num at hr; linarith only [S.P.hhigh, hs', hr]
  have hrat : DifferentiableAt ℂ (fun z : ℂ =>
      ((z - (1 - S.P.μ)) ^ 2 + (S.P.γ : ℂ) ^ 2) * (z + (4 * S.P.μ - 1)) /
        ((z + (3 * S.P.μ - 1 - S.P.ν)) * (z + (3 * S.P.μ - 1 + S.P.ν)))) s :=
    DifferentiableAt.div (by fun_prop) (by fun_prop) (mul_ne_zero hlow hhigh)
  have hrem : DifferentiableAt ℂ S.remFactor s :=
    S.differentiableOn_remFactor.differentiableAt (hopen 0 s (by linarith))
  have han : DifferentiableAt ℂ S.analyticExponent s :=
    S.differentiableOn_analyticExponent.differentiableAt (hopen (1 / 3) s hs')
  exact ((hrat.mul hrem).mul han.cexp).differentiableWithinAt

theorem crPoleFactor_one_ne_zero : S.crPoleFactor 1 ≠ 0 := by
  have hμ : 0 < S.P.μ := by linarith only [S.P.hμ1]
  have hlow : 0 < 3 * S.P.μ - S.P.ν := by linarith only [S.P.hν]
  have hhigh : 0 < 3 * S.P.μ + S.P.ν := by linarith only [hμ, S.P.hν0]
  have hnum : 0 < (S.P.μ ^ 2 + S.P.γ ^ 2) * (4 * S.P.μ) := by positivity
  have hden : 0 < (3 * S.P.μ - S.P.ν) * (3 * S.P.μ + S.P.ν) := mul_pos hlow hhigh
  have hrat : (((1 : ℂ) - (1 - S.P.μ)) ^ 2 + (S.P.γ : ℂ) ^ 2) * (1 + (4 * S.P.μ - 1)) /
        ((1 + (3 * S.P.μ - 1 - S.P.ν)) * (1 + (3 * S.P.μ - 1 + S.P.ν))) =
      (((S.P.μ ^ 2 + S.P.γ ^ 2) * (4 * S.P.μ) / ((3 * S.P.μ - S.P.ν) * (3 * S.P.μ + S.P.ν)) : ℝ) : ℂ) := by
    push_cast; congr 1 <;> ring
  have hrem1 : S.remFactor 1 ≠ 0 := by
    intro hz
    obtain ⟨n, hn⟩ := (S.remFactor_eq_zero_iff (by norm_num)).mp hz
    have him : (0 : ℝ) = |S.ω n| := by
      rcases hn with h | h <;> have hi := congrArg Complex.im h <;>
        simp [remZero] at hi <;> rw [abs_of_pos (S.hγ.trans (S.ω_gt_γ n))] <;> linarith
    linarith [abs_pos.mpr (S.hγ.trans (S.ω_gt_γ n)).ne']
  rw [crPoleFactor, hrat]
  exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hnum hden).ne') hrem1)
    (Complex.exp_ne_zero _)

/-- Exact zero set of `crContinuation` on `{Re s > 1/3, s ≠ 1}`. -/
theorem crContinuation_eq_zero_iff {s : ℂ} (hs : 1 / 3 < s.re) (hs1 : s ≠ 1) :
    S.crContinuation s = 0 ↔
      s = (S.β : ℂ) + (S.γ : ℂ) * I ∨
      s = (S.β : ℂ) - (S.γ : ℂ) * I ∨
      ∃ n : ℕ, s = S.remZero n ∨ s = starRingEnd ℂ (S.remZero n) := by
  have hden := overRegularZeta_denom_ne_zero (μ := S.P.μ) S.P.hν0.le (by linarith [S.P.hlow]) hs1
  have h4 : s + (4 * S.P.μ - 1) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [S.P.hμ1]
  have hβ_eq : (1 : ℂ) - S.P.μ = S.β := by dsimp [P]; push_cast; ring
  have hγ_eq : S.P.γ = S.γ := rfl
  have hfac : (s - (1 - S.P.μ)) ^ 2 + (S.P.γ : ℂ) ^ 2 =
      (s - ((S.β : ℂ) + (S.γ : ℂ) * I)) * (s - ((S.β : ℂ) - (S.γ : ℂ) * I)) := by
    rw [hβ_eq, hγ_eq]
    linear_combination ((S.γ : ℂ) ^ 2) * Complex.I_sq
  rw [crContinuation, mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), mul_eq_zero,
    S.remFactor_eq_zero_iff (by linarith), overRegularZeta, div_eq_zero_iff, or_iff_left hden,
    mul_eq_zero, or_iff_left h4, hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero, or_assoc]

theorem crContinuation_ne_zero_critical_line {s : ℂ} (hs : s.re = 1 / 2) :
    S.crContinuation s ≠ 0 := by
  have hs3 : 1 / 3 < s.re := by rw [hs]; norm_num
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  intro h0
  rcases (S.crContinuation_eq_zero_iff hs3 hs1).mp h0 with rfl | rfl | ⟨n, rfl | rfl⟩
  · simp at hs; linarith [S.half_lt_θ₂, S.hβ]
  · simp at hs; linarith [S.half_lt_θ₂, S.hβ]
  · simp [remZero] at hs; linarith [S.half_lt_θSeq n]
  · simp [remZero] at hs; linarith [S.half_lt_θSeq n]

/-! ### Reflection-symmetrized strip `ZeroConfig` -/

/-- Right-half zero set `{s : 1/2 < Re s < 1, F(s) = 0}` of the wave Euler product. -/
def rightZeroSet : Set ℂ :=
  {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ S.crContinuation s = 0}

theorem mem_rightZeroSet_iff (s : ℂ) :
    s ∈ S.rightZeroSet ↔
      s = (S.β : ℂ) + (S.γ : ℂ) * I ∨
      s = (S.β : ℂ) - (S.γ : ℂ) * I ∨
      ∃ n : ℕ, s = S.remZero n ∨ s = starRingEnd ℂ (S.remZero n) := by
  simp only [rightZeroSet, mem_setOf_eq]
  constructor
  · rintro ⟨h12, h1, hz⟩
    have hs1 : s ≠ 1 := by intro he; rw [he] at h1; norm_num at h1
    exact (S.crContinuation_eq_zero_iff (by linarith) hs1).mp hz
  · intro h
    have hre : 1 / 2 < s.re ∧ s.re < 1 := by
      rcases h with rfl | rfl | ⟨n, rfl | rfl⟩
      · simp; exact ⟨by linarith [S.half_lt_θ₂, S.hβ], by linarith [S.h23]⟩
      · simp; exact ⟨by linarith [S.half_lt_θ₂, S.hβ], by linarith [S.h23]⟩
      · simp only [remZero_re]
        exact ⟨S.half_lt_θSeq n, (S.θSeq_le_θ₂ n).trans_lt (S.hβ.trans (S.h23.trans (by norm_num)))⟩
      · simp only [Complex.conj_re, remZero_re]
        exact ⟨S.half_lt_θSeq n, (S.θSeq_le_θ₂ n).trans_lt (S.hβ.trans (S.h23.trans (by norm_num)))⟩
    have hs1 : s ≠ 1 := by intro he; rw [he] at hre; norm_num at hre
    exact ⟨hre.1, hre.2, (S.crContinuation_eq_zero_iff (by linarith [hre.1]) hs1).mpr h⟩

/-- Strip `ZeroConfig` generated by the zeros of `S.crContinuation` in `(1/2, 1)` and their
functional-equation reflections `s ↦ 1 - conj s`. -/
def zeroConfig : ZeroConfig where
  carrier := S.rightZeroSet ∪ (reflect '' S.rightZeroSet)
  mult _ := 1
  one_le_mult _ _ := le_rfl
  strip := by
    rintro z (hz | ⟨w, hw, rfl⟩)
    · exact ⟨by linarith [hz.1], hz.2.1.le⟩
    · rw [re_reflect]
      exact ⟨by linarith [hw.2.1], by linarith [hw.1]⟩
  reflect_mem := by
    rintro z (hz | ⟨w, hw, rfl⟩)
    · exact Or.inr ⟨z, hz, rfl⟩
    · have hinv : reflect (reflect w) = w := by simp [reflect]
      rw [hinv]
      exact Or.inl hw
  mult_reflect _ _ := rfl
  finite_window T₁ T₂ := by
    let B : ℝ := max (|T₁|) (|T₂|)
    let N : ℕ := ⌊B⌋₊ + 1
    let F_right : Set ℂ :=
      {(S.β : ℂ) + (S.γ : ℂ) * I, (S.β : ℂ) - (S.γ : ℂ) * I} ∪
        (S.remZero '' (Finset.range N : Set ℕ)) ∪
        ((fun n => starRingEnd ℂ (S.remZero n)) '' (Finset.range N : Set ℕ))
    have hF_fin : F_right.Finite :=
      (((finite_singleton _).insert _).union ((Finset.range N).finite_toSet.image _)).union
        ((Finset.range N).finite_toSet.image _)
    have hsub_right : {z ∈ S.rightZeroSet | |z.im| ≤ B} ⊆ F_right := by
      rintro z ⟨hz, him⟩
      rcases (S.mem_rightZeroSet_iff z).mp hz with rfl | rfl | ⟨n, rfl | rfl⟩
      · exact Or.inl (Or.inl (Or.inl rfl))
      · exact Or.inl (Or.inl (Or.inr rfl))
      · refine Or.inl (Or.inr ⟨n, Finset.mem_coe.mpr (Finset.mem_range.mpr ?_), rfl⟩)
        simp only [remZero_im, abs_of_pos (S.hγ.trans (S.ω_gt_γ n))] at him
        have hω := S.ω_gt_bound n
        have hp : 0 ≤ S.γ + (2 : ℝ) ^ n * Real.exp (2 * S.A n) := by have := S.hγ; positivity
        have hnB : (n : ℝ) ≤ B := by linarith
        exact Nat.lt_succ_of_le (Nat.le_floor hnB)
      · refine Or.inr ⟨n, Finset.mem_coe.mpr (Finset.mem_range.mpr ?_), rfl⟩
        simp only [Complex.conj_im, remZero_im, abs_neg,
          abs_of_pos (S.hγ.trans (S.ω_gt_γ n))] at him
        have hω := S.ω_gt_bound n
        have hp : 0 ≤ S.γ + (2 : ℝ) ^ n * Real.exp (2 * S.A n) := by have := S.hγ; positivity
        have hnB : (n : ℝ) ≤ B := by linarith
        exact Nat.lt_succ_of_le (Nat.le_floor hnB)
    refine (hF_fin.union (hF_fin.image reflect)).subset ?_
    rintro z ⟨(hz | ⟨w, hw, rfl⟩), hT₁, hT₂⟩
    · refine Or.inl (hsub_right ⟨hz, abs_le.mpr ⟨?_, ?_⟩⟩)
      · linarith [neg_le_abs T₁, le_max_left |T₁| |T₂|]
      · linarith [le_abs_self T₂, le_max_right |T₁| |T₂|]
    · have hwim : (reflect w).im = w.im := by simp [reflect]
      rw [hwim] at hT₁ hT₂
      refine Or.inr ⟨w, hsub_right ⟨hw, abs_le.mpr ⟨?_, ?_⟩⟩, rfl⟩
      · linarith [neg_le_abs T₁, le_max_left |T₁| |T₂|]
      · linarith [le_abs_self T₂, le_max_right |T₁| |T₂|]

theorem zeroConfig_zeroAbscissa : zeroAbscissa S.zeroConfig = S.β := by
  refine le_antisymm ?_ ?_
  · refine (zeroAbscissa_le_iff S.zeroConfig).mpr ⟨by linarith [S.half_lt_θ₂, S.hβ], ?_⟩
    rintro z (hz | ⟨w, hw, rfl⟩)
    · rcases (S.mem_rightZeroSet_iff z).mp hz with rfl | rfl | ⟨n, rfl | rfl⟩
      · simp
      · simp
      · simp [remZero]; exact (S.θSeq_le_θ₂ n).trans S.hβ.le
      · simp [remZero]; exact (S.θSeq_le_θ₂ n).trans S.hβ.le
    · rw [re_reflect]
      linarith [hw.1, S.half_lt_θ₂, S.hβ]
  · have hmem : (S.β : ℂ) + (S.γ : ℂ) * I ∈ S.zeroConfig.carrier :=
      Or.inl ((S.mem_rightZeroSet_iff _).mpr (Or.inl rfl))
    simpa using re_le_zeroAbscissa S.zeroConfig hmem

/-- Above depth `h ≥ 0`, the configuration keeps the top pair and the remainder pairs with
`θ_n > ½ + h`. -/
theorem rightOf_subset {h : ℝ} (hh : 0 ≤ h) {N : ℕ} (hN : ∀ n, N ≤ n → S.θSeq n ≤ 1 / 2 + h) :
    rightOf S.zeroConfig h ⊆
      {(S.β : ℂ) + (S.γ : ℂ) * I, (S.β : ℂ) - (S.γ : ℂ) * I} ∪
        (S.remZero '' (Finset.range N : Set ℕ)) ∪
        ((fun n => starRingEnd ℂ (S.remZero n)) '' (Finset.range N : Set ℕ)) := by
  rintro z ⟨(hz | ⟨w, hw, rfl⟩), hre⟩
  · rcases (S.mem_rightZeroSet_iff z).mp hz with rfl | rfl | ⟨n, rfl | rfl⟩
    · exact Or.inl (Or.inl (Or.inl rfl))
    · exact Or.inl (Or.inl (Or.inr rfl))
    · by_cases hn : n < N
      · exact Or.inl (Or.inr ⟨n, Finset.mem_coe.mpr (Finset.mem_range.mpr hn), rfl⟩)
      · simp only [remZero_re] at hre; linarith [hN n (not_lt.mp hn)]
    · by_cases hn : n < N
      · exact Or.inr ⟨n, Finset.mem_coe.mpr (Finset.mem_range.mpr hn), rfl⟩
      · simp only [Complex.conj_re, remZero_re] at hre; linarith [hN n (not_lt.mp hn)]
  · rw [re_reflect] at hre
    linarith [hw.1]

/-- Infinitely many remainder zeros lie right of every line below `limsup θ_n`. -/
theorem rightOf_infinite_of_frequently {σ : ℝ} (hσ : ∀ N, ∃ n, N ≤ n ∧ σ < S.θSeq n) :
    (rightOf S.zeroConfig (σ - 1 / 2)).Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := (hfin.image Complex.im).bddAbove
  -- a remainder zero with `θ_m > σ` and ordinate `ω_m > m > B`
  obtain ⟨m, hm, hσm⟩ := hσ (⌊max B 0⌋₊ + 1)
  have hmem : S.remZero m ∈ rightOf S.zeroConfig (σ - 1 / 2) :=
    ⟨Or.inl ((S.mem_rightZeroSet_iff _).mpr (Or.inr (Or.inr ⟨m, Or.inl rfl⟩))), by
      simp only [remZero_re]; linarith⟩
  have him := hB ⟨_, hmem, rfl⟩
  simp only [remZero_im] at him
  have hω := S.ω_gt_bound m
  have hp : 0 ≤ S.γ + (2 : ℝ) ^ m * Real.exp (2 * S.A m) := by have := S.hγ; positivity
  have hmB : max B 0 < (m : ℝ) := by
    have h1 : max B 0 < (⌊max B 0⌋₊ + 1 : ℝ) := Nat.lt_floor_add_one _
    have h2 : (⌊max B 0⌋₊ + 1 : ℝ) ≤ m := by exact_mod_cast (by omega : ⌊max B 0⌋₊ + 1 ≤ m)
    linarith
  linarith [le_max_left B 0]

/-- **The asymptotic abscissa is the limit of the remainder real parts.** -/
theorem zeroConfig_asymptoticAbscissa_of_tendsto {L : ℝ} (hL : Tendsto S.θSeq atTop (𝓝 L)) :
    asymptoticAbscissa S.zeroConfig = L := by
  have hL12 : 1 / 2 ≤ L := ge_of_tendsto' hL fun n => (S.half_lt_θSeq n).le
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) ?_
  · obtain ⟨N, hN⟩ := eventually_atTop.mp (hL.eventually (gt_mem_nhds (by linarith : L < L + ε)))
    refine csInf_le (bddBelow_asymptoticAbscissaSet S.zeroConfig) ⟨by linarith, ?_⟩
    refine ((((finite_singleton _).insert _).union ((Finset.range N).finite_toSet.image _)).union
      ((Finset.range N).finite_toSet.image _)).subset (S.rightOf_subset (by linarith) fun n hn => ?_)
    linarith [hN n hn]
  · refine le_csInf (asymptoticAbscissaSet_nonempty S.zeroConfig) fun σ ⟨_, hfin⟩ => ?_
    by_contra hlt
    push Not at hlt
    refine S.rightOf_infinite_of_frequently (σ := σ) (fun N => ?_) hfin
    obtain ⟨M, hM⟩ := eventually_atTop.mp (hL.eventually (lt_mem_nhds hlt))
    exact ⟨max N M, le_max_left _ _, hM _ (le_max_right _ _)⟩

/-- The remainder zeros are infinitely many and all lie right of the line. -/
theorem zeroConfig_rightOf_zero_infinite : (rightOf S.zeroConfig 0).Infinite := by
  have h := S.rightOf_infinite_of_frequently (σ := 1 / 2) fun N => ⟨N, le_rfl, S.half_lt_θSeq N⟩
  simpa using h

theorem zeroConfig_right_carrier :
    {s ∈ S.zeroConfig.carrier | 1 / 2 < s.re} = S.rightZeroSet := by
  ext s
  change s ∈ S.rightZeroSet ∪ (reflect '' S.rightZeroSet) ∧ 1 / 2 < s.re ↔ s ∈ S.rightZeroSet
  constructor
  · rintro ⟨hs | ⟨w, hw, rfl⟩, hre⟩
    · exact hs
    · rw [re_reflect] at hre
      linarith [hw.1]
  · intro hs
    exact ⟨Or.inl hs, hs.1⟩

theorem zeroConfig_top_layer :
    {s ∈ S.zeroConfig.carrier | 1 / 2 < s.re ∧ |s.im| ≤ S.γ} =
      {(S.β : ℂ) + (S.γ : ℂ) * I, (S.β : ℂ) - (S.γ : ℂ) * I} := by
  ext s
  have hreβ : 1 / 2 < S.β := by linarith [S.half_lt_θ₂, S.hβ]
  simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hs, h12, him⟩
    have hright : s ∈ S.rightZeroSet := by
      rw [← S.zeroConfig_right_carrier]
      exact ⟨hs, h12⟩
    rcases (S.mem_rightZeroSet_iff s).mp hright with rfl | rfl | ⟨n, rfl | rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · simp only [remZero_im, abs_of_pos (S.hγ.trans (S.ω_gt_γ n))] at him
      linarith [S.ω_gt_γ n]
    · simp only [Complex.conj_im, remZero_im, abs_neg,
        abs_of_pos (S.hγ.trans (S.ω_gt_γ n))] at him
      linarith [S.ω_gt_γ n]
  · rintro (rfl | rfl)
    · refine ⟨Or.inl ((S.mem_rightZeroSet_iff _).mpr (Or.inl rfl)), ?_, ?_⟩
      · simpa using hreβ
      · simp [abs_of_pos S.hγ]
    · refine ⟨Or.inl ((S.mem_rightZeroSet_iff _).mpr (Or.inr (Or.inl rfl))), ?_, ?_⟩
      · simpa using hreβ
      · simp [abs_of_pos S.hγ]

theorem zeroConfig_remainder_le_θ₂ :
    ∀ z ∈ S.zeroConfig.carrier, S.γ < |z.im| → z.re ≤ S.θ₂ := by
  rintro z (hz | ⟨w, hw, rfl⟩) him
  · rcases (S.mem_rightZeroSet_iff z).mp hz with rfl | rfl | ⟨n, rfl | rfl⟩
    · simp [abs_of_pos S.hγ] at him
    · simp [abs_of_pos S.hγ] at him
    · simp only [remZero_re]
      exact S.θSeq_le_θ₂ n
    · simp only [Complex.conj_re, remZero_re]
      exact S.θSeq_le_θ₂ n
  · rw [re_reflect]
    linarith [hw.1, S.half_lt_θ₂]

/-- **The wave Euler product.** Natural generators `q_k ≥ 2` and natural coefficients `a_n` with
`∏_k (1 - q_k^{-s})^{-1} = ∑_n a_n n^{-s} = F(s)` on `Re s > 1` and `∑_{n<N} a_n ∼ A N`, whose
continuation to `{Re s > 1/3, s ≠ 1}` is nonvanishing on `Re s = 1/2` and whose zeros in
`1/2 < Re s < 1` are the right half of `S.zeroConfig`. -/
theorem exists_integer_norm_euler_product :
    ∃ q a : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ, ∃ A : ℝ, 0 < A ∧
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (F s) ∧
        LSeriesHasSum (fun n => (a n : ℂ)) s (F s)) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (a n : ℝ)) / N) atTop (𝓝 A) ∧
      DifferentiableOn ℂ F {s : ℂ | 1 / 3 < s.re ∧ s ≠ 1} ∧
      (∀ s : ℂ, s.re = 1 / 2 → F s ≠ 0) ∧
      {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ F s = 0} = {s ∈ S.zeroConfig.carrier | 1 / 2 < s.re} := by
  have hq := S.cPrimeNorm_ge_two
  have hmono : ∀ k, Real.log (S.cPrimeNorm 0) ≤ Real.log (S.cPrimeNorm k) := S.cRounded_zero_le
  have hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * Real.log (S.cPrimeNorm k))) :=
    fun a ha => S.summable_exp_cRounded ha
  obtain ⟨A, hA, -, hcount⟩ := tendsto_genCoeff_count hq hmono hsum (H := S.crPoleFactor)
    (σ₁ := 1 / 3) (by norm_num) S.differentiableOn_crPoleFactor S.crPoleFactor_one_ne_zero
    fun s hs => by rw [S.genEulerLog_eq_crContinuation hs, S.crContinuation_eq_poleFactor]
  refine ⟨S.cPrimeNorm, genCoeff S.cPrimeNorm, hq, S.crContinuation, A, hA,
    fun s hs => ⟨S.hasProd_crContinuation hs, ?_⟩, hcount, S.differentiableOn_crContinuation,
    fun s hs => S.crContinuation_ne_zero_critical_line hs, S.zeroConfig_right_carrier.symm⟩
  rw [← S.genEulerLog_eq_crContinuation hs]
  exact hasSum_genCoeff hq hmono hsum hs

end WaveSpec

/-! ### The two-scale instance -/

/-- Prescribed two-scale abscissa parameters `1/2 < θ ≤ θ₂ < β < 2/3` and top ordinate `γ > 0`. -/
structure TwoScaleSpec where
  θ : ℝ
  θ₂ : ℝ
  β : ℝ
  γ : ℝ
  h12 : 1 / 2 < θ
  hθ₂ : θ ≤ θ₂
  hβ : θ₂ < β
  h23 : β < 2 / 3
  hγ : 0 < γ

namespace TwoScaleSpec

variable (S : TwoScaleSpec)

/-- Remainder real parts `θ_0 = θ₂` and `θ_{n+1} = θ`. -/
def θSeq (n : ℕ) : ℝ := if n = 0 then S.θ₂ else S.θ

/-- The two-scale wave data. -/
def toWaveSpec : WaveSpec where
  θ₂ := S.θ₂
  β := S.β
  γ := S.γ
  θSeq := S.θSeq
  half_lt_θSeq n := by unfold θSeq; split_ifs <;> linarith [S.h12, S.hθ₂]
  θSeq_le_θ₂ n := by unfold θSeq; split_ifs <;> linarith [S.hθ₂]
  hβ := S.hβ
  h23 := S.h23
  hγ := S.hγ

/-- Strip configuration of the two-scale Euler product. -/
abbrev zeroConfig : ZeroConfig := S.toWaveSpec.zeroConfig

theorem tendsto_θSeq : Tendsto S.θSeq atTop (𝓝 S.θ) :=
  tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨1, fun n hn => by
    simp [θSeq, show n ≠ 0 by omega]⟩)

theorem zeroConfig_asymptoticAbscissa : asymptoticAbscissa S.zeroConfig = S.θ :=
  S.toWaveSpec.zeroConfig_asymptoticAbscissa_of_tendsto S.tendsto_θSeq

theorem zeroConfig_remainder_le_θ₂ :
    (∀ z ∈ S.zeroConfig.carrier, S.γ < |z.im| → z.re ≤ S.θ₂) ∧
      ∃ z ∈ S.zeroConfig.carrier, S.γ < |z.im| ∧ z.re = S.θ₂ := by
  refine ⟨S.toWaveSpec.zeroConfig_remainder_le_θ₂, S.toWaveSpec.remZero 0,
    Or.inl ((S.toWaveSpec.mem_rightZeroSet_iff _).mpr (Or.inr (Or.inr ⟨0, Or.inl rfl⟩))), ?_, ?_⟩
  · simp only [WaveSpec.remZero_im, abs_of_pos (S.hγ.trans (S.toWaveSpec.ω_gt_γ 0))]
    exact S.toWaveSpec.ω_gt_γ 0
  · simp [WaveSpec.remZero_re, toWaveSpec, θSeq]

theorem twoScaleZeroConfig_properties :
    zeroAbscissa S.zeroConfig = S.β ∧
      asymptoticAbscissa S.zeroConfig = S.θ ∧
      LinearAbscissaLaw S.zeroConfig ∧
      AbscissaLawAt S.zeroConfig 0 ∧
      ¬ AbscissaLaw S.zeroConfig ∧
      (rightOf S.zeroConfig 0).Infinite ∧
      ¬ ApproachesLine S.zeroConfig := by
  have hΘ : zeroAbscissa S.zeroConfig = S.β := S.toWaveSpec.zeroConfig_zeroAbscissa
  have hΘ_inf := S.zeroConfig_asymptoticAbscissa
  have hnot_zal : ¬ ApproachesLine S.zeroConfig := by
    rw [approachesLine_iff_asymptoticAbscissa_eq_half, hΘ_inf]
    linarith [S.h12]
  have hlin : LinearAbscissaLaw S.zeroConfig :=
    ⟨_, linearAbscissaLawAt_of_not_approachesLine S.zeroConfig hnot_zal⟩
  have hnot_aal : ¬ AbscissaLaw S.zeroConfig := by
    rw [abscissaLaw_iff_asymptoticAbscissa_eq_zeroAbscissa, hΘ, hΘ_inf]
    linarith [S.hθ₂, S.hβ]
  exact ⟨hΘ, hΘ_inf, hlin, abscissaLawAt_zero_of_linearAbscissaLaw S.zeroConfig hlin, hnot_aal,
    S.toWaveSpec.zeroConfig_rightOf_zero_infinite, hnot_zal⟩

end TwoScaleSpec

/-- **Two-scale integer-norm Euler product across the critical line.** For every triple
`1/2 < θ ≤ θ₂ < β < 2/3` and height `γ > 0`, there exist natural generators `q_k ≥ 2`, natural
Dirichlet coefficients `a_n` with `∏_k (1 - q_k^{-s})^{-1} = ∑_n a_n n^{-s} = F(s)` on `Re s > 1`
and `∑_{n<N} a_n ∼ A N` (`A > 0`), analytic continuation of `F` to `{Re s > 1/3, s ≠ 1}` nonvanishing
on `Re s = 1/2`, and a reflection-symmetric strip configuration `Z` whose right-half zeros coincide
with the zeros of `F` in `1/2 < Re s < 1`, realizing a finite top layer `β ± i γ`, sharp remainder
ceiling `θ₂` above `γ`, `zeroAbscissa Z = β`, `asymptoticAbscissa Z = θ`, `LinearAbscissaLaw Z`,
`¬ AbscissaLaw Z`, `(rightOf Z 0).Infinite`, and `¬ ApproachesLine Z`. -/
theorem exists_two_scale_integer_norm_euler_product
    {θ θ₂ β γ : ℝ} (h12 : 1 / 2 < θ) (hθ₂ : θ ≤ θ₂) (hβ : θ₂ < β) (h23 : β < 2 / 3)
    (hγ : 0 < γ) :
    ∃ q a : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ, ∃ A : ℝ, 0 < A ∧ ∃ Z : ZeroConfig,
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (F s) ∧
        LSeriesHasSum (fun n => (a n : ℂ)) s (F s)) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (a n : ℝ)) / N) atTop (𝓝 A) ∧
      DifferentiableOn ℂ F {s : ℂ | 1 / 3 < s.re ∧ s ≠ 1} ∧
      (∀ s : ℂ, s.re = 1 / 2 → F s ≠ 0) ∧
      {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ F s = 0} = {s ∈ Z.carrier | 1 / 2 < s.re} ∧
      {s ∈ Z.carrier | 1 / 2 < s.re ∧ |s.im| ≤ γ} =
        {(β : ℂ) + (γ : ℂ) * I, (β : ℂ) - (γ : ℂ) * I} ∧
      (∀ z ∈ Z.carrier, γ < |z.im| → z.re ≤ θ₂) ∧
      (∃ z ∈ Z.carrier, γ < |z.im| ∧ z.re = θ₂) ∧
      zeroAbscissa Z = β ∧
      asymptoticAbscissa Z = θ ∧
      LinearAbscissaLaw Z ∧
      ¬ AbscissaLaw Z ∧
      (rightOf Z 0).Infinite ∧
      ¬ ApproachesLine Z := by
  let S : TwoScaleSpec := ⟨θ, θ₂, β, γ, h12, hθ₂, hβ, h23, hγ⟩
  obtain ⟨q, a, hq, F, A, hA, hEuler, hcount, hdiff, hcrit, hright⟩ :=
    S.toWaveSpec.exists_integer_norm_euler_product
  obtain ⟨hrem_le, hrem_eq⟩ := S.zeroConfig_remainder_le_θ₂
  obtain ⟨hΘ, hΘ_inf, hlin, -, hnot_aal, hinf, hnot_zal⟩ := S.twoScaleZeroConfig_properties
  exact ⟨q, a, hq, F, A, hA, S.zeroConfig, hEuler, hcount, hdiff, hcrit, hright,
    S.toWaveSpec.zeroConfig_top_layer, hrem_le, hrem_eq, hΘ, hΘ_inf, hlin, hnot_aal, hinf,
    hnot_zal⟩

end

end GaloisForLFunctions.ArithmeticPositiveDuality.TwoScaleIntegerNormOneOff
