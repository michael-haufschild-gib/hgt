import GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Cauchy's beta integral

For `Re a > 0`, `Re b > 1`,

`∫_ℝ (1 + iη)^{−a} (1 − iη)^{−b} dη = π 2^{2−a−b} Γ(a+b−1) / (Γ(a) Γ(b))`.

The one-sided Gamma densities `f_a(t) = t^{a−1} e^{−t} [t > 0]` have Fourier transforms
`𝓕f_a(ξ) = Γ(a) (1 + 2πiξ)^{−a}` (Euler's integral with the complex rate `1 + 2πiξ`).  The
self-adjointness `∫ 𝓕f · g = ∫ f · 𝓕g` with `g = 𝓕⁻ f_b` and Fourier inversion
`𝓕(𝓕⁻ f_b) = f_b` (valid since `f_b` is continuous for `Re b > 1`) give
`∫ 𝓕f_a · 𝓕⁻ f_b = ∫ f_a f_b = Γ(a+b−1) 2^{1−a−b}`.  This is the `ξ`-integral in Kuznetsov's
evaluation of the pairing of two Poincaré series.
-/

open Complex MeasureTheory Set Filter Topology Real
open scoped FourierTransform

namespace GaloisForLFunctions.RHTower.Kuznetsov

noncomputable section

/-- The one-sided Gamma density `t^{a−1} e^{−t} [t > 0]`. -/
def gammaDensity (a : ℂ) (t : ℝ) : ℂ := (Ioi (0 : ℝ)).indicator
  (fun t : ℝ => (t : ℂ) ^ (a - 1) * Complex.exp (-(t : ℂ))) t

theorem integrable_gammaDensity {a : ℂ} (ha : 0 < a.re) : Integrable (gammaDensity a) := by
  unfold gammaDensity
  rw [integrable_indicator_iff measurableSet_Ioi]
  have := HTGeometry.integrableOn_cpow_mul_exp_neg_mul_Ioi (s := a) (w := 1) ha (by norm_num)
  simpa using this

theorem integral_gammaDensity_mul {a w : ℂ} (ha : 0 < a.re) (hw : 0 < w.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) * Complex.exp (-(w * t)) = Complex.Gamma a * w ^ (-a) :=
  HTGeometry.integral_cpow_mul_exp_neg_mul_Ioi ha hw

/-- **Fourier transform of the Gamma density.** -/
theorem fourier_gammaDensity {a : ℂ} (ha : 0 < a.re) (ξ : ℝ) :
    𝓕 (gammaDensity a) ξ = Complex.Gamma a * (1 + 2 * π * I * ξ) ^ (-a) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h : (fun v : ℝ => Complex.exp (↑(-2 * π * v * ξ) * I) • gammaDensity a v) =
      (Ioi (0 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ (a - 1) *
        Complex.exp (-((1 + 2 * π * I * ξ) * t))) := by
    funext v
    unfold gammaDensity
    by_cases hv : v ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hv, indicator_of_mem hv, smul_eq_mul, mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    · rw [indicator_of_notMem hv, indicator_of_notMem hv, smul_zero]
  rw [h, integral_indicator measurableSet_Ioi]
  exact integral_gammaDensity_mul ha (by simp)

/-- **Inverse Fourier transform of the Gamma density.** -/
theorem fourierInv_gammaDensity {b : ℂ} (hb : 0 < b.re) (ξ : ℝ) :
    𝓕⁻ (gammaDensity b) ξ = Complex.Gamma b * (1 - 2 * π * I * ξ) ^ (-b) := by
  rw [Real.fourierInv_eq_fourier_neg, fourier_gammaDensity hb]
  congr 2
  push_cast
  ring

theorem norm_gammaDensity_le {b : ℂ} (t : ℝ) : ‖gammaDensity b t‖ ≤ |t| ^ (b.re - 1) := by
  unfold gammaDensity
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · have ht0 : (0 : ℝ) < t := ht
    rw [indicator_of_mem ht, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_exp,
      Complex.neg_re, Complex.ofReal_re, abs_of_pos ht0, Complex.sub_re, Complex.one_re]
    exact mul_le_of_le_one_right (Real.rpow_nonneg ht0.le _)
      (Real.exp_le_one_iff.mpr (by linarith))
  · rw [indicator_of_notMem ht, norm_zero]
    exact Real.rpow_nonneg (abs_nonneg t) _

theorem continuous_gammaDensity {b : ℂ} (hb : 1 < b.re) : Continuous (gammaDensity b) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rcases lt_trichotomy t₀ 0 with h | h | h
  · have hev : gammaDensity b =ᶠ[𝓝 t₀] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with t ht
      unfold gammaDensity
      exact indicator_of_notMem (fun h' => lt_asymm ht h') _
    exact continuousAt_const.congr hev.symm
  · subst h
    have h0 : gammaDensity b 0 = 0 := by
      unfold gammaDensity; exact indicator_of_notMem (lt_irrefl 0) _
    rw [ContinuousAt, h0]
    have hc : 0 < b.re - 1 := by linarith
    have hlim : Tendsto (fun t : ℝ => |t| ^ (b.re - 1)) (𝓝 0) (𝓝 0) := by
      have := ((continuous_abs.rpow_const fun _ => Or.inr hc.le).tendsto 0)
      simpa [Real.zero_rpow hc.ne'] using this
    exact squeeze_zero_norm (fun t => norm_gammaDensity_le t) hlim
  · have hev : gammaDensity b =ᶠ[𝓝 t₀]
        fun t : ℝ => (t : ℂ) ^ (b - 1) * Complex.exp (-(t : ℂ)) := by
      filter_upwards [Ioi_mem_nhds h] with t ht
      unfold gammaDensity
      exact indicator_of_mem ht _
    refine ContinuousAt.congr ?_ hev.symm
    exact (Complex.continuousAt_ofReal_cpow_const t₀ (b - 1) (Or.inr h.ne')).mul
      (Complex.continuous_exp.comp Complex.continuous_ofReal.neg).continuousAt

/-- **The multiplication formula** `∫ 𝓕f · g = ∫ f · 𝓕g` on the line. -/
theorem integral_fourier_mul_eq (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  simp_rw [Real.fourier_real_eq]
  simp_rw [Circle.smul_def, smul_eq_mul]
  have hF : Integrable (fun p : ℝ × ℝ => (𝐞 (-(p.2 * p.1)) : ℂ) * f p.2 * g p.1)
      (volume.prod volume) := by
    have hprod : Integrable (fun p : ℝ × ℝ => g p.1 * f p.2) (volume.prod volume) :=
      hg.mul_prod hf
    refine hprod.norm.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact ((Continuous.aestronglyMeasurable (by fun_prop)).mul
        hf.1.comp_snd).mul hg.1.comp_fst
    · rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, norm_mul, mul_comm]
  calc ∫ ξ, (∫ v, (𝐞 (-(v * ξ)) : ℂ) * f v) * g ξ
      = ∫ ξ, ∫ v, (𝐞 (-(v * ξ)) : ℂ) * f v * g ξ := by
        congr 1; ext ξ; rw [← integral_mul_const]
    _ = ∫ v, ∫ ξ, (𝐞 (-(v * ξ)) : ℂ) * f v * g ξ := integral_integral_swap hF
    _ = ∫ x, f x * ∫ v, (𝐞 (-(v * x)) : ℂ) * g v := by
        congr 1; ext x; rw [← integral_const_mul]
        congr 1; ext v; rw [mul_comm v x]; ring

theorem one_add_abs_le_two_mul_norm (c : ℝ) (hc : 1 ≤ |c|) (ξ : ℝ) :
    1 + |ξ| ≤ 2 * ‖(1 : ℂ) + c * I * ξ‖ := by
  have h1 : 1 ≤ ‖(1 : ℂ) + c * I * ξ‖ := by
    have := Complex.abs_re_le_norm ((1 : ℂ) + c * I * ξ)
    simp at this
    linarith
  have h2 : |ξ| ≤ ‖(1 : ℂ) + c * I * ξ‖ := by
    have := Complex.abs_im_le_norm ((1 : ℂ) + c * I * ξ)
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, add_zero, mul_one, zero_add,
      Complex.mul_re, sub_zero] at this
    rw [abs_mul] at this
    nlinarith [abs_nonneg ξ]
  linarith

/-- `ξ ↦ (1 + ciξ)^{−b}` is integrable for `Re b > 1`, `|c| ≥ 1`. -/
theorem integrable_one_add_mul_I_cpow {b : ℂ} (hb : 1 < b.re) {c : ℝ} (hc : 1 ≤ |c|) :
    Integrable (fun ξ : ℝ => ((1 : ℂ) + c * I * ξ) ^ (-b)) := by
  have hint := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := b.re)
    (by simpa using hb)).const_mul (2 ^ b.re * Real.exp (π * |b.im|))
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
  · exact (Continuous.aestronglyMeasurable
      ((by fun_prop : Continuous fun ξ : ℝ => (1 : ℂ) + c * I * ξ).cpow continuous_const
        fun ξ => Or.inl (by simp)))
  · have hne : (1 : ℂ) + c * I * ξ ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    rw [Complex.norm_cpow_of_ne_zero hne]
    have harg : |((1 : ℂ) + c * I * ξ).arg| ≤ π := Complex.abs_arg_le_pi _
    have hexp : Real.exp (-(((1 : ℂ) + c * I * ξ).arg * (-b).im)) ≤ Real.exp (π * |b.im|) := by
      refine Real.exp_le_exp.mpr ?_
      have : |((1 : ℂ) + c * I * ξ).arg * (-b).im| ≤ π * |b.im| := by
        rw [abs_mul, Complex.neg_im, abs_neg]
        exact mul_le_mul_of_nonneg_right harg (abs_nonneg _)
      linarith [neg_abs_le (((1 : ℂ) + c * I * ξ).arg * (-b).im)]
    have hbase := one_add_abs_le_two_mul_norm c hc ξ
    have hpos : 0 < ‖(1 : ℂ) + c * I * ξ‖ := norm_pos_iff.mpr hne
    have hpow : ‖(1 : ℂ) + c * I * ξ‖ ^ (-b).re ≤ 2 ^ b.re * (1 + ‖ξ‖) ^ (-b.re) := by
      have hle : (1 + |ξ|) / 2 ≤ ‖(1 : ℂ) + c * I * ξ‖ := by linarith
      rw [Complex.neg_re]
      calc ‖(1 : ℂ) + c * I * ξ‖ ^ (-b.re) ≤ ((1 + |ξ|) / 2) ^ (-b.re) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
        _ = 2 ^ b.re * (1 + ‖ξ‖) ^ (-b.re) := by
            rw [Real.div_rpow (by positivity) (by norm_num), Real.norm_eq_abs,
              Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv, inv_inv]
            ring
    rw [div_eq_mul_inv, ← Real.exp_neg]
    calc ‖(1 : ℂ) + c * I * ξ‖ ^ (-b).re * Real.exp (-(((1 : ℂ) + c * I * ξ).arg * (-b).im))
        ≤ (2 ^ b.re * (1 + ‖ξ‖) ^ (-b.re)) * Real.exp (π * |b.im|) :=
          mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
      _ = 2 ^ b.re * Real.exp (π * |b.im|) * (1 + ‖ξ‖) ^ (-b.re) := by ring

/-- **Cauchy's beta integral**, Fourier normalisation:
`∫ (1 + 2πiξ)^{−a} (1 − 2πiξ)^{−b} dξ = Γ(a+b−1) 2^{1−a−b} / (Γ(a) Γ(b))`. -/
theorem integral_one_add_two_pi_mul_cpow {a b : ℂ} (ha : 0 < a.re) (hb : 1 < b.re) :
    ∫ ξ : ℝ, (1 + 2 * π * I * ξ) ^ (-a) * (1 - 2 * π * I * ξ) ^ (-b) =
      Complex.Gamma (a + b - 1) * 2 ^ (1 - (a + b)) / (Complex.Gamma a * Complex.Gamma b) := by
  have hb0 : 0 < b.re := by linarith
  have hfa := integrable_gammaDensity ha
  have hfb := integrable_gammaDensity hb0
  have h2pi : (1 : ℝ) ≤ |2 * π| := by
    rw [abs_of_pos (by positivity)]; linarith [Real.pi_gt_three]
  have h2pi' : (1 : ℝ) ≤ |-(2 * π)| := by rwa [abs_neg]
  -- the inverse transform of `f_b` is integrable
  have hinvint : Integrable (𝓕⁻ (gammaDensity b)) := by
    have := (integrable_one_add_mul_I_cpow hb h2pi').const_mul (Complex.Gamma b)
    refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
    rw [fourierInv_gammaDensity hb0]
    push_cast; ring_nf
  have hfwdint : Integrable (𝓕 (gammaDensity b)) := by
    have := (integrable_one_add_mul_I_cpow hb h2pi).const_mul (Complex.Gamma b)
    refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
    show _ = _
    rw [fourier_gammaDensity hb0]
    push_cast; ring_nf
  have hinv : 𝓕 (𝓕⁻ (gammaDensity b)) = gammaDensity b := by
    funext x
    exact hfb.fourier_fourierInv_eq hfwdint (continuous_gammaDensity hb).continuousAt
  have hmul := integral_fourier_mul_eq (gammaDensity a) (𝓕⁻ (gammaDensity b)) hfa hinvint
  rw [hinv] at hmul
  simp_rw [fourier_gammaDensity ha, fourierInv_gammaDensity hb0] at hmul
  -- the right side
  have hright : ∫ x, gammaDensity a x * gammaDensity b x =
      Complex.Gamma (a + b - 1) * 2 ^ (-(a + b - 1)) := by
    have h : (fun x => gammaDensity a x * gammaDensity b x) = (Ioi (0 : ℝ)).indicator
        (fun t : ℝ => (t : ℂ) ^ (a + b - 1 - 1) * Complex.exp (-(2 * t))) := by
      funext x
      unfold gammaDensity
      by_cases hx : x ∈ Ioi (0 : ℝ)
      · have hx0 : (0 : ℝ) < x := hx
        rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx]
        have hcp : (x : ℂ) ^ (a - 1) * (x : ℂ) ^ (b - 1) = (x : ℂ) ^ (a + b - 1 - 1) := by
          rw [← Complex.cpow_add _ _ (by exact_mod_cast hx0.ne')]
          congr 1; ring
        rw [show (x : ℂ) ^ (a - 1) * Complex.exp (-(x : ℂ)) * ((x : ℂ) ^ (b - 1) *
            Complex.exp (-(x : ℂ))) = ((x : ℂ) ^ (a - 1) * (x : ℂ) ^ (b - 1)) *
            (Complex.exp (-(x : ℂ)) * Complex.exp (-(x : ℂ))) by ring, hcp, ← Complex.exp_add]
        congr 2; ring
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
    rw [h, integral_indicator measurableSet_Ioi]
    exact integral_gammaDensity_mul (by simp; linarith) (by norm_num)
  rw [hright] at hmul
  have hG : Complex.Gamma a * Complex.Gamma b ≠ 0 :=
    mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos ha) (Complex.Gamma_ne_zero_of_re_pos hb0)
  rw [eq_div_iff hG, show 1 - (a + b) = -(a + b - 1) by ring, ← hmul, ← integral_mul_const]
  congr 1
  ext ξ
  ring

/-- **Cauchy's beta integral**:
`∫_ℝ (1 + iη)^{−a} (1 − iη)^{−b} dη = π 2^{2−a−b} Γ(a+b−1) / (Γ(a) Γ(b))` for `Re a > 0`,
`Re b > 1`. -/
theorem integral_one_add_I_mul_cpow {a b : ℂ} (ha : 0 < a.re) (hb : 1 < b.re) :
    ∫ η : ℝ, (1 + I * η) ^ (-a) * (1 - I * η) ^ (-b) =
      π * 2 ^ (2 - (a + b)) * Complex.Gamma (a + b - 1) / (Complex.Gamma a * Complex.Gamma b) := by
  have h := Measure.integral_comp_mul_left
    (fun η : ℝ => (1 + I * η) ^ (-a) * (1 - I * η) ^ (-b)) (2 * π)
  have h' : ∫ ξ : ℝ, (1 + I * ((2 * π * ξ : ℝ) : ℂ)) ^ (-a) * (1 - I * ((2 * π * ξ : ℝ) : ℂ)) ^ (-b) =
      ∫ ξ : ℝ, (1 + 2 * π * I * ξ) ^ (-a) * (1 - 2 * π * I * ξ) ^ (-b) := by
    congr 1; ext ξ; push_cast; ring_nf
  rw [h', integral_one_add_two_pi_mul_cpow ha hb, abs_inv, abs_of_pos (by positivity),
    Complex.real_smul] at h
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  have hI : ∫ η : ℝ, (1 + I * η) ^ (-a) * (1 - I * η) ^ (-b) = ((2 * π : ℝ) : ℂ) *
      (Complex.Gamma (a + b - 1) * 2 ^ (1 - (a + b)) / (Complex.Gamma a * Complex.Gamma b)) := by
    rw [h, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hpi, Complex.ofReal_one, one_mul]
  rw [hI, show (2 : ℂ) ^ (2 - (a + b)) = 2 * 2 ^ (1 - (a + b)) by
    rw [show 2 - (a + b) = 1 + (1 - (a + b)) by ring, Complex.cpow_add _ _ (by norm_num),
      Complex.cpow_one]]
  push_cast
  ring

end

end GaloisForLFunctions.RHTower.Kuznetsov
