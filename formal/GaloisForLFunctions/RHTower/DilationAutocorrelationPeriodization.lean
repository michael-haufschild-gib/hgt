import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# The dilation autocorrelation and the cosine–dilation kernel `Cf ⋆ f`

For a real function `f` on `(0, ∞)` let

* `A_f(r) = ∫_0^∞ f(y) f(ry) dy` (`dilationAutocorr`),
* `Cf(w) = 2 ∫_0^∞ f(z) cos(2π z w) dz` (`halfLineCosTransform`),
* `Ψ_f(x) = ∫_0^∞ f(y) Cf(x/y) dy/y` (`cosDilationKernel`), the multiplicative convolution `Cf ⋆ f`.

Since `Γ_ℝ(s)/Γ_ℝ(1−s) = 2𝓜[cos 2πx](s)`, `Ψ_f` is the inverse Mellin transform of
`(Γ_ℝ(s)/Γ_ℝ(1−s)) 𝓜f(s) 𝓜f(1−s)`, whose values on `Re s = ½` are `e^{2iθ(t)} |𝓜f(½+it)|²`.

* **Inversion law** (`dilationAutocorr_inv`): `A_f(1/r) = r A_f(r)` for `r > 0`, by the substitution
  `y = rw`.
* **Cosine representation** (`cosDilationKernel_eq`): for continuous `f` supported in `[α, β]`,
  `0 < α ≤ β`, `Ψ_f(x) = 2 ∫_0^∞ A_f(r) cos(2π x r) dr`. The inner substitution `z = yr` turns
  `Cf(x/y)/y` into `2 ∫ f(yr) cos(2π x r) dr`, and Fubini exchanges the integrals; the integrand is
  continuous and supported in `[α, β] × [α/β, β/α]`.
* **Even extension** (`cosDilationKernel_eq_integral_abs`): `Ψ_f(x) = ∫_ℝ A_f(|r|) cos(2π x r) dr`.
* **Support and continuity** (`dilationAutocorr_eq_zero_of_not_mem`, `continuous_dilationAutocorr`):
  `A_f` is continuous and vanishes off `[α/β, β/α]`.
* **Fourier transform** (`fourier_evenDilationAutocorr`): the Fourier transform of `r ↦ A_f(|r|)`
  is `Ψ_f`; the odd part integrates to zero.
* **Poisson periodization** (`tsum_dilationAutocorr_abs_eq`): if `Ψ_f(n) = 0` for every integer
  `|n| ≥ 2`, then `Σ_k A_f(|x + k|) = Ψ_f(0) + 2Ψ_f(1) cos 2πx` for every `x`.

So vanishing of `Ψ_f` on the integers `n ≥ 2` forces the even `1`-periodization of the dilation
autocorrelation to be a trigonometric polynomial of degree one; positivity of the symbol
`|𝓜f(½+it)|²` and the inversion law hold for every `f`.
-/

open MeasureTheory Set Real
open scoped FourierTransform

namespace RHTower

noncomputable section

/-- The dilation autocorrelation `A_f(r) = ∫_0^∞ f(y) f(ry) dy`. -/
def dilationAutocorr (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), f y * f (r * y)

/-- The half-line cosine transform `Cf(w) = 2 ∫_0^∞ f(z) cos(2π z w) dz`. -/
def halfLineCosTransform (f : ℝ → ℝ) (w : ℝ) : ℝ :=
  2 * ∫ z in Ioi (0 : ℝ), f z * Real.cos (2 * π * (z * w))

/-- The cosine–dilation kernel `Ψ_f(x) = ∫_0^∞ f(y) Cf(x/y) dy/y`. -/
def cosDilationKernel (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), f y * halfLineCosTransform f (x / y) / y

/-- **The inversion law** `A_f(1/r) = r A_f(r)`. -/
theorem dilationAutocorr_inv (f : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    dilationAutocorr f r⁻¹ = r * dilationAutocorr f r := by
  unfold dilationAutocorr
  have h := integral_comp_mul_left_Ioi (fun y => f y * f (r⁻¹ * y)) 0 hr
  simp only [mul_zero, smul_eq_mul] at h
  have e : ∀ x : ℝ, f (r * x) * f (r⁻¹ * (r * x)) = f x * f (r * x) := by
    intro x
    rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul, mul_comm]
  simp only [e] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

/-- The substitution `z = y r` in the cosine transform. -/
theorem halfLineCosTransform_div (f : ℝ → ℝ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    halfLineCosTransform f (x / y) =
      2 * y * ∫ r in Ioi (0 : ℝ), f (y * r) * Real.cos (2 * π * (x * r)) := by
  unfold halfLineCosTransform
  have h := integral_comp_mul_left_Ioi
    (fun z => f z * Real.cos (2 * π * (z * (x / y)))) 0 hy
  simp only [mul_zero, smul_eq_mul] at h
  have e : ∀ r : ℝ, y * r * (x / y) = x * r := by
    intro r; field_simp
  simp only [e] at h
  rw [h, ← mul_assoc, mul_assoc 2 y, mul_inv_cancel₀ hy.ne', mul_one]


/-- If `f(y) ≠ 0` and `f(yr) ≠ 0` for `f` supported in `[α, β]`, then `r ∈ [α/β, β/α]`. -/
theorem ratio_mem_Icc_of_support {f : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {y r : ℝ} (hfy : f y ≠ 0) (hfyr : f (y * r) ≠ 0) :
    y ∈ Icc α β ∧ r ∈ Icc (α / β) (β / α) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  obtain ⟨hy1, hy2⟩ := hsupp y hfy
  obtain ⟨hyr1, hyr2⟩ := hsupp (y * r) hfyr
  have hy0 : 0 < y := lt_of_lt_of_le hα hy1
  have hr : 0 < r := by
    by_contra h; push Not at h
    have : y * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy0.le h
    linarith
  refine ⟨⟨hy1, hy2⟩, ?_, ?_⟩
  · rw [div_le_iff₀ hβ]
    calc α ≤ y * r := hyr1
      _ ≤ β * r := mul_le_mul_of_nonneg_right hy2 hr.le
      _ = r * β := mul_comm β r
  · rw [le_div_iff₀ hα]
    calc r * α ≤ r * y := mul_le_mul_of_nonneg_left hy1 hr.le
      _ = y * r := mul_comm r y
      _ ≤ β := hyr2

/-- The two-variable integrand `f(y) f(yr) cos(2π x r)`. -/
def cosDilationIntegrand (f : ℝ → ℝ) (x : ℝ) (y r : ℝ) : ℝ :=
  f y * f (y * r) * Real.cos (2 * π * (x * r))

theorem integrable_cosDilationIntegrand {f : ℝ → ℝ} (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (x : ℝ) :
    Integrable (Function.uncurry (cosDilationIntegrand f x))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  refine Integrable.integrableOn ?_
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hcont : Continuous (Function.uncurry (cosDilationIntegrand f x)) := by
    unfold cosDilationIntegrand Function.uncurry
    fun_prop
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro ((isCompact_Icc (a := α) (b := β)).prod
    (isCompact_Icc (a := α / β) (b := β / α))) fun p hp => ?_
  obtain ⟨y, r⟩ := p
  simp only [Function.uncurry_apply_pair, cosDilationIntegrand]
  by_contra hne
  have hfy : f y ≠ 0 := fun h => hne (by rw [h]; ring)
  have hfyr : f (y * r) ≠ 0 := fun h => hne (by rw [h]; ring)
  exact hp (ratio_mem_Icc_of_support hα hαβ hsupp hfy hfyr)

/-- **The cosine representation of `Cf ⋆ f`.** -/
theorem cosDilationKernel_eq {f : ℝ → ℝ} (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (x : ℝ) :
    cosDilationKernel f x =
      2 * ∫ r in Ioi (0 : ℝ), dilationAutocorr f r * Real.cos (2 * π * (x * r)) := by
  have step1 : cosDilationKernel f x =
      ∫ y in Ioi (0 : ℝ), 2 * ∫ r in Ioi (0 : ℝ), cosDilationIntegrand f x y r := by
    unfold cosDilationKernel
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : (0 : ℝ) < y := hy
    rw [halfLineCosTransform_div f hy0 x]
    simp only [cosDilationIntegrand]
    set I := ∫ r in Ioi (0 : ℝ), f (y * r) * Real.cos (2 * π * (x * r)) with hI
    have h2 : f y * (2 * y * I) / y = 2 * (f y * I) := by
      rw [div_eq_iff hy0.ne']; ring
    rw [h2, hI, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    ring
  rw [step1, integral_const_mul]
  have hint := integrable_cosDilationIntegrand hf hα hαβ hsupp x
  rw [integral_integral_swap hint]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  simp only [cosDilationIntegrand, dilationAutocorr]
  rw [← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  show f y * f (y * r) * Real.cos (2 * π * (x * r)) = f y * f (r * y) * Real.cos (2 * π * (x * r))
  rw [mul_comm r y]

/-- **The even extension.** -/
theorem cosDilationKernel_eq_integral_abs {f : ℝ → ℝ} (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (x : ℝ) :
    cosDilationKernel f x = ∫ r, dilationAutocorr f |r| * Real.cos (2 * π * (x * r)) := by
  rw [cosDilationKernel_eq hf hα hαβ hsupp x]
  have h := integral_comp_abs (f := fun r => dilationAutocorr f r * Real.cos (2 * π * (x * r)))
  have e : ∀ r : ℝ, Real.cos (2 * π * (x * |r|)) = Real.cos (2 * π * (x * r)) := by
    intro r
    rcases le_or_gt 0 r with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_neg h0, mul_neg, mul_neg, Real.cos_neg]
  simp only [e] at h
  rw [h]

/-! ### Support, continuity and the Poisson periodization -/

theorem dilationAutocorr_eq_zero_of_not_mem {f : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {r : ℝ} (hr : r ∉ Icc (α / β) (β / α)) :
    dilationAutocorr f r = 0 := by
  unfold dilationAutocorr
  refine integral_eq_zero_of_ae (ae_of_all _ fun y => ?_)
  by_contra hne
  have hfy : f y ≠ 0 := fun h => hne (by simp [h])
  have hfyr : f (y * r) ≠ 0 := fun h => hne (by simp [mul_comm r y, h])
  exact hr (ratio_mem_Icc_of_support hα hαβ hsupp hfy hfyr).2

theorem continuous_dilationAutocorr {f : ℝ → ℝ} (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) : Continuous (dilationAutocorr f) := by
  have e : dilationAutocorr f = fun r => ∫ y in Icc α β, f y * f (r * y) := by
    funext r
    unfold dilationAutocorr
    have h1 : ∫ y in Ioi (0 : ℝ), f y * f (r * y) = ∫ y, f y * f (r * y) := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
      have : f y = 0 := by
        by_contra h
        have := (hsupp y h).1
        exact hy (lt_of_lt_of_le hα this)
      simp [this]
    have h2 : ∫ y in Icc α β, f y * f (r * y) = ∫ y, f y * f (r * y) := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
      have : f y = 0 := by
        by_contra h
        exact hy (hsupp y h)
      simp [this]
    rw [h1, h2]
  rw [e]
  exact continuous_parametric_integral_of_continuous (f := fun r y => f y * f (r * y))
    (by fun_prop) isCompact_Icc

/-- The even extension `r ↦ A_f(|r|)` as a continuous complex function. -/
def evenDilationAutocorr {f : ℝ → ℝ} (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) : C(ℝ, ℂ) :=
  ⟨fun r => ((dilationAutocorr f |r| : ℝ) : ℂ),
    Complex.continuous_ofReal.comp ((continuous_dilationAutocorr hf hα hsupp).comp
      continuous_abs)⟩

theorem cosDilationKernel_neg {f : ℝ → ℝ} (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (x : ℝ) :
    cosDilationKernel f (-x) = cosDilationKernel f x := by
  rw [cosDilationKernel_eq hf hα hαβ hsupp, cosDilationKernel_eq hf hα hαβ hsupp]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rw [neg_mul, mul_neg, Real.cos_neg]

theorem hasCompactSupport_dilationAutocorr_abs {f : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    HasCompactSupport fun v => dilationAutocorr f |v| := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(β / α)) (b := β / α)) fun v hv => ?_
  refine dilationAutocorr_eq_zero_of_not_mem hα hαβ hsupp fun h => hv ?_
  exact abs_le.mp h.2

/-- **The Fourier transform of the even extension is `Ψ_f`.** -/
theorem fourier_evenDilationAutocorr {f : ℝ → ℝ} (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (w : ℝ) :
    𝓕 (evenDilationAutocorr hf hα hsupp : ℝ → ℂ) w = (cosDilationKernel f w : ℂ) := by
  have hcont : Continuous fun v => dilationAutocorr f |v| :=
    (continuous_dilationAutocorr hf hα hsupp).comp continuous_abs
  have hsupA := hasCompactSupport_dilationAutocorr_abs hα hαβ hsupp (f := f)
  have hintc : Integrable fun v => dilationAutocorr f |v| * Real.cos (2 * π * (w * v)) :=
    (hcont.mul (by fun_prop)).integrable_of_hasCompactSupport hsupA.mul_right
  have hints : Integrable fun v => dilationAutocorr f |v| * Real.sin (2 * π * (w * v)) :=
    (hcont.mul (by fun_prop)).integrable_of_hasCompactSupport hsupA.mul_right
  have hodd : ∫ v, dilationAutocorr f |v| * Real.sin (2 * π * (w * v)) = 0 := by
    have h := integral_neg_eq_self (fun v => dilationAutocorr f |v| * Real.sin (2 * π * (w * v))) volume
    simp only [abs_neg, mul_neg, Real.sin_neg, integral_neg] at h
    linarith
  rw [fourier_real_eq_integral_exp_smul, cosDilationKernel_eq_integral_abs hf hα hαβ hsupp]
  have e : ∀ v : ℝ, Complex.exp (↑(-2 * π * v * w) * Complex.I) •
      (evenDilationAutocorr hf hα hsupp : ℝ → ℂ) v =
      ((dilationAutocorr f |v| * Real.cos (2 * π * (w * v)) : ℝ) : ℂ) -
        Complex.I * ((dilationAutocorr f |v| * Real.sin (2 * π * (w * v)) : ℝ) : ℂ) := by
    intro v
    have hv : -2 * π * v * w = -(2 * π * (w * v)) := by ring
    simp only [evenDilationAutocorr, ContinuousMap.coe_mk, smul_eq_mul]
    rw [Complex.exp_mul_I, hv, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg]
    push_cast
    ring
  simp_rw [e]
  rw [integral_sub hintc.ofReal (hints.ofReal.const_mul _), integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal, hodd]
  simp

/-- **Poisson periodization of a blind kernel.**  If `Ψ_f` vanishes at every integer `n` with
`|n| ≥ 2`, the `1`-periodization of `r ↦ A_f(|r|)` is `Ψ_f(0) + 2Ψ_f(1) cos 2πx`. -/
theorem tsum_dilationAutocorr_abs_eq {f : ℝ → ℝ} (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hblind : ∀ n : ℤ, 2 ≤ |n| → cosDilationKernel f n = 0) (x : ℝ) :
    ∑' k : ℤ, ((dilationAutocorr f |x + k| : ℝ) : ℂ) =
      ((cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π * x) : ℝ) : ℂ) := by
  set ρ := evenDilationAutocorr hf hα hsupp with hρ
  have hF : ∀ n : ℤ, 𝓕 (ρ : ℝ → ℂ) n = (cosDilationKernel f n : ℂ) := fun n =>
    fourier_evenDilationAutocorr hf hα hαβ hsupp n
  have hout : ∀ n : ℤ, n ∉ Finset.Icc (-1 : ℤ) 1 → 2 ≤ |n| := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [le_abs']
    omega
  have h_sum : Summable fun n : ℤ => 𝓕 (ρ : ℝ → ℂ) n := by
    refine summable_of_ne_finset_zero (s := Finset.Icc (-1 : ℤ) 1) fun n hn => ?_
    rw [hF, hblind n (hout n hn), Complex.ofReal_zero]
  have h_norm : ∀ K : TopologicalSpace.Compacts ℝ,
      Summable fun n : ℤ => ‖(ρ.comp (ContinuousMap.addRight (n : ℝ))).restrict K‖ := by
    intro K
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
    obtain ⟨N, hN⟩ := exists_int_gt (R + β / α)
    refine summable_of_ne_finset_zero (s := Finset.Icc (-N) N) fun n hn => ?_
    rw [norm_eq_zero]
    ext ⟨y, hy⟩
    have hyR : |y| ≤ R := by
      have := hR hy
      rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    have hn' : (N : ℝ) < |(n : ℝ)| := by
      rw [Finset.mem_Icc] at hn
      have : N < |n| := by rw [lt_abs]; omega
      exact_mod_cast this
    have hbig : β / α < |y + n| := by
      have := abs_sub_abs_le_abs_add (n : ℝ) y
      have h3 := abs_add_le (y + n) (-y)
      have e1 : y + n + -y = (n : ℝ) := by ring
      rw [e1, abs_neg] at h3
      linarith
    simp only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_addRight, ContinuousMap.zero_apply, hρ, evenDilationAutocorr,
      ContinuousMap.coe_mk]
    rw [dilationAutocorr_eq_zero_of_not_mem hα hαβ hsupp (fun h => by linarith [h.2]),
      Complex.ofReal_zero]
  have hP := Real.tsum_eq_tsum_fourier h_norm h_sum x
  have hL : ∀ k : ℤ, ρ (x + k) = ((dilationAutocorr f |x + k| : ℝ) : ℂ) := fun k => rfl
  simp only [hL] at hP
  rw [hP, tsum_eq_sum (s := Finset.Icc (-1 : ℤ) 1) fun n hn => by
    rw [hF, hblind n (hout n hn), Complex.ofReal_zero, zero_mul]]
  have hI : Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} := by decide
  rw [hI, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [hF, fourier_coe_apply]
  have hneg : cosDilationKernel f ((-1 : ℤ) : ℝ) = cosDilationKernel f 1 := by
    rw [Int.cast_neg, Int.cast_one, cosDilationKernel_neg hf hα hαβ hsupp]
  rw [hneg]
  have hexp : ∀ c : ℂ, Complex.exp (2 * ↑π * Complex.I * c * ↑x / ((1 : ℝ) : ℂ)) =
      Complex.exp (c * ((2 * π * x : ℝ) : ℂ) * Complex.I) := by
    intro c; congr 1; push_cast; ring
  simp only [hexp]
  simp only [Int.cast_neg, Int.cast_one, Int.cast_zero, neg_mul, one_mul, zero_mul,
    Complex.exp_zero, mul_one]
  rw [← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

end

end RHTower
