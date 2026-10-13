import GaloisForLFunctions.RHTower.DilationAutocorrelationPeriodization

/-!
# Poisson periodization of the dilation autocorrelation for bounded cores

The Poisson periodization `Σ_k A_f(|x+k|) = Ψ_f(0) + 2Ψ_f(1) cos 2πx` of a kernel `Ψ_f = Cf ⋆ f`
that vanishes at every integer `|n| ≥ 2` (`tsum_dilationAutocorr_abs_eq`) holds for every bounded
measurable `f` supported in `[α, β] ⊂ (0, ∞)` whose dilation autocorrelation `A_f` is continuous
(`tsum_dilationAutocorr_abs_eq_of_bounded`).  Such `f` need not be continuous; step functions are
the main example.  The proofs are those of the continuous case: the two-variable integrand
`f(y) f(yr) cos(2πxr)` is bounded, measurable and supported in `[α, β] × [α/β, β/α]`
(`integrable_cosDilationIntegrand_of_bounded`), which is all Fubini needs.
-/

open MeasureTheory Set Real
open scoped FourierTransform

namespace RHTower

noncomputable section

theorem integrable_cosDilationIntegrand_of_bounded {f : ℝ → ℝ} (hfm : Measurable f) {C : ℝ}
    (hfb : ∀ y, |f y| ≤ C) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (x : ℝ) :
    Integrable (Function.uncurry (cosDilationIntegrand f x))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  refine Integrable.integrableOn ?_
  set K : Set (ℝ × ℝ) := Icc α β ×ˢ Icc (α / β) (β / α) with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hmeas : Measurable (Function.uncurry (cosDilationIntegrand f x)) := by
    unfold cosDilationIntegrand Function.uncurry
    exact ((hfm.comp measurable_fst).mul (hfm.comp (measurable_fst.mul measurable_snd))).mul
      (Real.continuous_cos.measurable.comp (measurable_const.mul (measurable_const.mul measurable_snd)))
  have hbound : Integrable (K.indicator fun _ => C * C) :=
    (integrableOn_const hKc.measure_lt_top.ne).integrable_indicator hKc.measurableSet
  refine Integrable.mono' hbound hmeas.aestronglyMeasurable (ae_of_all _ fun p => ?_)
  obtain ⟨y, r⟩ := p
  simp only [Function.uncurry_apply_pair, cosDilationIntegrand]
  by_cases hp : (y, r) ∈ K
  · rw [indicator_of_mem hp, Real.norm_eq_abs, abs_mul, abs_mul]
    have h1 := hfb y
    have h2 := hfb (y * r)
    have h3 : |Real.cos (2 * π * (x * r))| ≤ 1 := Real.abs_cos_le_one _
    have hC : 0 ≤ C := le_trans (abs_nonneg _) h1
    calc |f y| * |f (y * r)| * |Real.cos (2 * π * (x * r))| ≤ C * C * 1 := by
          gcongr
      _ = C * C := mul_one _
  · rw [indicator_of_notMem hp, norm_le_zero_iff]
    by_contra hne
    have hfy : f y ≠ 0 := fun h => hne (by rw [h]; ring)
    have hfyr : f (y * r) ≠ 0 := fun h => hne (by rw [h]; ring)
    exact hp (ratio_mem_Icc_of_support hα hαβ hsupp hfy hfyr)

/-- **The cosine representation of `Cf ⋆ f`.** -/
theorem cosDilationKernel_eq_of_bounded {f : ℝ → ℝ} (hfm : Measurable f) {C : ℝ} (hfb : ∀ y, |f y| ≤ C) {α β : ℝ} (hα : 0 < α)
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
  have hint := integrable_cosDilationIntegrand_of_bounded hfm hfb hα hαβ hsupp x
  rw [integral_integral_swap hint]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  simp only [cosDilationIntegrand, dilationAutocorr]
  rw [← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  show f y * f (y * r) * Real.cos (2 * π * (x * r)) = f y * f (r * y) * Real.cos (2 * π * (x * r))
  rw [mul_comm r y]

/-- **The even extension.** -/
theorem cosDilationKernel_eq_integral_abs_of_bounded {f : ℝ → ℝ} (hfm : Measurable f) {C : ℝ} (hfb : ∀ y, |f y| ≤ C) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (x : ℝ) :
    cosDilationKernel f x = ∫ r, dilationAutocorr f |r| * Real.cos (2 * π * (x * r)) := by
  rw [cosDilationKernel_eq_of_bounded hfm hfb hα hαβ hsupp x]
  have h := integral_comp_abs (f := fun r => dilationAutocorr f r * Real.cos (2 * π * (x * r)))
  have e : ∀ r : ℝ, Real.cos (2 * π * (x * |r|)) = Real.cos (2 * π * (x * r)) := by
    intro r
    rcases le_or_gt 0 r with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_neg h0, mul_neg, mul_neg, Real.cos_neg]
  simp only [e] at h
  rw [h]

/-- The even extension `r ↦ A_f(|r|)` as a continuous complex function. -/
def evenDilationAutocorrOf {f : ℝ → ℝ} (hA : Continuous (dilationAutocorr f)) : C(ℝ, ℂ) :=
  ⟨fun r => ((dilationAutocorr f |r| : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (hA.comp continuous_abs)⟩

theorem cosDilationKernel_neg_of_bounded {f : ℝ → ℝ} (hfm : Measurable f) {C : ℝ} (hfb : ∀ y, |f y| ≤ C) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (x : ℝ) :
    cosDilationKernel f (-x) = cosDilationKernel f x := by
  rw [cosDilationKernel_eq_of_bounded hfm hfb hα hαβ hsupp, cosDilationKernel_eq_of_bounded hfm hfb hα hαβ hsupp]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rw [neg_mul, mul_neg, Real.cos_neg]

/-- **The Fourier transform of the even extension is `Ψ_f`.** -/
theorem fourier_evenDilationAutocorrOf {f : ℝ → ℝ} (hfm : Measurable f) {C : ℝ} (hfb : ∀ y, |f y| ≤ C) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (hA : Continuous (dilationAutocorr f)) (w : ℝ) :
    𝓕 (evenDilationAutocorrOf hA : ℝ → ℂ) w = (cosDilationKernel f w : ℂ) := by
  have hcont : Continuous fun v => dilationAutocorr f |v| :=
    hA.comp continuous_abs
  have hsupA := hasCompactSupport_dilationAutocorr_abs hα hαβ hsupp (f := f)
  have hintc : Integrable fun v => dilationAutocorr f |v| * Real.cos (2 * π * (w * v)) :=
    (hcont.mul (by fun_prop)).integrable_of_hasCompactSupport hsupA.mul_right
  have hints : Integrable fun v => dilationAutocorr f |v| * Real.sin (2 * π * (w * v)) :=
    (hcont.mul (by fun_prop)).integrable_of_hasCompactSupport hsupA.mul_right
  have hodd : ∫ v, dilationAutocorr f |v| * Real.sin (2 * π * (w * v)) = 0 := by
    have h := integral_neg_eq_self (fun v => dilationAutocorr f |v| * Real.sin (2 * π * (w * v))) volume
    simp only [abs_neg, mul_neg, Real.sin_neg, integral_neg] at h
    linarith
  rw [fourier_real_eq_integral_exp_smul, cosDilationKernel_eq_integral_abs_of_bounded hfm hfb hα hαβ hsupp]
  have e : ∀ v : ℝ, Complex.exp (↑(-2 * π * v * w) * Complex.I) •
      (evenDilationAutocorrOf hA : ℝ → ℂ) v =
      ((dilationAutocorr f |v| * Real.cos (2 * π * (w * v)) : ℝ) : ℂ) -
        Complex.I * ((dilationAutocorr f |v| * Real.sin (2 * π * (w * v)) : ℝ) : ℂ) := by
    intro v
    have hv : -2 * π * v * w = -(2 * π * (w * v)) := by ring
    simp only [evenDilationAutocorrOf, ContinuousMap.coe_mk, smul_eq_mul]
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
theorem tsum_dilationAutocorr_abs_eq_of_bounded {f : ℝ → ℝ} (hfm : Measurable f) {C : ℝ} (hfb : ∀ y, |f y| ≤ C) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (hA : Continuous (dilationAutocorr f))
    (hblind : ∀ n : ℤ, 2 ≤ |n| → cosDilationKernel f n = 0) (x : ℝ) :
    ∑' k : ℤ, ((dilationAutocorr f |x + k| : ℝ) : ℂ) =
      ((cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π * x) : ℝ) : ℂ) := by
  set ρ := evenDilationAutocorrOf hA with hρ
  have hF : ∀ n : ℤ, 𝓕 (ρ : ℝ → ℂ) n = (cosDilationKernel f n : ℂ) := fun n =>
    fourier_evenDilationAutocorrOf hfm hfb hα hαβ hsupp hA n
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
      ContinuousMap.coe_addRight, ContinuousMap.zero_apply, hρ, evenDilationAutocorrOf,
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
    rw [Int.cast_neg, Int.cast_one, cosDilationKernel_neg_of_bounded hfm hfb hα hαβ hsupp]
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
