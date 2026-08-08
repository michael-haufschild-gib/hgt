import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# Young's inequality for `L²` convolution on the line

`‖k ⋆ f‖₂ ≤ ‖k‖₁ ‖f‖₂`.  mathlib carries the convolution and its smoothness theory but not this
estimate.

The pointwise step is Cauchy–Schwarz against the weight `|k|`; the outer step is Tonelli on a
nonnegative integrand, which has to run in `ℝ≥0∞` because the joint-integrability hypothesis of
`integral_integral_swap` is the very quantity being computed.
-/

open MeasureTheory ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- The convolution of a kernel with a profile on the line. -/
noncomputable def lineConvolution (k f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, k y * f (x - y)

/-- **Tonelli for the weighted squared translate.** -/
theorem lintegral_weighted_translate_sq {k f : ℝ → ℝ} (hk : Measurable k) (hf : Measurable f) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (|k y| * f (x - y) ^ 2))
      = (∫⁻ y, ENNReal.ofReal |k y|) * ∫⁻ x, ENNReal.ofReal (f x ^ 2) := by
  have hmeas : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (|k p.2| * f (p.1 - p.2) ^ 2) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact ((hk.comp measurable_snd).abs).mul
      (((hf.comp (measurable_fst.sub measurable_snd))).pow_const 2)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hinner : ∀ y : ℝ, (∫⁻ x, ENNReal.ofReal (|k y| * f (x - y) ^ 2))
      = ENNReal.ofReal |k y| * ∫⁻ x, ENNReal.ofReal (f x ^ 2) := by
    intro y
    have hstep : ∀ x : ℝ, ENNReal.ofReal (|k y| * f (x - y) ^ 2)
        = ENNReal.ofReal |k y| * ENNReal.ofReal (f (x - y) ^ 2) := by
      intro x
      rw [ENNReal.ofReal_mul (abs_nonneg _)]
    have hm2 : Measurable fun x : ℝ => ENNReal.ofReal (f (x - y) ^ 2) := by fun_prop
    simp only [hstep]
    rw [lintegral_const_mul _ hm2]
    congr 1
    exact lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (f x ^ 2)) y
  simp only [hinner]
  exact lintegral_mul_const'' _ (by fun_prop)

/-- **The pointwise Cauchy–Schwarz step of Young's inequality.**  At every point, the square of the
convolution is at most the kernel's total mass times its weighted mean of the squared translate. -/
theorem sq_lineConvolution_le {k f : ℝ → ℝ} {x : ℝ}
    (hkm : AEStronglyMeasurable k volume) (hfm : AEStronglyMeasurable f volume)
    (hki : Integrable (fun y => |k y|))
    (h2 : Integrable (fun y => |k y| * f (x - y) ^ 2)) :
    lineConvolution k f x ^ 2 ≤ (∫ y, |k y|) * ∫ y, |k y| * f (x - y) ^ 2 := by
  have hg : AEStronglyMeasurable (fun y => f (x - y)) volume :=
    hfm.comp_measurePreserving ((volume : Measure ℝ).measurePreserving_sub_left x)
  have hkabs : AEStronglyMeasurable (fun y => |k y|) volume := by
    simpa [Real.norm_eq_abs] using hkm.norm
  have hgabs : AEStronglyMeasurable (fun y => |f (x - y)|) volume := by
    simpa [Real.norm_eq_abs] using hg.norm
  have habs2 : Integrable (fun y => |k y| * |f (x - y)| ^ 2) := by
    refine h2.congr ?_
    filter_upwards with y
    rw [sq_abs]
  have hcs := sq_integral_weighted_le (μ := (volume : Measure ℝ))
    (w := fun y => |k y|) (g := fun y => |f (x - y)|)
    (fun y => abs_nonneg _) hkabs hgabs hki habs2
  have hsq : (∫ y, |k y| * |f (x - y)| ^ 2) = ∫ y, |k y| * f (x - y) ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [sq_abs]
  rw [hsq] at hcs
  have hbound : |lineConvolution k f x| ≤ ∫ y, |k y| * |f (x - y)| := by
    rw [lineConvolution]
    refine le_trans (abs_integral_le_integral_abs) ?_
    refine le_of_eq (integral_congr_ae ?_)
    filter_upwards with y
    rw [abs_mul]
  calc lineConvolution k f x ^ 2 = |lineConvolution k f x| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ y, |k y| * |f (x - y)|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hbound 2
    _ ≤ (∫ y, |k y|) * ∫ y, |k y| * f (x - y) ^ 2 := hcs


/-! ## Joint integrability of the weighted translate -/

/-- The double integrand of Young's inequality is jointly integrable, by the Tonelli identity. -/
theorem integrable_weighted_translate_sq {k f : ℝ → ℝ} (hk : Measurable k) (hf : Measurable f)
    (hki : Integrable (fun y => |k y|)) (hf2 : Integrable (fun x => f x ^ 2)) :
    Integrable (Function.uncurry fun x y => |k y| * f (x - y) ^ 2)
      ((volume : Measure ℝ).prod volume) := by
  have hmeas : Measurable (Function.uncurry fun x y : ℝ => |k y| * f (x - y) ^ 2) :=
    ((hk.comp measurable_snd).abs).mul
      ((hf.comp (measurable_fst.sub measurable_snd)).pow_const 2)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hnn : ∀ p : ℝ × ℝ, 0 ≤ (Function.uncurry fun x y : ℝ => |k y| * f (x - y) ^ 2) p := by
    intro p; exact mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have henorm : (∫⁻ p, ‖(Function.uncurry fun x y : ℝ => |k y| * f (x - y) ^ 2) p‖ₑ
      ∂((volume : Measure ℝ).prod volume))
      = ∫⁻ p, ENNReal.ofReal ((Function.uncurry fun x y : ℝ => |k y| * f (x - y) ^ 2) p)
        ∂((volume : Measure ℝ).prod volume) := by
    refine lintegral_congr fun p => ?_
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hnn p)]
  have hprod : (∫⁻ p, ENNReal.ofReal ((Function.uncurry fun x y : ℝ => |k y| * f (x - y) ^ 2) p)
      ∂((volume : Measure ℝ).prod volume))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (|k y| * f (x - y) ^ 2) :=
    lintegral_prod _ ((ENNReal.measurable_ofReal.comp hmeas).aemeasurable)
  rw [HasFiniteIntegral, henorm, hprod, lintegral_weighted_translate_sq hk hf]
  have h1 : (∫⁻ y, ENNReal.ofReal |k y|) ≠ ⊤ := by
    have := hki.hasFiniteIntegral
    rw [HasFiniteIntegral] at this
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) this)
    refine lintegral_congr fun y => ?_
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
  have h2 : (∫⁻ x, ENNReal.ofReal (f x ^ 2)) ≠ ⊤ := by
    have := hf2.hasFiniteIntegral
    rw [HasFiniteIntegral] at this
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) this)
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact ENNReal.mul_lt_top (lt_of_le_of_ne le_top h1) (lt_of_le_of_ne le_top h2)


/-! ## Young's inequality -/

/-- The double integral of the weighted translate factors. -/
theorem integral_double_translate_sq {k f : ℝ → ℝ} (hk : Measurable k) (hf : Measurable f)
    (hki : Integrable (fun y => |k y|)) (hf2 : Integrable (fun x => f x ^ 2)) :
    (∫ x, ∫ y, |k y| * f (x - y) ^ 2) = (∫ y, |k y|) * ∫ x, f x ^ 2 := by
  have hjoint := integrable_weighted_translate_sq hk hf hki hf2
  rw [integral_integral_swap hjoint]
  have hinner : ∀ y : ℝ, (∫ x, |k y| * f (x - y) ^ 2) = |k y| * ∫ x, f x ^ 2 := by
    intro y
    rw [integral_const_mul]
    congr 1
    exact integral_sub_right_eq_self (fun x => f x ^ 2) y
  simp only [hinner]
  rw [integral_mul_const]

/-- **Young's inequality for `L²` convolution.**  `‖k ⋆ f‖₂ ≤ ‖k‖₁ ‖f‖₂`, in squared form. -/
theorem integral_sq_lineConvolution_le {k f : ℝ → ℝ} (hk : Measurable k) (hf : Measurable f)
    (hki : Integrable (fun y => |k y|)) (hf2 : Integrable (fun x => f x ^ 2))
    (hconv : Integrable (fun x => lineConvolution k f x ^ 2)) :
    (∫ x, lineConvolution k f x ^ 2) ≤ (∫ y, |k y|) ^ 2 * ∫ x, f x ^ 2 := by
  have hjoint := integrable_weighted_translate_sq hk hf hki hf2
  have hG : Integrable (fun x => ∫ y, |k y| * f (x - y) ^ 2) := hjoint.integral_prod_left
  have hae : ∀ᵐ x, Integrable (fun y => |k y| * f (x - y) ^ 2) := hjoint.prod_right_ae
  have hbound : ∀ᵐ x, lineConvolution k f x ^ 2
      ≤ (∫ y, |k y|) * ∫ y, |k y| * f (x - y) ^ 2 := by
    filter_upwards [hae] with x hx
    exact sq_lineConvolution_le hk.aestronglyMeasurable hf.aestronglyMeasurable hki hx
  have hmono := integral_mono_ae hconv (hG.const_mul _) hbound
  rw [integral_const_mul, integral_double_translate_sq hk hf hki hf2] at hmono
  calc (∫ x, lineConvolution k f x ^ 2)
      ≤ (∫ y, |k y|) * ((∫ y, |k y|) * ∫ x, f x ^ 2) := hmono
    _ = (∫ y, |k y|) ^ 2 * ∫ x, f x ^ 2 := by ring


end GaloisForLFunctions.HTGeometry
