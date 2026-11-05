import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.BoundedLipschitzCutoffsPreserveLogarithmicEnergy

/-!
# The bounded literal logarithmic cutoff commutator

Lipschitz cancellation bounds the singular commutator kernel by an integrable
exponential. The resulting Schur operator preserves essential boundedness.
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform ENNReal InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

/-- The literal commutator kernel of logarithmic energy and real multiplication. -/
def logarithmicCutoffKernel (χ : ℝ → ℝ) (x y : ℝ) : ℂ :=
  ((χ x - χ y) * logReferenceLevyDensity |x - y| : ℝ)

theorem measurable_logarithmicCutoffKernel {χ : ℝ → ℝ} (hm : Measurable χ) :
    Measurable (Function.uncurry (logarithmicCutoffKernel χ)) := by
  exact Complex.continuous_ofReal.measurable.comp
    (((hm.comp measurable_fst).sub (hm.comp measurable_snd)).mul
      (measurable_logReferenceLevyDensity.comp (measurable_fst.sub measurable_snd).abs))

/-- Lipschitz cancellation removes the singularity and leaves an exponential kernel. -/
theorem norm_logarithmicCutoffKernel_le {χ : ℝ → ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|) (x y : ℝ) :
    ‖logarithmicCutoffKernel χ x y‖ ≤ (Λ / 2) * Real.exp (-|x - y|) := by
  by_cases hxy : x = y
  · subst y
    simp only [logarithmicCutoffKernel, sub_self, zero_mul, Complex.ofReal_zero, norm_zero]
    positivity
  have habs : |x - y| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hxy)
  rw [logarithmicCutoffKernel, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (logReferenceLevyDensity_nonneg (abs_nonneg _))]
  calc
    _ ≤ (Λ * |x - y|) * logReferenceLevyDensity |x - y| :=
      mul_le_mul_of_nonneg_right (hlip x y) (logReferenceLevyDensity_nonneg (abs_nonneg _))
    _ = _ := by unfold logReferenceLevyDensity; field_simp [habs]

private theorem integrable_logarithmicCutoffEnvelope :
    Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul 2)
    (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have hq := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have hpos : 0 < 1 + x ^ 2 := by positivity
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  rw [show 2 * (1 + x ^ 2)⁻¹ * Real.exp |x| = 2 * Real.exp |x| / (1 + x ^ 2) by field_simp]
  rw [le_div_iff₀ hpos]
  nlinarith only [hq, hx2, abs_nonneg x]

private theorem integral_logarithmicCutoffEnvelope :
    (∫ x : ℝ, Real.exp (-|x|)) = 2 := by
  rw [integral_comp_abs (f := fun x : ℝ => Real.exp (-x)), integral_exp_neg_Ioi,
    neg_zero, Real.exp_zero, mul_one]

private def logarithmicCutoffEnvelopeKernel (Λ : ℝ) : SchurKernel (volume : Measure ℝ) :=
  convolutionKernel (fun x : ℝ => ((Λ / 2) * Real.exp (-|x|) : ℝ))
    (by fun_prop)
    (Complex.ofRealCLM.integrable_comp (integrable_logarithmicCutoffEnvelope.const_mul (Λ / 2)))


private theorem norm_logarithmicCutoffEnvelope {Λ : ℝ} (hΛ : 0 ≤ Λ) (x : ℝ) :
    ‖(((Λ / 2) * Real.exp (-|x|) : ℝ) : ℂ)‖ = (Λ / 2) * Real.exp (-|x|) := by
  rw [Complex.norm_real]
  exact Real.norm_of_nonneg
    (mul_nonneg (div_nonneg hΛ (by norm_num : (0 : ℝ) ≤ 2)) (Real.exp_pos (-|x|)).le)

private theorem logarithmicCutoffEnvelopeKernel_bound {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    (logarithmicCutoffEnvelopeKernel Λ).bound = ⟨Λ, hΛ⟩ := by
  apply Subtype.ext
  change (∫⁻ x : ℝ, ‖(((Λ / 2) * Real.exp (-|x|) : ℝ) : ℂ)‖ₑ).toReal = Λ
  calc
    _ = ∫ x : ℝ, ‖(((Λ / 2) * Real.exp (-|x|) : ℝ) : ℂ)‖ := by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => norm_nonneg _)
        (Continuous.aestronglyMeasurable (by fun_prop))]
      simp only [ofReal_norm]
    _ = Λ := by
      simp_rw [norm_logarithmicCutoffEnvelope hΛ]
      rw [integral_const_mul, integral_logarithmicCutoffEnvelope]
      ring

/-- The actual logarithmic commutator is a bounded integral operator on all of L². -/
def logarithmicCutoffSchurKernel {χ : ℝ → ℝ} (hm : Measurable χ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|) : SchurKernel (volume : Measure ℝ) where
  toFun := logarithmicCutoffKernel χ
  measurable := measurable_logarithmicCutoffKernel hm
  bound := ⟨Λ, hΛ⟩
  row x := by
    rw [← logarithmicCutoffEnvelopeKernel_bound hΛ]
    apply le_trans (lintegral_mono fun y => ?_) ((logarithmicCutoffEnvelopeKernel Λ).row x)
    rw [← ofReal_norm, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    simpa only [logarithmicCutoffEnvelopeKernel, convolutionKernel_toFun,
      norm_logarithmicCutoffEnvelope hΛ] using norm_logarithmicCutoffKernel_le hΛ hlip x y
  col y := by
    rw [← logarithmicCutoffEnvelopeKernel_bound hΛ]
    apply le_trans (lintegral_mono fun x => ?_) ((logarithmicCutoffEnvelopeKernel Λ).col y)
    rw [← ofReal_norm, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    simpa only [logarithmicCutoffEnvelopeKernel, convolutionKernel_toFun,
      norm_logarithmicCutoffEnvelope hΛ] using norm_logarithmicCutoffKernel_le hΛ hlip x y

/-- The singular commutator has operator norm at most the Lipschitz constant. -/
theorem norm_logarithmicCutoffSchurKernel_op_le {χ : ℝ → ℝ} (hm : Measurable χ)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|) :
    ‖(logarithmicCutoffSchurKernel hm hΛ hlip).op‖ ≤ Λ :=
  (logarithmicCutoffSchurKernel hm hΛ hlip).norm_op_le

/-- The same literal kernel preserves essential boundedness of L² sources. -/
theorem logarithmicCutoffSchurKernel_preserves_boundedness {χ : ℝ → ℝ} (hm : Measurable χ)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|)
    (f : RealLineL2) {C : ℝ} (hf : ∀ᵐ x ∂volume, ‖f x‖ ≤ C) :
    ∀ᵐ x ∂volume, ‖(logarithmicCutoffSchurKernel hm hΛ hlip).op f x‖ ≤ Λ * C := by
  let k := logarithmicCutoffSchurKernel hm hΛ hlip
  filter_upwards [k.op_coeFn f, k.ae_integrable f] with x hx hi
  rw [hx]
  change ‖∫ y : ℝ, logarithmicCutoffKernel χ x y * f y‖ ≤ Λ * C
  have henv : Integrable (fun y : ℝ => (Λ / 2) * Real.exp (-|x - y|) * C) :=
    ((integrable_logarithmicCutoffEnvelope.comp_sub_left x).const_mul (Λ / 2)).mul_const C
  calc
    _ ≤ ∫ y : ℝ, ‖logarithmicCutoffKernel χ x y * f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, (Λ / 2) * Real.exp (-|x - y|) * C := by
      apply integral_mono_ae hi.norm henv
      filter_upwards [hf] with y hy
      rw [norm_mul]
      exact mul_le_mul (norm_logarithmicCutoffKernel_le hΛ hlip x y) hy (norm_nonneg _)
        (mul_nonneg (div_nonneg hΛ (by norm_num)) (Real.exp_pos _).le)
    _ = Λ * C := by
      rw [integral_mul_const, integral_const_mul,
        integral_sub_left_eq_self (fun y : ℝ => Real.exp (-|y|)) volume x,
        integral_logarithmicCutoffEnvelope]
      ring

#print axioms logarithmicCutoffSchurKernel
#print axioms logarithmicCutoffSchurKernel_preserves_boundedness
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
