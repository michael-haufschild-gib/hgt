import GaloisForLFunctions.HTGeometry.GoldenRuleKernel

/-!
# The golden-rule limit

The analytic heart of Fermi's golden rule: against an integrable weight that is continuous at the
resonance, the golden-rule kernel behaves like `2 π t` times a Dirac mass,

```text
t⁻¹ ∫_ℝ K t x · g x dx  ⟶  2 π g 0        (t → ∞).
```

The proof is the standard concentration split at a radius `δ`.  Inside `|x| < δ` the weight is
within `η` of `g 0` and the whole mass `2 π t` of the kernel is available; outside, the kernel is
bounded by `4/x²`, so both the missing mass and the outside contribution stay bounded uniformly in
`t` and disappear after dividing by `t`.

No hypothesis beyond integrability of `g` and continuity of `g` at the single point `0` is used.
-/

open MeasureTheory Set Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section Tail

variable {δ : ℝ}

theorem abs_ge_of_notMem_Ioo (hδ : 0 < δ) {x : ℝ} (hx : x ∉ Set.Ioo (-δ) δ) : δ ≤ |x| := by
  rcases le_or_gt 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0]
    by_contra hcon
    exact hx ⟨by linarith, by linarith⟩
  · rw [abs_of_neg hx0]
    by_contra hcon
    exact hx ⟨by linarith, by linarith⟩

/-- On the tail the kernel is dominated by a fixed integrable majorant, uniformly in the time. -/
theorem goldenRuleKernel_le_tail_majorant (hδ : 0 < δ) (t : ℝ) {x : ℝ}
    (hx : x ∉ Set.Ioo (-δ) δ) :
    goldenRuleKernel t x ≤ (4 + 4 / δ ^ 2) * (1 + x ^ 2)⁻¹ := by
  have habs : δ ≤ |x| := abs_ge_of_notMem_Ioo hδ hx
  have hx0 : x ≠ 0 := by
    intro h; rw [h] at habs; simp at habs; linarith
  have hx2 : δ ^ 2 ≤ x ^ 2 := by
    have := sq_abs x
    nlinarith [abs_nonneg x]
  have hxpos : (0 : ℝ) < x ^ 2 := by positivity
  have hδpos : (0 : ℝ) < δ ^ 2 := by positivity
  have hone : (0 : ℝ) < 1 + x ^ 2 := by positivity
  refine le_trans (goldenRuleKernel_le_four_div_sq t hx0) ?_
  rw [← div_eq_mul_inv, div_le_div_iff₀ hxpos hone]
  have hexp : (4 + 4 / δ ^ 2) * x ^ 2 - 4 * (1 + x ^ 2) = 4 * x ^ 2 / δ ^ 2 - 4 := by
    field_simp; ring
  have hfrac : (4 : ℝ) ≤ 4 * x ^ 2 / δ ^ 2 := by
    rw [le_div_iff₀ hδpos]; nlinarith
  linarith

/-- The tail mass of the kernel is bounded uniformly in the time. -/
theorem setIntegral_goldenRuleKernel_tail_le (hδ : 0 < δ) (t : ℝ) :
    ∫ x in (Set.Ioo (-δ) δ)ᶜ, goldenRuleKernel t x ≤ (4 + 4 / δ ^ 2) * Real.pi := by
  have hmaj : Integrable (fun x : ℝ => (4 + 4 / δ ^ 2) * (1 + x ^ 2)⁻¹) (volume : Measure ℝ) :=
    integrable_inv_one_add_sq.const_mul _
  have hmeas : MeasurableSet ((Set.Ioo (-δ) δ)ᶜ) := measurableSet_Ioo.compl
  have h1 : ∫ x in (Set.Ioo (-δ) δ)ᶜ, goldenRuleKernel t x
      ≤ ∫ x in (Set.Ioo (-δ) δ)ᶜ, (4 + 4 / δ ^ 2) * (1 + x ^ 2)⁻¹ := by
    refine MeasureTheory.setIntegral_mono_on
      ((integrable_goldenRuleKernel t).integrableOn) (hmaj.integrableOn) hmeas ?_
    intro x hx
    exact goldenRuleKernel_le_tail_majorant hδ t hx
  have h2 : ∫ x in (Set.Ioo (-δ) δ)ᶜ, (4 + 4 / δ ^ 2) * (1 + x ^ 2)⁻¹
      ≤ ∫ x : ℝ, (4 + 4 / δ ^ 2) * (1 + x ^ 2)⁻¹ := by
    refine MeasureTheory.setIntegral_le_integral hmaj ?_
    filter_upwards with x
    have : (0 : ℝ) < 1 + x ^ 2 := by positivity
    positivity
  have h3 : ∫ x : ℝ, (4 + 4 / δ ^ 2) * (1 + x ^ 2)⁻¹ = (4 + 4 / δ ^ 2) * Real.pi := by
    rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
  linarith

/-- The tail contribution of an integrable weight vanishes uniformly in the time. -/
theorem abs_setIntegral_goldenRuleKernel_tail_mul_le (hδ : 0 < δ) (t : ℝ) {g : ℝ → ℝ}
    (hg : Integrable g (volume : Measure ℝ)) :
    |∫ x in (Set.Ioo (-δ) δ)ᶜ, goldenRuleKernel t x * g x|
      ≤ (4 / δ ^ 2) * ∫ x : ℝ, |g x| := by
  have hmeas : MeasurableSet ((Set.Ioo (-δ) δ)ᶜ) := measurableSet_Ioo.compl
  have hKg : Integrable (fun x : ℝ => goldenRuleKernel t x * g x) (volume : Measure ℝ) := by
    refine hg.bdd_mul (c := t ^ 2) (continuous_goldenRuleKernel t).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (goldenRuleKernel_nonneg t x)]
    exact goldenRuleKernel_le_sq t x
  have habs : Integrable (fun x : ℝ => (4 / δ ^ 2) * |g x|) (volume : Measure ℝ) :=
    (hg.abs).const_mul _
  calc |∫ x in (Set.Ioo (-δ) δ)ᶜ, goldenRuleKernel t x * g x|
      ≤ ∫ x in (Set.Ioo (-δ) δ)ᶜ, |goldenRuleKernel t x * g x| := by
        simpa using MeasureTheory.abs_integral_le_integral_abs
          (μ := (volume : Measure ℝ).restrict ((Set.Ioo (-δ) δ)ᶜ))
          (f := fun x => goldenRuleKernel t x * g x)
    _ ≤ ∫ x in (Set.Ioo (-δ) δ)ᶜ, (4 / δ ^ 2) * |g x| := by
        refine MeasureTheory.setIntegral_mono_on (hKg.abs.integrableOn) (habs.integrableOn)
          hmeas ?_
        intro x hx
        have habsx : δ ≤ |x| := abs_ge_of_notMem_Ioo hδ hx
        have hx0 : x ≠ 0 := by
          intro h; rw [h] at habsx; simp at habsx; linarith
        have hx2 : δ ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
        have hkle : goldenRuleKernel t x ≤ 4 / δ ^ 2 := by
          refine le_trans (goldenRuleKernel_le_four_div_sq t hx0) ?_
          have h1 : (0 : ℝ) < δ ^ 2 := by positivity
          have h2 : (0 : ℝ) < x ^ 2 := by positivity
          rw [div_le_div_iff₀ h2 h1]
          nlinarith
        rw [abs_mul, abs_of_nonneg (goldenRuleKernel_nonneg t x)]
        exact mul_le_mul_of_nonneg_right hkle (abs_nonneg _)
    _ ≤ ∫ x : ℝ, (4 / δ ^ 2) * |g x| := by
        refine MeasureTheory.setIntegral_le_integral habs ?_
        filter_upwards with x
        have : (0 : ℝ) ≤ 4 / δ ^ 2 := by positivity
        positivity
    _ = (4 / δ ^ 2) * ∫ x : ℝ, |g x| := MeasureTheory.integral_const_mul _ _

end Tail

end GaloisForLFunctions.HTGeometry
