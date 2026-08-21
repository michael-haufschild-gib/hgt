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

section Limit

/-- **The golden-rule limit.**  Against an integrable weight continuous at the resonance, the
golden-rule kernel concentrates: its normalized pairing converges to `2 π` times the value of the
weight at the resonance. -/
theorem tendsto_goldenRuleKernel_weight {g : ℝ → ℝ}
    (hg : Integrable g (volume : Measure ℝ)) (hc : ContinuousAt g 0) :
    Filter.Tendsto (fun t : ℝ => (∫ x : ℝ, goldenRuleKernel t x * g x) / t)
      Filter.atTop (nhds (2 * Real.pi * g 0)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / (8 * Real.pi) with hηdef
  have hηpos : 0 < η := by positivity
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ → |g x - g 0| ≤ η := by
    obtain ⟨δ, hδpos, hδ⟩ := Metric.tendsto_nhds_nhds.mp hc η hηpos
    refine ⟨δ, hδpos, fun x hx => le_of_lt ?_⟩
    have hdx : dist x (0 : ℝ) < δ := by simpa [Real.dist_eq] using hx
    simpa [Real.dist_eq] using hδ hdx
  set C₁ : ℝ := (4 + 4 / δ ^ 2) * Real.pi with hC₁def
  set C₂ : ℝ := (4 / δ ^ 2) * ∫ x : ℝ, |g x| with hC₂def
  set M : ℝ := |g 0| * C₁ + C₂ with hMdef
  have hC₁nn : 0 ≤ C₁ := by rw [hC₁def]; positivity
  have hC₂nn : 0 ≤ C₂ := by
    have hint : (0 : ℝ) ≤ ∫ x : ℝ, |g x| := MeasureTheory.integral_nonneg fun x => abs_nonneg _
    rw [hC₂def]
    positivity
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact add_nonneg (mul_nonneg (abs_nonneg _) hC₁nn) hC₂nn
  have key : ∀ t : ℝ, 0 < t →
      |(∫ x : ℝ, goldenRuleKernel t x * g x) / t - 2 * Real.pi * g 0|
        ≤ 2 * Real.pi * η + M / t := by
    intro t ht
    have ht' : t ≠ 0 := ne_of_gt ht
    have hS : MeasurableSet (Set.Ioo (-δ) δ) := measurableSet_Ioo
    have hK : Integrable (goldenRuleKernel t) (volume : Measure ℝ) := integrable_goldenRuleKernel t
    have hKg : Integrable (fun x : ℝ => goldenRuleKernel t x * g x) (volume : Measure ℝ) := by
      refine hg.bdd_mul (c := t ^ 2) (continuous_goldenRuleKernel t).aestronglyMeasurable ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (goldenRuleKernel_nonneg t x)]
      exact goldenRuleKernel_le_sq t x
    have hSfin : (volume : Measure ℝ) (Set.Ioo (-δ) δ) ≠ ⊤ := by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    have hconstOn : IntegrableOn (fun _ : ℝ => g 0) (Set.Ioo (-δ) δ) volume :=
      (integrableOn_const hSfin)
    have hgOn : IntegrableOn g (Set.Ioo (-δ) δ) volume := hg.integrableOn
    have hdiffOn : IntegrableOn (fun x : ℝ => g x - g 0) (Set.Ioo (-δ) δ) volume :=
      hgOn.sub hconstOn
    have hKdiffOn : IntegrableOn (fun x : ℝ => goldenRuleKernel t x * (g x - g 0))
        (Set.Ioo (-δ) δ) volume := by
      refine hdiffOn.bdd_mul (c := t ^ 2)
        ((continuous_goldenRuleKernel t).aestronglyMeasurable.restrict) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (goldenRuleKernel_nonneg t x)]
      exact goldenRuleKernel_le_sq t x
    have hKconstOn : IntegrableOn (fun x : ℝ => goldenRuleKernel t x * g 0)
        (Set.Ioo (-δ) δ) volume := hK.integrableOn.mul_const _
    set A : ℝ := ∫ x in Set.Ioo (-δ) δ, goldenRuleKernel t x * (g x - g 0) with hAdef
    set R : ℝ := ∫ x in (Set.Ioo (-δ) δ)ᶜ, goldenRuleKernel t x with hRdef
    set B : ℝ := ∫ x in (Set.Ioo (-δ) δ)ᶜ, goldenRuleKernel t x * g x with hBdef
    have hmass : (∫ x in Set.Ioo (-δ) δ, goldenRuleKernel t x) = 2 * Real.pi * t - R := by
      have h := MeasureTheory.integral_add_compl hS hK
      rw [integral_goldenRuleKernel ht.le] at h
      rw [hRdef]
      linarith
    have hinner : (∫ x in Set.Ioo (-δ) δ, goldenRuleKernel t x * g x)
        = A + (2 * Real.pi * t - R) * g 0 := by
      have hpt : ∀ x : ℝ, goldenRuleKernel t x * g x
          = goldenRuleKernel t x * (g x - g 0) + goldenRuleKernel t x * g 0 := by
        intro x; ring
      rw [funext hpt, MeasureTheory.integral_add hKdiffOn hKconstOn,
        MeasureTheory.integral_mul_const, hmass, hAdef]
    have hid : (∫ x : ℝ, goldenRuleKernel t x * g x) = A + (2 * Real.pi * t - R) * g 0 + B := by
      have h := MeasureTheory.integral_add_compl hS hKg
      rw [hinner, ← hBdef] at h
      linarith
    have hRnn : 0 ≤ R := by
      rw [hRdef]
      exact MeasureTheory.setIntegral_nonneg hS.compl fun x _ => goldenRuleKernel_nonneg t x
    have hRle : R ≤ C₁ := by
      rw [hRdef, hC₁def]; exact setIntegral_goldenRuleKernel_tail_le hδpos t
    have hBle : |B| ≤ C₂ := by
      rw [hBdef, hC₂def]; exact abs_setIntegral_goldenRuleKernel_tail_mul_le hδpos t hg
    have hAle : |A| ≤ η * (2 * Real.pi * t) := by
      have h1 : |A| ≤ ∫ x in Set.Ioo (-δ) δ, |goldenRuleKernel t x * (g x - g 0)| := by
        rw [hAdef]
        simpa using MeasureTheory.abs_integral_le_integral_abs
          (μ := (volume : Measure ℝ).restrict (Set.Ioo (-δ) δ))
          (f := fun x => goldenRuleKernel t x * (g x - g 0))
      have h2 : (∫ x in Set.Ioo (-δ) δ, |goldenRuleKernel t x * (g x - g 0)|)
          ≤ ∫ x in Set.Ioo (-δ) δ, η * goldenRuleKernel t x := by
        refine MeasureTheory.setIntegral_mono_on hKdiffOn.abs
          (hK.integrableOn.const_mul _) hS ?_
        intro x hx
        have hxabs : |x| < δ := abs_lt.mpr ⟨hx.1, hx.2⟩
        rw [abs_mul, abs_of_nonneg (goldenRuleKernel_nonneg t x), mul_comm]
        exact mul_le_mul_of_nonneg_right (hδ x hxabs) (goldenRuleKernel_nonneg t x)
      have h3 : (∫ x in Set.Ioo (-δ) δ, η * goldenRuleKernel t x)
          = η * (2 * Real.pi * t - R) := by
        rw [MeasureTheory.integral_const_mul, hmass]
      have h4 : η * (2 * Real.pi * t - R) ≤ η * (2 * Real.pi * t) := by
        have : (2 : ℝ) * Real.pi * t - R ≤ 2 * Real.pi * t := by linarith
        exact mul_le_mul_of_nonneg_left this hηpos.le
      linarith
    have halg : (A + (2 * Real.pi * t - R) * g 0 + B) / t - 2 * Real.pi * g 0
        = (A - g 0 * R + B) / t := by
      field_simp
      ring
    rw [hid, halg, abs_div, abs_of_pos ht]
    have hnum : |A - g 0 * R + B| ≤ η * (2 * Real.pi * t) + M := by
      have h1 : |A - g 0 * R + B| ≤ |A| + |g 0 * R| + |B| := by
        have hA1 := neg_abs_le A
        have hA2 := le_abs_self A
        have hB1 := neg_abs_le B
        have hB2 := le_abs_self B
        have hR1 := neg_abs_le (g 0 * R)
        have hR2 := le_abs_self (g 0 * R)
        rw [abs_le]
        constructor <;> linarith
      have h2 : |g 0 * R| ≤ |g 0| * C₁ := by
        rw [abs_mul, abs_of_nonneg hRnn]
        exact mul_le_mul_of_nonneg_left hRle (abs_nonneg _)
      rw [hMdef]
      linarith
    calc |A - g 0 * R + B| / t ≤ (η * (2 * Real.pi * t) + M) / t := by gcongr
      _ = 2 * Real.pi * η + M / t := by field_simp
  refine ⟨2 * M / ε + 1, fun t ht => ?_⟩
  have hT : (0 : ℝ) < 2 * M / ε + 1 := by positivity
  have ht0 : 0 < t := lt_of_lt_of_le hT ht
  have hMt : M / t < ε / 2 := by
    rw [div_lt_iff₀ ht0]
    have h1 : ε / 2 * (2 * M / ε + 1) = M + ε / 2 := by field_simp
    have h2 : ε / 2 * (2 * M / ε + 1) ≤ ε / 2 * t :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    linarith
  have hηval : 2 * Real.pi * η = ε / 4 := by rw [hηdef]; field_simp; ring
  have hmain := key t ht0
  rw [Real.dist_eq]
  rw [hηval] at hmain
  linarith

/-- **Fermi's golden rule, analytic form.**  For an integrable density continuous at `E₀`, the
kernel integral centred at `E₀` grows linearly in time with slope `2 π ρ E₀`. -/
theorem tendsto_goldenRuleKernel_density {ρ : ℝ → ℝ} {E₀ : ℝ}
    (hρ : Integrable ρ (volume : Measure ℝ)) (hc : ContinuousAt ρ E₀) :
    Filter.Tendsto (fun t : ℝ => (∫ E : ℝ, goldenRuleKernel t (E - E₀) * ρ E) / t)
      Filter.atTop (nhds (2 * Real.pi * ρ E₀)) := by
  set g : ℝ → ℝ := fun x => ρ (x + E₀) with hgdef
  have hmp : MeasurePreserving (fun x : ℝ => x + E₀) volume volume :=
    measurePreserving_add_right volume E₀
  have hgint : Integrable g (volume : Measure ℝ) :=
    (hmp.integrable_comp hρ.aestronglyMeasurable).mpr hρ
  have hg0 : g 0 = ρ E₀ := by simp [hgdef]
  have hgc : ContinuousAt g 0 := by
    have h1 : ContinuousAt (fun x : ℝ => x + E₀) 0 := by fun_prop
    have h2 : ContinuousAt ρ ((fun x : ℝ => x + E₀) 0) := by simpa using hc
    have hcomp := h2.comp h1
    simpa [hgdef, Function.comp] using hcomp
  have hshift : ∀ t : ℝ, (∫ E : ℝ, goldenRuleKernel t (E - E₀) * ρ E)
      = ∫ x : ℝ, goldenRuleKernel t x * g x := by
    intro t
    have h := MeasureTheory.integral_add_right_eq_self
      (fun E : ℝ => goldenRuleKernel t (E - E₀) * ρ E) E₀
    rw [← h]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [hgdef]
  have := tendsto_goldenRuleKernel_weight hgint hgc
  rw [hg0] at this
  refine this.congr fun t => ?_
  rw [hshift t]

end Limit

end GaloisForLFunctions.HTGeometry
