import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropSevenOne
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# From the cancellation region to `Ĩ_m` (proof of Guth–Maynard Proposition 7.2, smoothing step)

Let `M ≤ |m₂|`, `δ > 0`, and `G = {v ∈ [1/2,2]² : |m₁v₁ + m₂v₂ + m₃| ≤ δ/N}` the region of
Proposition 7.1. Over each `v₁ ∈ [1/2, 2]` the fibre of `G` lies in `[1/2, 2] ∩ [c − r, c + r]` with
`c = (m₁v₁ + m₃)/(−m₂)` and `r = δ/(N|m₂|) ≤ δ/(NM)`. Cauchy–Schwarz on the fibre and the
majorisations

`NM ∫_{fibre} |R(v₂/v₁)|² dv₂ ≤ v₁ R̃(c/v₁)²`,   `NM ∫_{fibre} |R(v₂)|² dv₂ ≤ R̃(c)²`

(the inner bump `ψ̃₁ = innerBump (2δ)` is `1` on `[-2δ, 2δ]`, the outer bump is `1` on `[1/4, 4]`;
the first one after the substitution `v₂ = v₁x`) give

`∫_G |R(v₁) R(v₂/v₁) R(v₂)| dv ≤ (√2/(NM)) Ĩ_{(m₁, −m₂, m₃)}`

(`setIntegral_lagTripleNorm_le_smoothedCubicTerm`). With Proposition 7.1 this is the bound
`|I_m| ≪ (N²/M) Ĩ_{(m₁,−m₂,m₃)} + O(N³|W|³T^{−A})` of the paper (`norm_cubicTerm_le_smoothedCubicTerm`).
-/

set_option autoImplicit false

open MeasureTheory Set

namespace RHTower.GuthMaynard

noncomputable section

/-- The fibre `{v₂ ∈ [1/2, 2] : |m₁v₁ + m₂v₂ + m₃| ≤ δ}` of the cancellation region over `v₁`. -/
def cancellationFibre (m₁ m₂ m₃ : ℤ) (δ v₁ : ℝ) : Set ℝ :=
  {v₂ | v₂ ∈ Icc (1 / 2 : ℝ) 2 ∧ |(m₁ : ℝ) * v₁ + m₂ * v₂ + m₃| ≤ δ}

theorem measurableSet_cancellationFibre (m₁ m₂ m₃ : ℤ) (δ v₁ : ℝ) :
    MeasurableSet (cancellationFibre m₁ m₂ m₃ δ v₁) := by
  change MeasurableSet (Icc (1 / 2 : ℝ) 2 ∩ {v₂ | |(m₁ : ℝ) * v₁ + m₂ * v₂ + m₃| ≤ δ})
  exact measurableSet_Icc.inter
    (measurableSet_le (f := fun v₂ => |(m₁ : ℝ) * v₁ + m₂ * v₂ + m₃|) (by fun_prop)
      measurable_const)

theorem volume_cancellationFibre_ne_top (m₁ m₂ m₃ : ℤ) (δ v₁ : ℝ) :
    volume (cancellationFibre m₁ m₂ m₃ δ v₁) ≠ ⊤ :=
  ((measure_mono fun _ h => h.1).trans_lt measure_Icc_lt_top).ne

/-- Points of the fibre are within `δ/|m₂|` of `c = (m₁v₁ + m₃)/(−m₂)`. -/
theorem abs_sub_le_of_mem_cancellationFibre {m₁ m₂ m₃ : ℤ} (hm₂ : (m₂ : ℝ) ≠ 0) {δ v₁ y : ℝ}
    (hy : y ∈ cancellationFibre m₁ m₂ m₃ δ v₁) :
    |(m₁ * v₁ + m₃) / ((-m₂ : ℤ) : ℝ) - y| ≤ δ / |(m₂ : ℝ)| := by
  have hpos : 0 < |(m₂ : ℝ)| := abs_pos.mpr hm₂
  have : (m₁ * v₁ + m₃) / ((-m₂ : ℤ) : ℝ) - y = -((m₁ * v₁ + m₂ * y + m₃) / m₂) := by
    push_cast; field_simp; ring
  rw [this, abs_neg, abs_div, le_div_iff₀ hpos, div_mul_cancel₀ _ hpos.ne']
  exact hy.2

/-- **Fibre majorisation.** If on a finite-measure set `E` the outer bump is `1` at `y/a` and the
inner bump is `1` at `NM(c₀ − y/a)`, then `NM ∫_E |R(y/a)|² dy ≤ a R̃(c₀)²`. -/
theorem mul_setIntegral_normSq_lagSum_div_le {ψ₁ ψ₂ : ℝ → ℝ} (h : IsSmoothingPair ψ₁ ψ₂)
    {N M : ℝ} (hNM : 0 < N * M) (W : Finset ℝ) {E : Set ℝ} (hEm : MeasurableSet E)
    (hE : volume E ≠ ⊤) {a c₀ : ℝ} (ha : 0 < a)
    (h₁ : ∀ y ∈ E, 1 ≤ ψ₁ (N * M * (c₀ - y / a))) (h₂ : ∀ y ∈ E, 1 ≤ ψ₂ (y / a)) :
    N * M * ∫ y in E, ‖lagSum W (y / a)‖ ^ 2 ≤ a * smoothedLagSum ψ₁ ψ₂ N M W c₀ ^ 2 := by
  have hF := integrable_smoothedLagSumIntegrand h N M W c₀
  have hFa : Integrable fun y => smoothedLagSumIntegrand ψ₁ ψ₂ N M W c₀ (y / a) :=
    hF.comp_div ha.ne'
  have hint : IntegrableOn (fun y => ‖lagSum W (y / a)‖ ^ 2) E :=
    Measure.integrableOn_of_bounded hE
      ((measurable_norm_lagSum_sq W).comp (measurable_id.div_const a)).aestronglyMeasurable
      (M := (W.card : ℝ) ^ 2) (ae_of_all _ fun y => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_lagSum_le W _) 2)
  rw [smoothedLagSum_sq h hNM.le, ← integral_const_mul]
  calc ∫ y in E, N * M * ‖lagSum W (y / a)‖ ^ 2
      ≤ ∫ y in E, smoothedLagSumIntegrand ψ₁ ψ₂ N M W c₀ (y / a) := by
        refine setIntegral_mono_on (hint.const_mul _) hFa.integrableOn hEm fun y hy => ?_
        unfold smoothedLagSumIntegrand
        have := h₁ y hy
        have := h₂ y hy
        have h0 : 0 ≤ N * M * ‖lagSum W (y / a)‖ ^ 2 := by positivity
        calc N * M * ‖lagSum W (y / a)‖ ^ 2 = N * M * 1 * 1 * ‖lagSum W (y / a)‖ ^ 2 := by ring
          _ ≤ N * M * ψ₁ (N * M * (c₀ - y / a)) * ψ₂ (y / a) * ‖lagSum W (y / a)‖ ^ 2 := by
            gcongr
    _ ≤ ∫ y, smoothedLagSumIntegrand ψ₁ ψ₂ N M W c₀ (y / a) :=
        setIntegral_le_integral hFa
          (ae_of_all _ fun y => smoothedLagSumIntegrand_nonneg h hNM.le W c₀ _)
    _ = a * ∫ x, smoothedLagSumIntegrand ψ₁ ψ₂ N M W c₀ x := by
        rw [Measure.integral_comp_div (fun x => smoothedLagSumIntegrand ψ₁ ψ₂ N M W c₀ x) a,
          abs_of_pos ha, smul_eq_mul]

/-- `√(2a²/(NM)) √(b²/(NM)) = √2 ab/(NM)`. -/
theorem sqrt_mul_sqrt_eq {a b K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 0 < K) :
    Real.sqrt (2 * a ^ 2 / K) * Real.sqrt (b ^ 2 / K) = Real.sqrt 2 / K * (a * b) := by
  rw [← Real.sqrt_mul (by positivity)]
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have : 2 * a ^ 2 / K * (b ^ 2 / K) = (Real.sqrt 2 / K * (a * b)) ^ 2 := by
    rw [mul_pow, div_pow, h2]; field_simp
  rw [this, Real.sqrt_sq (by positivity)]

/-- Cauchy–Schwarz on one fibre:
`∫_{fibre} |R(v₂/v₁)| |R(v₂)| dv₂ ≤ (√2/(NM)) R̃(c/v₁) R̃(c)` with `c = (m₁v₁ + m₃)/(−m₂)`. -/
theorem setIntegral_fibre_le {N M δ : ℝ} (hN : 0 < N) (hM : 0 < M) (hδ : 0 < δ) (W : Finset ℝ)
    {m₁ m₂ m₃ : ℤ} (hm₂ : M ≤ |(m₂ : ℝ)|) {v₁ : ℝ} (hv₁ : v₁ ∈ Icc (1 / 2 : ℝ) 2) :
    ∫ v₂ in cancellationFibre m₁ m₂ m₃ (δ / N) v₁, ‖lagSum W (v₂ / v₁)‖ * ‖lagSum W v₂‖ ≤
      Real.sqrt 2 / (N * M) *
        (smoothedLagSum (innerBump (2 * δ)) outerBump N M W
            ((m₁ * v₁ + m₃) / (((-m₂ : ℤ) : ℝ) * v₁)) *
          smoothedLagSum (innerBump (2 * δ)) outerBump N M W ((m₁ * v₁ + m₃) / ((-m₂ : ℤ) : ℝ))) := by
  have hpair := isSmoothingPair_innerBump_outerBump (A := 2 * δ) (by positivity)
  have hNM : 0 < N * M := mul_pos hN hM
  have hm₂pos : 0 < |(m₂ : ℝ)| := hM.trans_le hm₂
  have hm₂0 : (m₂ : ℝ) ≠ 0 := abs_pos.mp hm₂pos
  have hv₁0 : 0 < v₁ := by linarith [hv₁.1]
  set E := cancellationFibre m₁ m₂ m₃ (δ / N) v₁ with hE
  have hEm := measurableSet_cancellationFibre m₁ m₂ m₃ (δ / N) v₁
  have hEf := volume_cancellationFibre_ne_top m₁ m₂ m₃ (δ / N) v₁
  set c := (m₁ * v₁ + m₃) / ((-m₂ : ℤ) : ℝ) with hc
  -- `NM |c − y| ≤ δ` on the fibre
  have hclose : ∀ y ∈ E, N * M * |c - y| ≤ δ := fun y hy => by
    have h := abs_sub_le_of_mem_cancellationFibre hm₂0 hy
    calc N * M * |c - y| ≤ N * M * (δ / N / |(m₂ : ℝ)|) := by gcongr
      _ = δ * (M / |(m₂ : ℝ)|) := by field_simp
      _ ≤ δ * 1 := by gcongr; exact (div_le_one hm₂pos).mpr hm₂
      _ = δ := mul_one δ
  have hout : ∀ y ∈ E, ∀ a ∈ Icc (1 / 2 : ℝ) 2, 1 ≤ outerBump (y / a) := fun y hy a ha => by
    have hy' := hy.1
    rw [outerBump_eq_one]
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ (by linarith [ha.1])]; nlinarith [hy'.1, ha.2]
    · rw [div_le_iff₀ (by linarith [ha.1])]; nlinarith [hy'.2, ha.1]
  -- the two fibre masses
  have hX : N * M * ∫ y in E, ‖lagSum W (y / v₁)‖ ^ 2 ≤
      2 * smoothedLagSum (innerBump (2 * δ)) outerBump N M W (c / v₁) ^ 2 := by
    refine (mul_setIntegral_normSq_lagSum_div_le hpair hNM W hEm hEf hv₁0 (c₀ := c / v₁)
      (fun y hy => ?_) (fun y hy => hout y hy v₁ hv₁)).trans ?_
    · refine (innerBump_eq_one (by positivity) ?_).ge
      have : N * M * (c / v₁ - y / v₁) = (N * M * (c - y)) / v₁ := by field_simp
      rw [this, abs_div, abs_of_pos hv₁0, div_le_iff₀ hv₁0, abs_mul, abs_of_pos hNM]
      nlinarith [hclose y hy, hv₁.1]
    · have := sq_nonneg (smoothedLagSum (innerBump (2 * δ)) outerBump N M W (c / v₁))
      nlinarith [hv₁.2]
  have hY : N * M * ∫ y in E, ‖lagSum W y‖ ^ 2 ≤
      smoothedLagSum (innerBump (2 * δ)) outerBump N M W c ^ 2 := by
    have h := mul_setIntegral_normSq_lagSum_div_le hpair hNM W hEm hEf one_pos
      (c₀ := c) (fun y hy => by
        rw [div_one]
        refine (innerBump_eq_one (by positivity) ?_).ge
        rw [abs_mul, abs_of_pos hNM]
        linarith [hclose y hy])
      (fun y hy => hout y hy 1 (by norm_num))
    simpa using h
  -- Cauchy–Schwarz on the fibre
  have hmeas₁ : AEStronglyMeasurable (fun y => ‖lagSum W (y / v₁)‖) (volume.restrict E) :=
    ((measurable_lagSum W).comp (measurable_id.div_const v₁)).norm.aestronglyMeasurable
  have hmeas₂ : AEStronglyMeasurable (fun y => ‖lagSum W y‖) (volume.restrict E) :=
    (measurable_lagSum W).norm.aestronglyMeasurable
  have hsq₁ : IntegrableOn (fun y => ‖lagSum W (y / v₁)‖ ^ 2) E :=
    Measure.integrableOn_of_bounded hEf
      ((measurable_norm_lagSum_sq W).comp (measurable_id.div_const v₁)).aestronglyMeasurable
      (M := (W.card : ℝ) ^ 2) (ae_of_all _ fun y => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_lagSum_le W _) 2)
  have hsq₂ : IntegrableOn (fun y => ‖lagSum W y‖ ^ 2) E :=
    Measure.integrableOn_of_bounded hEf (measurable_norm_lagSum_sq W).aestronglyMeasurable
      (M := (W.card : ℝ) ^ 2) (ae_of_all _ fun y => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_lagSum_le W _) 2)
  have hCS := GaloisForLFunctions.HTGeometry.sq_integral_mul_le hmeas₁ hmeas₂ hsq₁ hsq₂
  set X := ∫ y in E, ‖lagSum W (y / v₁)‖ ^ 2
  set Y := ∫ y in E, ‖lagSum W y‖ ^ 2
  have hX0 : 0 ≤ X := setIntegral_nonneg hEm fun _ _ => sq_nonneg _
  have hP0 : 0 ≤ ∫ y in E, ‖lagSum W (y / v₁)‖ * ‖lagSum W y‖ :=
    setIntegral_nonneg hEm fun _ _ => by positivity
  set a := smoothedLagSum (innerBump (2 * δ)) outerBump N M W (c / v₁)
  set b := smoothedLagSum (innerBump (2 * δ)) outerBump N M W c
  have ha0 : 0 ≤ a := smoothedLagSum_nonneg _ _ _ _ _ _
  have hb0 : 0 ≤ b := smoothedLagSum_nonneg _ _ _ _ _ _
  have hXle : X ≤ 2 * a ^ 2 / (N * M) := by rw [le_div_iff₀ hNM]; linarith
  have hYle : Y ≤ b ^ 2 / (N * M) := by rw [le_div_iff₀ hNM]; linarith
  have hcarg : (m₁ * v₁ + m₃) / (((-m₂ : ℤ) : ℝ) * v₁) = c / v₁ := by rw [hc, div_div]
  rw [hcarg]
  calc ∫ y in E, ‖lagSum W (y / v₁)‖ * ‖lagSum W y‖
      ≤ Real.sqrt (X * Y) := by
        have := Real.abs_le_sqrt hCS
        rwa [abs_of_nonneg hP0] at this
    _ = Real.sqrt X * Real.sqrt Y := Real.sqrt_mul hX0 Y
    _ ≤ Real.sqrt (2 * a ^ 2 / (N * M)) * Real.sqrt (b ^ 2 / (N * M)) := by
        gcongr
    _ = Real.sqrt 2 / (N * M) * (a * b) := sqrt_mul_sqrt_eq ha0 hb0 hNM

/-- **The smoothing step.** For `M ≤ |m₂|` and `δ > 0`,
`∫_{v ∈ [1/2,2]², |m₁v₁+m₂v₂+m₃| ≤ δ/N} |R(v₁)R(v₂/v₁)R(v₂)| dv ≤ (√2/(NM)) Ĩ_{(m₁,−m₂,m₃)}`,
with `R̃` built from `ψ̃₁ = innerBump (2δ)` and `ψ̃₂ = outerBump`. -/
theorem setIntegral_lagTripleNorm_le_smoothedCubicTerm {N M δ : ℝ} (hN : 0 < N) (hM : 0 < M)
    (hδ : 0 < δ) (W : Finset ℝ) {m₁ m₂ m₃ : ℤ} (hm₂ : M ≤ |(m₂ : ℝ)|) :
    ∫ v in cancellationRegion m₁ m₂ m₃ (δ / N), lagTripleNorm W v ≤
      Real.sqrt 2 / (N * M) *
        smoothedCubicTerm (innerBump (2 * δ)) outerBump N M W m₁ (-m₂) m₃ := by
  have hpair := isSmoothingPair_innerBump_outerBump (A := 2 * δ) (by positivity)
  have hNM : 0 < N * M := mul_pos hN hM
  set G := cancellationRegion m₁ m₂ m₃ (δ / N)
  have hGm := measurableSet_cancellationRegion m₁ m₂ m₃ (δ / N)
  set g : ℝ → ℝ := fun v₁ => ‖lagSum W v₁‖ *
    (Real.sqrt 2 / (N * M) *
      (smoothedLagSum (innerBump (2 * δ)) outerBump N M W
          ((m₁ * v₁ + m₃) / (((-m₂ : ℤ) : ℝ) * v₁)) *
        smoothedLagSum (innerBump (2 * δ)) outerBump N M W ((m₁ * v₁ + m₃) / ((-m₂ : ℤ) : ℝ))))
    with hg
  have hgint : IntegrableOn g (Icc (1 / 2 : ℝ) 2) := by
    have h := integrableOn_norm_lagSum_mul_smoothedLagSum hpair hNM W
      (a := fun v => (m₁ * v + m₃) / (((-m₂ : ℤ) : ℝ) * v))
      (b := fun v => (m₁ * v + m₃) / ((-m₂ : ℤ) : ℝ)) (by fun_prop) (by fun_prop)
    refine IntegrableOn.congr_fun (h.const_mul (Real.sqrt 2 / (N * M))) (fun v _ => ?_)
      measurableSet_Icc
    simp only [hg]; ring
  have hindint : Integrable (G.indicator (lagTripleNorm W)) :=
    (integrableOn_lagTripleNorm W m₁ m₂ m₃ (δ / N)).integrable_indicator hGm
  -- fibrewise bound
  have hfibre : ∀ v₁, ∫ v₂, G.indicator (lagTripleNorm W) (v₁, v₂) ≤
      (Icc (1 / 2 : ℝ) 2).indicator g v₁ := by
    intro v₁
    by_cases hv₁ : v₁ ∈ Icc (1 / 2 : ℝ) 2
    · have hrw : (fun v₂ => G.indicator (lagTripleNorm W) (v₁, v₂)) = fun v₂ =>
          ‖lagSum W v₁‖ * (cancellationFibre m₁ m₂ m₃ (δ / N) v₁).indicator
            (fun v₂ => ‖lagSum W (v₂ / v₁)‖ * ‖lagSum W v₂‖) v₂ := by
        funext v₂
        by_cases hv₂ : v₂ ∈ cancellationFibre m₁ m₂ m₃ (δ / N) v₁
        · have hmem : (v₁, v₂) ∈ G := ⟨⟨hv₁, hv₂.1⟩, by
            simpa [cubicLinearForm] using hv₂.2⟩
          rw [indicator_of_mem hmem, indicator_of_mem hv₂, lagTripleNorm]; ring
        · have hmem : (v₁, v₂) ∉ G := fun h => hv₂ ⟨h.1.2, by
            simpa [cubicLinearForm] using h.2⟩
          rw [indicator_of_notMem hmem, indicator_of_notMem hv₂, mul_zero]
      rw [hrw, integral_const_mul,
        integral_indicator (measurableSet_cancellationFibre m₁ m₂ m₃ (δ / N) v₁),
        indicator_of_mem hv₁]
      exact mul_le_mul_of_nonneg_left (setIntegral_fibre_le hN hM hδ W hm₂ hv₁) (norm_nonneg _)
    · have hzero : (fun v₂ => G.indicator (lagTripleNorm W) (v₁, v₂)) = fun _ => 0 := by
        funext v₂
        exact indicator_of_notMem (fun h => hv₁ h.1.1) _
      rw [hzero, integral_zero, indicator_of_notMem hv₁]
  calc ∫ v in G, lagTripleNorm W v
      = ∫ v₁, ∫ v₂, G.indicator (lagTripleNorm W) (v₁, v₂) := by
        rw [← integral_indicator hGm, Measure.volume_eq_prod]
        exact integral_prod _ (by rw [← Measure.volume_eq_prod]; exact hindint)
    _ ≤ ∫ v₁, (Icc (1 / 2 : ℝ) 2).indicator g v₁ :=
        integral_mono_of_nonneg (ae_of_all _ fun v₁ => integral_nonneg fun v₂ =>
          indicator_nonneg (fun v _ => lagTripleNorm_nonneg W v) _)
          (hgint.integrable_indicator measurableSet_Icc) (ae_of_all _ hfibre)
    _ = Real.sqrt 2 / (N * M) *
          smoothedCubicTerm (innerBump (2 * δ)) outerBump N M W m₁ (-m₂) m₃ := by
        rw [integral_indicator measurableSet_Icc, smoothedCubicTerm, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Icc fun v _ => ?_
        simp only [hg]; ring

/-- **Proposition 7.1 in smoothed form.** For every `η > 0` and `A` there is `C` such that for
`T ≥ 1`, `N > 0`, `0 < M ≤ |m₂|`:
`|I_m| ≤ C (N²/M) Ĩ_{(m₁,−m₂,m₃)} + C N³ |W|³ T^{−A}`, with `ψ̃₁ = innerBump (2T^η)`,
`ψ̃₂ = outerBump`. -/
theorem norm_cubicTerm_le_smoothedCubicTerm (w : CGLSmoothBump) {η : ℝ} (hη : 0 < η) (A : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (T N M : ℝ) (W : Finset ℝ) (m₁ m₂ m₃ : ℤ), 1 ≤ T → 0 < N → 0 < M →
      M ≤ |(m₂ : ℝ)| →
      ‖cubicTerm w W N m₁ m₂ m₃‖ ≤
        C * (N ^ 2 / M) * smoothedCubicTerm (innerBump (2 * T ^ η)) outerBump N M W m₁ (-m₂) m₃ +
          C * N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-A) := by
  obtain ⟨C, hC, hbound⟩ := prop71 w hη A
  refine ⟨2 * C, by positivity, fun T N M W m₁ m₂ m₃ hT hN hM hm₂ => ?_⟩
  have hTη : 0 < T ^ η := Real.rpow_pos_of_pos (by linarith) η
  have hsm := setIntegral_lagTripleNorm_le_smoothedCubicTerm hN hM hTη W (m₁ := m₁) (m₃ := m₃) hm₂
  have hI0 := smoothedCubicTerm_nonneg (innerBump (2 * T ^ η)) outerBump N M W m₁ (-m₂) m₃
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have herr : 0 ≤ C * N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-A) := by
    have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < T) (-A); positivity
  refine (hbound T N W m₁ m₂ m₃ hT hN).trans ?_
  have hmain : C * N ^ 3 * (∫ v in cancellationRegion m₁ m₂ m₃ (T ^ η / N), lagTripleNorm W v) ≤
      2 * C * (N ^ 2 / M) *
        smoothedCubicTerm (innerBump (2 * T ^ η)) outerBump N M W m₁ (-m₂) m₃ := by
    calc C * N ^ 3 * (∫ v in cancellationRegion m₁ m₂ m₃ (T ^ η / N), lagTripleNorm W v)
        ≤ C * N ^ 3 * (Real.sqrt 2 / (N * M) *
            smoothedCubicTerm (innerBump (2 * T ^ η)) outerBump N M W m₁ (-m₂) m₃) := by
          gcongr
      _ = C * Real.sqrt 2 * (N ^ 2 / M) *
            smoothedCubicTerm (innerBump (2 * T ^ η)) outerBump N M W m₁ (-m₂) m₃ := by
          field_simp
      _ ≤ 2 * C * (N ^ 2 / M) *
            smoothedCubicTerm (innerBump (2 * T ^ η)) outerBump N M W m₁ (-m₂) m₃ := by
          have h1 : C * Real.sqrt 2 ≤ 2 * C := by
            nlinarith [mul_le_mul_of_nonneg_left hsqrt hC]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) hI0
  have : C * N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-A) ≤ 2 * C * N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-A) := by
    linarith
  linarith

end

end RHTower.GuthMaynard
