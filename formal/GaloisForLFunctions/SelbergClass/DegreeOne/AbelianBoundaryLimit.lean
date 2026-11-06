import GaloisForLFunctions.SelbergClass.ComplexRayMellinInversion

/-!
# An Abelian limit for the Laplace transform of a slowly oscillating function

Let `r` be bounded with `r(t) → c` as `t → ∞`, let `ϑ` be real and `a = 1 − iϑ`, and set

`I(w) = ∫₀^∞ r(t) t^{−iϑ} e^{−wt} dt`,   `Re w > 0`.

As `ε → 0⁺` along `w = ε + iτ`:

* if `τ/ε → 0`, then `ε^a I(w) → c Γ(a)` (`tendsto_abelIntegral_resonant`);
* if `τ → τ₀ ≠ 0`, then `ε |I(w)| → 0` (`tendsto_abelIntegral_off`).

The constant part of `r` is computed exactly by the Laplace transform of `t^{−iϑ}`, extended from real
to complex `w` by the identity theorem.  The rest of `r` is `o(1/ε)` uniformly in `τ`.
-/

noncomputable section

set_option autoImplicit false

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace GaloisForLFunctions.SelbergClass.DegreeOne

/-- The kernel `t^{−iϑ} e^{−wt}`. -/
def abelKernel (ϑ : ℝ) (w : ℂ) (t : ℝ) : ℂ := (t : ℂ) ^ (-(I * (ϑ : ℂ))) * cexp (-(w * (t : ℂ)))

/-- The exponent `a = 1 − iϑ`. -/
def abelExponent (ϑ : ℝ) : ℂ := 1 - I * (ϑ : ℂ)

/-- The transform `I(w)`. -/
def abelIntegral (r : ℝ → ℂ) (ϑ : ℝ) (w : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), r t * abelKernel ϑ w t

theorem abelExponent_re (ϑ : ℝ) : (abelExponent ϑ).re = 1 := by simp [abelExponent]

theorem abelExponent_im (ϑ : ℝ) : (abelExponent ϑ).im = -ϑ := by simp [abelExponent]

theorem norm_abelKernel (ϑ : ℝ) (w : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖abelKernel ϑ w t‖ = Real.exp (-w.re * t) := by
  unfold abelKernel
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  simp

theorem measurable_abelKernel (ϑ : ℝ) (w : ℂ) : Measurable (abelKernel ϑ w) := by
  unfold abelKernel
  exact (Complex.measurable_ofReal.pow_const _).mul (by fun_prop)

theorem integrableOn_abelKernel (ϑ : ℝ) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (abelKernel ϑ w) (Ioi 0) := by
  refine (exp_neg_integrableOn_Ioi 0 hw).mono' (measurable_abelKernel ϑ w).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (norm_abelKernel ϑ w ht).le

/-- `∫₀^∞ e^{−bt} dt = 1/b`. -/
theorem integral_exp_neg_mul_Ioi' {b : ℝ} (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-b * t) = 1 / b := by
  rw [integral_exp_mul_Ioi (by linarith : -b < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  rw [neg_div_neg_eq]

/-- The Laplace transform of `t^{−iϑ}` is holomorphic on the right half-plane. -/
theorem differentiableAt_integral_abelKernel (ϑ : ℝ) {w₀ : ℂ} (hw₀ : 0 < w₀.re) :
    DifferentiableAt ℂ (fun w : ℂ => ∫ t in Ioi (0 : ℝ), abelKernel ϑ w t) w₀ := by
  set δ : ℝ := w₀.re / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hS : {w : ℂ | δ < w.re} ∈ 𝓝 w₀ :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
      simp only [mem_setOf_eq, hδ]
      linarith)
  let F' : ℂ → ℝ → ℂ := fun w t => abelKernel ϑ w t * (-(t : ℂ))
  have hmeas : ∀ w : ℂ, Measurable (F' w) := fun w =>
    (measurable_abelKernel ϑ w).mul (by fun_prop)
  have hbound : IntegrableOn (fun t : ℝ => 2 / δ * Real.exp (-(δ / 2) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by positivity : 0 < δ / 2)).const_mul _
  have hd : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ w ∈ {w : ℂ | δ < w.re},
      ‖F' w t‖ ≤ 2 / δ * Real.exp (-(δ / 2) * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    have ht0 : (0 : ℝ) < t := ht
    have hw' : δ < w.re := hw
    dsimp only [F']
    rw [norm_mul, norm_abelKernel ϑ w ht0, norm_neg, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    have h1 : t ≤ 2 / δ * Real.exp (δ / 2 * t) := by
      have h := Real.add_one_le_exp (δ / 2 * t)
      have e : 2 / δ * (δ / 2 * t) = t := by field_simp
      calc t = 2 / δ * (δ / 2 * t) := e.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : Real.exp (-w.re * t) ≤ Real.exp (-δ * t) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h3 : Real.exp (-δ * t) * Real.exp (δ / 2 * t) = Real.exp (-(δ / 2) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc Real.exp (-w.re * t) * t ≤ Real.exp (-δ * t) * (2 / δ * Real.exp (δ / 2 * t)) :=
          mul_le_mul h2 h1 ht0.le (Real.exp_pos _).le
      _ = 2 / δ * (Real.exp (-δ * t) * Real.exp (δ / 2 * t)) := by ring
      _ = _ := by rw [h3]
  have hdiff : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ w ∈ {w : ℂ | δ < w.re},
      HasDerivAt (fun w : ℂ => abelKernel ϑ w t) (F' w t) w := by
    refine Eventually.of_forall fun t w _ => ?_
    have h0 : HasDerivAt (fun w : ℂ => -(w * (t : ℂ))) (-(t : ℂ)) w := by
      have h := (hasDerivAt_id w).const_mul (-(t : ℂ))
      simp only [id_eq, mul_one] at h
      have e : (fun w : ℂ => -(w * (t : ℂ))) = fun y => -(t : ℂ) * y := by
        funext v
        ring
      rw [e]
      exact h
    have h1 := h0.cexp.const_mul ((t : ℂ) ^ (-(I * (ϑ : ℂ))))
    simp only [F', abelKernel, mul_assoc]
    exact h1
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun w t => abelKernel ϑ w t)
    (F' := F') hS (Eventually.of_forall fun w => (measurable_abelKernel ϑ w).aestronglyMeasurable)
    (integrableOn_abelKernel ϑ hw₀) (hmeas w₀).aestronglyMeasurable hd hbound
    hdiff).2.differentiableAt

/-- **The Laplace transform of `t^{−iϑ}` at a complex point.** -/
theorem integral_abelKernel (ϑ : ℝ) {w : ℂ} (hw : 0 < w.re) :
    ∫ t in Ioi (0 : ℝ), abelKernel ϑ w t = (1 / w) ^ abelExponent ϑ * Complex.Gamma (abelExponent ϑ) := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hL : AnalyticOnNhd ℂ (fun w : ℂ => ∫ t in Ioi (0 : ℝ), abelKernel ϑ w t) {w : ℂ | 0 < w.re} :=
    DifferentiableOn.analyticOnNhd
      (fun w hw => (differentiableAt_integral_abelKernel ϑ hw).differentiableWithinAt) hopen
  have hR : AnalyticOnNhd ℂ (fun w : ℂ => (1 / w) ^ abelExponent ϑ * Complex.Gamma (abelExponent ϑ))
      {w : ℂ | 0 < w.re} := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hopen
    have hw0 : w ≠ 0 := by
      intro h
      rw [h] at hw
      simp at hw
    have hslit : 1 / w ∈ Complex.slitPlane := by
      refine Or.inl ?_
      rw [one_div, Complex.inv_re]
      exact div_pos hw (Complex.normSq_pos.mpr hw0)
    have hd : DifferentiableAt ℂ (fun w : ℂ => 1 / w) w :=
      (differentiableAt_const _).div differentiableAt_id hw0
    exact ((hd.cpow (differentiableAt_const _) hslit).mul_const _).differentiableWithinAt
  refine eqOn_rightHalfPlane_of_eq_on_pos_reals hL hR (fun x hx => ?_) hw
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := abelExponent ϑ) (r := x)
    (by rw [abelExponent_re]; norm_num) hx
  have e : abelExponent ϑ - 1 = -(I * (ϑ : ℂ)) := by
    simp [abelExponent]
  rw [e] at h
  exact h

/-! ### The error term -/

/-- The weighted mass of `r − c`. -/
def abelError (r : ℝ → ℂ) (c : ℂ) (ε : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), ‖r t - c‖ * Real.exp (-ε * t)

theorem integrableOn_mul_abelKernel {r : ℝ → ℂ} {R : ℝ}
    (hr : AEStronglyMeasurable r (volume.restrict (Ioi 0))) (hb : ∀ t, 0 < t → ‖r t‖ ≤ R) (ϑ : ℝ)
    {w : ℂ} (hw : 0 < w.re) : IntegrableOn (fun t => r t * abelKernel ϑ w t) (Ioi 0) := by
  refine ((exp_neg_integrableOn_Ioi 0 hw).const_mul R).mono'
    (hr.mul (measurable_abelKernel ϑ w).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, norm_abelKernel ϑ w ht]
  exact mul_le_mul_of_nonneg_right (hb t ht) (Real.exp_pos _).le

/-- `|I(w)| ≤ R/Re w`. -/
theorem norm_abelIntegral_le {r : ℝ → ℂ} {R : ℝ} (hb : ∀ t, 0 < t → ‖r t‖ ≤ R) (ϑ : ℝ) {w : ℂ}
    (hw : 0 < w.re) : ‖abelIntegral r ϑ w‖ ≤ R / w.re := by
  have hint : IntegrableOn (fun t : ℝ => R * Real.exp (-w.re * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hw).const_mul R
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ))) hint
    (f := fun t => r t * abelKernel ϑ w t) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, norm_abelKernel ϑ w ht]
      exact mul_le_mul_of_nonneg_right (hb t ht) (Real.exp_pos _).le)
  refine h.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_neg_mul_Ioi' hw, mul_one_div]

theorem norm_abelIntegral_sub_le {r : ℝ → ℂ} {R : ℝ}
    (hr : AEStronglyMeasurable r (volume.restrict (Ioi 0))) (hb : ∀ t, 0 < t → ‖r t‖ ≤ R) (c : ℂ)
    (ϑ : ℝ) {w : ℂ} (hw : 0 < w.re) :
    ‖abelIntegral r ϑ w - c * ((1 / w) ^ abelExponent ϑ * Complex.Gamma (abelExponent ϑ))‖ ≤
      abelError r c w.re := by
  have h1 := integrableOn_mul_abelKernel hr hb ϑ hw
  have h2 := (integrableOn_abelKernel ϑ hw).const_mul c
  have hsub : abelIntegral r ϑ w - c * ((1 / w) ^ abelExponent ϑ * Complex.Gamma (abelExponent ϑ)) =
      ∫ t in Ioi (0 : ℝ), (r t - c) * abelKernel ϑ w t := by
    rw [← integral_abelKernel ϑ hw, ← integral_const_mul, abelIntegral, ← integral_sub h1 h2]
    exact integral_congr_ae (Eventually.of_forall fun t => by simp only [sub_mul])
  rw [hsub]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [norm_mul, norm_abelKernel ϑ w ht]

/-- **The non-constant part is `o(1/ε)`.** -/
theorem tendsto_mul_abelError {r : ℝ → ℂ} {c : ℂ} {R : ℝ} (hb : ∀ t, 0 < t → ‖r t‖ ≤ R)
    (hlim : Tendsto r atTop (𝓝 c)) :
    Tendsto (fun ε : ℝ => ε * abelError r c ε) (𝓝[>] 0) (𝓝 0) := by
  refine Metric.tendsto_nhds.mpr fun η hη => ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (η / 4) (by positivity)
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = max N 1 := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := hT ▸ le_max_right _ _
  have hT0 : 0 < T := by linarith
  have hTN : N ≤ T := hT ▸ le_max_left _ _
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = |R| + ‖c‖ := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hM]
    positivity
  have hbd : ∀ t, 0 < t → ‖r t - c‖ ≤ M := fun t ht => by
    rw [hM]
    exact (norm_sub_le _ _).trans (add_le_add ((hb t ht).trans (le_abs_self R)) le_rfl)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = M * Real.exp 1 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = η / (2 * (A * T + 1)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδ]
    positivity
  filter_upwards [Ioo_mem_nhdsGT hδ0] with ε hε
  have hε0 : 0 < ε := hε.1
  have hb1 : 0 < 1 / T := by positivity
  have hg1 := (exp_neg_integrableOn_Ioi 0 hε0).const_mul (η / 4)
  have hg2 := (exp_neg_integrableOn_Ioi 0 hb1).const_mul A
  have hE : abelError r c ε ≤ (η / 4) * (1 / ε) + A * T := by
    have hmono := integral_mono_of_nonneg (μ := volume.restrict (Ioi (0 : ℝ)))
      (f := fun t => ‖r t - c‖ * Real.exp (-ε * t))
      (g := fun t => η / 4 * Real.exp (-ε * t) + A * Real.exp (-(1 / T) * t))
      (Eventually.of_forall fun t => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
      (hg1.add hg2) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : (0 : ℝ) < t := ht
        have hE1 := Real.exp_pos (-ε * t)
        have hE2 := Real.exp_pos (-(1 / T) * t)
        rcases le_total T t with htT | htT
        · have h := hN t (hTN.trans htT)
          rw [dist_eq_norm] at h
          have h1 : ‖r t - c‖ * Real.exp (-ε * t) ≤ η / 4 * Real.exp (-ε * t) :=
            mul_le_mul_of_nonneg_right h.le hE1.le
          have h2 : 0 ≤ A * Real.exp (-(1 / T) * t) := by positivity
          linarith
        · have hE1' : Real.exp (-ε * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
          have hM1 : ‖r t - c‖ * Real.exp (-ε * t) ≤ M :=
            (mul_le_of_le_one_right (norm_nonneg _) hE1').trans (hbd t ht0)
          have hexp : 1 ≤ Real.exp 1 * Real.exp (-(1 / T) * t) := by
            rw [← Real.exp_add]
            refine Real.one_le_exp ?_
            have : (1 / T) * t ≤ 1 := by
              rw [one_div, inv_mul_le_iff₀ hT0]
              linarith
            linarith
          have hM2 : M ≤ A * Real.exp (-(1 / T) * t) := by
            rw [hA, mul_assoc]
            exact le_mul_of_one_le_right hM0 hexp
          have h3 : 0 ≤ η / 4 * Real.exp (-ε * t) := by positivity
          linarith)
    refine hmono.trans (le_of_eq ?_)
    rw [integral_add hg1 hg2, integral_const_mul, integral_const_mul, integral_exp_neg_mul_Ioi' hε0,
      integral_exp_neg_mul_Ioi' hb1, one_div_one_div]
  have hE0 : 0 ≤ abelError r c ε :=
    setIntegral_nonneg measurableSet_Ioi fun t _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hval : ε * ((η / 4) * (1 / ε) + A * T) = η / 4 + ε * (A * T) := by
    field_simp
  have hAT : 0 ≤ A * T := by positivity
  have hδAT : δ * (A * T) ≤ η / 2 := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hεAT : ε * (A * T) ≤ δ * (A * T) := mul_le_mul_of_nonneg_right hε.2.le hAT
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hε0.le hE0)]
  calc ε * abelError r c ε ≤ ε * ((η / 4) * (1 / ε) + A * T) :=
        mul_le_mul_of_nonneg_left hE hε0.le
    _ = η / 4 + ε * (A * T) := hval
    _ < η := by linarith

theorem ofReal_mul_cpow {x : ℝ} (hx : 0 < x) {z : ℂ} (hz : z ≠ 0) (a : ℂ) :
    ((x : ℂ) * z) ^ a = (x : ℂ) ^ a * z ^ a := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hx0 hz), Complex.log_ofReal_mul hx hz, add_mul,
    Complex.exp_add, Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hz,
    Complex.ofReal_log hx.le]

theorem norm_ofReal_cpow_abelExponent {x : ℝ} (hx : 0 < x) (ϑ : ℝ) :
    ‖(x : ℂ) ^ abelExponent ϑ‖ = x := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, abelExponent_re, Real.rpow_one]

variable {ι : Type*} {l : Filter ι} {ε τ : ι → ℝ} {r : ℝ → ℂ} {c : ℂ} {R : ℝ}

/-- **The resonant limit.**  If `τ/ε → 0`, then `ε^a I(ε + iτ) → c Γ(a)`. -/
theorem tendsto_abelIntegral_resonant (hr : AEStronglyMeasurable r (volume.restrict (Ioi 0)))
    (hb : ∀ t, 0 < t → ‖r t‖ ≤ R) (hlim : Tendsto r atTop (𝓝 c)) (ϑ : ℝ)
    (hεpos : ∀ᶠ i in l, 0 < ε i) (hε0 : Tendsto ε l (𝓝 0))
    (hτ : Tendsto (fun i => τ i / ε i) l (𝓝 0)) :
    Tendsto (fun i => (ε i : ℂ) ^ abelExponent ϑ *
      abelIntegral r ϑ ((ε i : ℂ) + (τ i : ℂ) * I)) l (𝓝 (c * Complex.Gamma (abelExponent ϑ))) := by
  have hε' : Tendsto ε l (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hε0, hεpos⟩
  have herr := (tendsto_mul_abelError hb hlim).comp hε'
  -- the ratio `ε/w`
  have hu : Tendsto (fun i => (1 + ((τ i / ε i : ℝ) : ℂ) * I)⁻¹) l (𝓝 1) := by
    have h0 : Tendsto (fun i => (1 : ℂ) + ((τ i / ε i : ℝ) : ℂ) * I) l (𝓝 (1 + ((0 : ℝ) : ℂ) * I)) :=
      tendsto_const_nhds.add (((Complex.continuous_ofReal.tendsto _).comp hτ).mul_const I)
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h0
    simpa using h0.inv₀ one_ne_zero
  have hpow : Tendsto (fun i => ((1 + ((τ i / ε i : ℝ) : ℂ) * I)⁻¹) ^ abelExponent ϑ) l (𝓝 1) := by
    have h := (continuousAt_cpow_const (b := abelExponent ϑ)
      (a := (1 : ℂ)) (by simp)).tendsto.comp hu
    simpa [Function.comp_def] using h
  have hmain := hpow.mul_const (c * Complex.Gamma (abelExponent ϑ))
  rw [one_mul] at hmain
  have hsmall : Tendsto (fun i => (ε i : ℂ) ^ abelExponent ϑ *
      (abelIntegral r ϑ ((ε i : ℂ) + (τ i : ℂ) * I) - c * ((1 / ((ε i : ℂ) + (τ i : ℂ) * I)) ^
        abelExponent ϑ * Complex.Gamma (abelExponent ϑ)))) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ herr
    filter_upwards [hεpos] with i hi
    have hw : 0 < ((ε i : ℂ) + (τ i : ℂ) * I).re := by simpa using hi
    have h := norm_abelIntegral_sub_le hr hb c ϑ hw
    have hre : ((ε i : ℂ) + (τ i : ℂ) * I).re = ε i := by simp
    rw [hre] at h
    rw [norm_mul, norm_ofReal_cpow_abelExponent hi]
    exact mul_le_mul_of_nonneg_left h hi.le
  have hsum := hmain.add hsmall
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hεpos] with i hi
  have hεc : (ε i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hi.ne'
  have hw0 : (ε i : ℂ) + (τ i : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hi.ne' this
  have hquot : (ε i : ℂ) * (1 / ((ε i : ℂ) + (τ i : ℂ) * I)) =
      (1 + ((τ i / ε i : ℝ) : ℂ) * I)⁻¹ := by
    have h1 : (1 : ℂ) + ((τ i / ε i : ℝ) : ℂ) * I = ((ε i : ℂ) + (τ i : ℂ) * I) / (ε i : ℂ) := by
      push_cast
      field_simp
    rw [h1, inv_div, mul_one_div]
  rw [← hquot, ofReal_mul_cpow hi (one_div_ne_zero hw0)]
  ring

/-- **The non-resonant limit.**  If `τ → τ₀ ≠ 0`, then `ε |I(ε + iτ)| → 0`. -/
theorem tendsto_abelIntegral_off (hr : AEStronglyMeasurable r (volume.restrict (Ioi 0)))
    (hb : ∀ t, 0 < t → ‖r t‖ ≤ R) (hlim : Tendsto r atTop (𝓝 c)) (ϑ : ℝ)
    (hεpos : ∀ᶠ i in l, 0 < ε i) (hε0 : Tendsto ε l (𝓝 0)) {τ₀ : ℝ} (hτ : Tendsto τ l (𝓝 τ₀))
    (hτ₀ : τ₀ ≠ 0) :
    Tendsto (fun i => ε i * ‖abelIntegral r ϑ ((ε i : ℂ) + (τ i : ℂ) * I)‖) l (𝓝 0) := by
  have hε' : Tendsto ε l (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hε0, hεpos⟩
  have herr := (tendsto_mul_abelError hb hlim).comp hε'
  have hτpos : 0 < |τ₀| := abs_pos.mpr hτ₀
  have hτev : ∀ᶠ i in l, |τ₀| / 2 < |τ i| :=
    (continuous_abs.tendsto τ₀).comp hτ |>.eventually (lt_mem_nhds (by linarith))
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ‖c‖ * ((2 / |τ₀| * Real.exp (π * |ϑ|)) *
      ‖Complex.Gamma (abelExponent ϑ)‖) := ⟨_, rfl⟩
  have hlin : Tendsto (fun i => ε i * B + (Function.comp (fun ε : ℝ => ε * abelError r c ε) ε) i) l
      (𝓝 (0 * B + 0)) := (hε0.mul_const B).add herr
  rw [zero_mul, add_zero] at hlin
  refine squeeze_zero' ?_ ?_ hlin
  · filter_upwards [hεpos] with i hi
    exact mul_nonneg hi.le (norm_nonneg _)
  · filter_upwards [hεpos, hτev] with i hi hτi
    have hw : 0 < ((ε i : ℂ) + (τ i : ℂ) * I).re := by simpa using hi
    have h := norm_abelIntegral_sub_le hr hb c ϑ hw
    have hre : ((ε i : ℂ) + (τ i : ℂ) * I).re = ε i := by simp
    rw [hre] at h
    -- the exact main term is bounded
    have hw1 : |τ₀| / 2 ≤ ‖(ε i : ℂ) + (τ i : ℂ) * I‖ := by
      have him := Complex.abs_im_le_norm ((ε i : ℂ) + (τ i : ℂ) * I)
      have : ((ε i : ℂ) + (τ i : ℂ) * I).im = τ i := by simp
      rw [this] at him
      linarith
    have hnw : ‖1 / ((ε i : ℂ) + (τ i : ℂ) * I)‖ ≤ 2 / |τ₀| := by
      rw [norm_div, norm_one, div_le_div_iff₀ (by linarith) hτpos]
      linarith
    have hcp : ‖(1 / ((ε i : ℂ) + (τ i : ℂ) * I)) ^ abelExponent ϑ‖ ≤
        2 / |τ₀| * Real.exp (π * |ϑ|) := by
      refine (Complex.norm_cpow_le _ _).trans ?_
      rw [abelExponent_re, abelExponent_im, Real.rpow_one, div_eq_mul_inv, ← Real.exp_neg]
      refine mul_le_mul hnw (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by positivity)
      have harg := Complex.abs_arg_le_pi (1 / ((ε i : ℂ) + (τ i : ℂ) * I))
      have h1 : -(Complex.arg (1 / ((ε i : ℂ) + (τ i : ℂ) * I)) * -ϑ) ≤
          |Complex.arg (1 / ((ε i : ℂ) + (τ i : ℂ) * I))| * |ϑ| := by
        have := le_abs_self (Complex.arg (1 / ((ε i : ℂ) + (τ i : ℂ) * I)) * ϑ)
        rw [abs_mul] at this
        linarith
      exact h1.trans (mul_le_mul_of_nonneg_right harg (abs_nonneg ϑ))
    have hmainB : ‖c * ((1 / ((ε i : ℂ) + (τ i : ℂ) * I)) ^ abelExponent ϑ *
        Complex.Gamma (abelExponent ϑ))‖ ≤ B := by
      rw [hB, norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcp (norm_nonneg _))
        (norm_nonneg _)
    have htri : ‖abelIntegral r ϑ ((ε i : ℂ) + (τ i : ℂ) * I)‖ ≤ B + abelError r c (ε i) := by
      have := norm_add_le (c * ((1 / ((ε i : ℂ) + (τ i : ℂ) * I)) ^ abelExponent ϑ *
        Complex.Gamma (abelExponent ϑ))) (abelIntegral r ϑ ((ε i : ℂ) + (τ i : ℂ) * I) -
        c * ((1 / ((ε i : ℂ) + (τ i : ℂ) * I)) ^ abelExponent ϑ * Complex.Gamma (abelExponent ϑ)))
      rw [add_sub_cancel] at this
      linarith
    have := mul_le_mul_of_nonneg_left htri hi.le
    simp only [Function.comp_apply]
    linarith

end GaloisForLFunctions.SelbergClass.DegreeOne
