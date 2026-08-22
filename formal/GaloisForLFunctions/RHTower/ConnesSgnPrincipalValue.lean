import GaloisForLFunctions.RHTower.ConnesSgnPairingOsc

/-!
# Step 1b, completed: the sign pairing is the principal value

  `∫ sgn(x) g(x) dx = (i/π) · PV ∫ 𝓕g(u)/u du`.

Step 1b of the route to the last §V identification of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The truncated pairing of `ConnesSgnPairingOsc` is split into the principal-value integrand times
`1 − cos 2πXu` plus a constant term that vanishes by oddness
(`connes_oscQuotient_ball_vanishes`); the oscillating factor is then removed in the limit by the
**Riemann–Lebesgue lemma**, since `∫ H(u) cos(2πXu) du = (𝓕H(X) + 𝓕H(−X))/2`.
-/

open MeasureTheory Set Filter Topology Real
open scoped SchwartzMap FourierTransform Interval

namespace GaloisForLFunctions.RHTower

noncomputable section

theorem connes_unitBall_eq_Icc : {v : ℝ | |v| ≤ 1} = Set.Icc (-1 : ℝ) 1 := by
  ext u
  simp [abs_le]

/-- The pointwise split of the oscillating integrand. -/
theorem connes_osc_split_pointwise (G : ℝ → ℂ) (X : ℝ) {u : ℝ} (hu : u ≠ 0) :
    G u * (((1 - Real.cos (2 * Real.pi * X * u)) / u : ℝ) : ℂ)
      = connesPVintegrand G u * (((1 - Real.cos (2 * Real.pi * X * u)) : ℝ) : ℂ)
        + Set.indicator {v : ℝ | |v| ≤ 1} (fun _ => G 0) u
            * (((1 - Real.cos (2 * Real.pi * X * u)) / u : ℝ) : ℂ) := by
  have hu' : ((u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu
  rw [connesPVintegrand]
  push_cast
  field_simp
  ring

/-- The oscillating factor is bounded by `2`. -/
theorem connes_one_sub_cos_norm_le (t : ℝ) : ‖(((1 - Real.cos t) : ℝ) : ℂ)‖ ≤ 2 := by
  obtain ⟨hnn, _⟩ := connes_one_sub_cos_bounds t
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  have := Real.neg_one_le_cos t
  linarith

/-- The principal-value integrand against the oscillating factor is integrable. -/
theorem connes_pvOsc_integrable (g : 𝓢(ℝ, ℂ)) (X : ℝ) :
    Integrable (fun u : ℝ => connesPVintegrand (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) u
      * (((1 - Real.cos (2 * Real.pi * X * u)) : ℝ) : ℂ)) volume := by
  have hH := connes_pvIntegrand_integrable (SchwartzMap.fourierTransformCLM ℂ g)
  have hHcoe : ((SchwartzMap.fourierTransformCLM ℂ g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = 𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe]
  rw [hHcoe] at hH
  refine Integrable.mono' (hH.norm.const_mul 2) ?_ ?_
  · refine AEStronglyMeasurable.mul hH.aestronglyMeasurable ?_
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  · filter_upwards with u
    rw [norm_mul]
    calc ‖connesPVintegrand (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) u‖
          * ‖(((1 - Real.cos (2 * Real.pi * X * u)) : ℝ) : ℂ)‖
        ≤ ‖connesPVintegrand (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) u‖ * 2 :=
          mul_le_mul_of_nonneg_left (connes_one_sub_cos_norm_le _) (norm_nonneg _)
      _ = 2 * ‖connesPVintegrand (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) u‖ := by ring

/-- The constant piece is integrable. -/
theorem connes_constOsc_integrable (G : ℝ → ℂ) (X : ℝ) :
    Integrable (fun u : ℝ => Set.indicator {v : ℝ | |v| ≤ 1} (fun _ => G 0) u
      * (((1 - Real.cos (2 * Real.pi * X * u)) / u : ℝ) : ℂ)) volume := by
  have hfun : (fun u : ℝ => Set.indicator {v : ℝ | |v| ≤ 1} (fun _ => G 0) u
      * (((1 - Real.cos (2 * Real.pi * X * u)) / u : ℝ) : ℂ))
      = Set.indicator {v : ℝ | |v| ≤ 1}
        (fun u : ℝ => G 0 * (((1 - Real.cos (2 * Real.pi * X * u)) / u : ℝ) : ℂ)) := by
    funext u
    by_cases hu : u ∈ {v : ℝ | |v| ≤ 1}
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]
  rw [hfun, MeasureTheory.integrable_indicator_iff connes_unitBall_measurable]
  refine Measure.integrableOn_of_bounded (M := ‖G 0‖ * (2 * Real.pi ^ 2 * X ^ 2)) ?_ ?_ ?_
  · rw [connes_unitBall_eq_Icc]
    exact measure_Icc_lt_top.ne
  · refine Measurable.aestronglyMeasurable ?_
    refine measurable_const.mul ?_
    refine Complex.measurable_ofReal.comp ?_
    exact (measurable_const.sub
      (Real.measurable_cos.comp (measurable_const.mul measurable_id))).div measurable_id
  · filter_upwards [ae_restrict_mem connes_unitBall_measurable] with u hu
    have hu1 : |u| ≤ 1 := hu
    have hM0 : (0 : ℝ) ≤ 2 * Real.pi ^ 2 * X ^ 2 := by positivity
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖(((1 - Real.cos (2 * Real.pi * X * u)) / u : ℝ) : ℂ)‖
        ≤ 2 * Real.pi ^ 2 * X ^ 2 * |u| := connes_oscQuotient_bound X u
      _ ≤ 2 * Real.pi ^ 2 * X ^ 2 * 1 := mul_le_mul_of_nonneg_left hu1 hM0
      _ = 2 * Real.pi ^ 2 * X ^ 2 := mul_one _

/-- **The constant piece integrates to zero.** -/
theorem connes_constOsc_integral_zero (G : ℝ → ℂ) (X : ℝ) :
    (∫ u : ℝ, Set.indicator {v : ℝ | |v| ≤ 1} (fun _ => G 0) u
      * (((1 - Real.cos (2 * Real.pi * X * u)) / u : ℝ) : ℂ)) = 0 := by
  have hfun : (fun u : ℝ => Set.indicator {v : ℝ | |v| ≤ 1} (fun _ => G 0) u
      * (((1 - Real.cos (2 * Real.pi * X * u)) / u : ℝ) : ℂ))
      = Set.indicator {v : ℝ | |v| ≤ 1}
        (fun u : ℝ => G 0 * (((1 - Real.cos (2 * Real.pi * X * u)) / u : ℝ) : ℂ)) := by
    funext u
    by_cases hu : u ∈ {v : ℝ | |v| ≤ 1}
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]
  rw [hfun, MeasureTheory.integral_indicator connes_unitBall_measurable,
    MeasureTheory.integral_const_mul, connes_unitBall_eq_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    connes_oscQuotient_ball_vanishes X, mul_zero]

/-- **The truncated pairing against the principal-value integrand.** -/
theorem connes_sgn_pairing_H (g : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 ≤ X) :
    (∫ x in (-X : ℝ)..X, (Real.sign x : ℂ) * g x)
      = (Complex.I / (Real.pi : ℂ)) *
          ∫ u : ℝ, connesPVintegrand (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) u
            * (((1 - Real.cos (2 * Real.pi * X * u)) : ℝ) : ℂ) := by
  rw [connes_sgn_pairing_osc g hX]
  congr 1
  have hsplit : (∫ u : ℝ, (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) u
        * (((1 - Real.cos (2 * Real.pi * X * u)) / u : ℝ) : ℂ))
      = (∫ u : ℝ, connesPVintegrand (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) u
          * (((1 - Real.cos (2 * Real.pi * X * u)) : ℝ) : ℂ))
        + ∫ u : ℝ, Set.indicator {v : ℝ | |v| ≤ 1}
            (fun _ => (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) 0) u
            * (((1 - Real.cos (2 * Real.pi * X * u)) / u : ℝ) : ℂ) := by
    rw [← MeasureTheory.integral_add (connes_pvOsc_integrable g X)
      (connes_constOsc_integrable (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) X)]
    refine integral_congr_ae ?_
    filter_upwards [connes_ae_ne_zero] with u hu
    exact connes_osc_split_pointwise _ X hu
  rw [hsplit, connes_constOsc_integral_zero, add_zero]

/-- The exponential sum is twice the cosine. -/
theorem connes_exp_add_exp_neg (z : ℂ) :
    Complex.exp (z * Complex.I) + Complex.exp (-(z * Complex.I)) = 2 * Complex.cos z := by
  rw [show -(z * Complex.I) = (-z) * Complex.I by ring, Complex.exp_mul_I, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg]
  ring

/-- The oscillating integral is the average of two Fourier values. -/
theorem connes_H_cos_eq_fourier {H : ℝ → ℂ} (hH : Integrable H volume) (X : ℝ) :
    (∫ u : ℝ, H u * ((Real.cos (2 * Real.pi * X * u) : ℝ) : ℂ))
      = (𝓕 H X + 𝓕 H (-X)) / 2 := by
  have hint : ∀ w : ℝ, Integrable
      (fun v : ℝ => Complex.exp (((-2 * Real.pi * v * w : ℝ) : ℂ) * Complex.I) * H v) volume := by
    intro w
    refine Integrable.mono' hH.norm ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ hH.aestronglyMeasurable
      refine Continuous.aestronglyMeasurable ?_
      fun_prop
    · filter_upwards with v
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← MeasureTheory.integral_add (hint X) (hint (-X)), ← MeasureTheory.integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  set a : ℂ := ((-2 * Real.pi * v * X : ℝ) : ℂ) with ha
  have hz : ((-2 * Real.pi * v * -X : ℝ) : ℂ) = -a := by
    rw [ha]
    push_cast
    ring
  have hcos : Complex.cos a = ((Real.cos (2 * Real.pi * X * v) : ℝ) : ℂ) := by
    rw [ha, ← Complex.ofReal_cos]
    congr 1
    rw [show (-2 * Real.pi * v * X : ℝ) = -(2 * Real.pi * X * v) by ring, Real.cos_neg]
  have key : Complex.exp (a * Complex.I) * H v + Complex.exp (-a * Complex.I) * H v
      = 2 * Complex.cos a * H v := by
    rw [← add_mul, show (-a) * Complex.I = -(a * Complex.I) by ring,
      connes_exp_add_exp_neg a]
  show H v * ((Real.cos (2 * Real.pi * X * v) : ℝ) : ℂ)
    = (Complex.exp (a * Complex.I) * H v
        + Complex.exp (((-2 * Real.pi * v * -X : ℝ) : ℂ) * Complex.I) * H v) / 2
  rw [hz, key, hcos]
  ring

/-- The principal-value integrand against `cos` is integrable. -/
theorem connes_pvCos_integrable (g : 𝓢(ℝ, ℂ)) (X : ℝ) :
    Integrable (fun u : ℝ => connesPVintegrand (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) u
      * (((Real.cos (2 * Real.pi * X * u)) : ℝ) : ℂ)) volume := by
  have hH := connes_pvIntegrand_integrable (SchwartzMap.fourierTransformCLM ℂ g)
  have hHcoe : ((SchwartzMap.fourierTransformCLM ℂ g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = 𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe]
  rw [hHcoe] at hH
  refine Integrable.mono' hH.norm ?_ ?_
  · refine AEStronglyMeasurable.mul hH.aestronglyMeasurable ?_
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  · filter_upwards with u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)

/-- The principal-value integrand of a Schwartz transform is integrable. -/
theorem connes_pvIntegrand_fourier_integrable (g : 𝓢(ℝ, ℂ)) :
    Integrable (connesPVintegrand (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ))) volume := by
  have hH := connes_pvIntegrand_integrable (SchwartzMap.fourierTransformCLM ℂ g)
  have hHcoe : ((SchwartzMap.fourierTransformCLM ℂ g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = 𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe]
  rwa [hHcoe] at hH

/-- **Riemann–Lebesgue.**  The oscillating integral vanishes in the limit. -/
theorem connes_H_cos_tendsto {H : ℝ → ℂ} (hH : Integrable H volume) :
    Tendsto (fun X : ℝ => ∫ u : ℝ, H u * ((Real.cos (2 * Real.pi * X * u) : ℝ) : ℂ))
      atTop (𝓝 0) := by
  have hRL : Tendsto (𝓕 H) (cocompact ℝ) (𝓝 0) := Real.zero_at_infty_fourier H
  have hTop : Tendsto (fun X : ℝ => 𝓕 H X) atTop (𝓝 0) := by
    refine hRL.mono_left ?_
    rw [cocompact_eq_atBot_atTop]
    exact le_sup_right
  have hBot : Tendsto (fun X : ℝ => 𝓕 H (-X)) atTop (𝓝 0) := by
    have hle : (atBot : Filter ℝ) ≤ cocompact ℝ := by
      rw [cocompact_eq_atBot_atTop]
      exact le_sup_left
    exact (hRL.mono_left hle).comp tendsto_neg_atTop_atBot
  have hsum : Tendsto (fun X : ℝ => (𝓕 H X + 𝓕 H (-X)) / 2) atTop (𝓝 0) := by
    have h := (hTop.add hBot).div_const 2
    simpa using h
  exact hsum.congr fun X => (connes_H_cos_eq_fourier hH X).symm

/-- **Step 1b, the conclusion.**  `∫ sgn(x) g(x) dx = (i/π) · PV ∫ 𝓕g(u)/u du`. -/
theorem connes_sgn_pv_pairing (g : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, (Real.sign x : ℂ) * g x)
      = (Complex.I / (Real.pi : ℂ)) * connesPVinv (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) := by
  set G : ℝ → ℂ := 𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) with hG
  have hH : Integrable (connesPVintegrand G) volume := connes_pvIntegrand_fourier_integrable g
  have hgint : Integrable (fun x : ℝ => (Real.sign x : ℂ) * g x) volume := by
    refine Integrable.mono' (g.integrable (μ := volume)).norm ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ g.continuous.aestronglyMeasurable
      exact (Complex.measurable_ofReal.comp connes_measurable_sign).aestronglyMeasurable
    · filter_upwards with x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (connes_abs_sign_le_one x)
  have hA : Tendsto (fun X : ℝ => ∫ x in (-X : ℝ)..X, (Real.sign x : ℂ) * g x) atTop
      (𝓝 (∫ x : ℝ, (Real.sign x : ℂ) * g x)) :=
    MeasureTheory.intervalIntegral_tendsto_integral hgint tendsto_neg_atTop_atBot tendsto_id
  have hsplit : ∀ X : ℝ,
      (∫ u : ℝ, connesPVintegrand G u * (((1 - Real.cos (2 * Real.pi * X * u)) : ℝ) : ℂ))
        = (∫ u : ℝ, connesPVintegrand G u)
          - ∫ u : ℝ, connesPVintegrand G u
              * (((Real.cos (2 * Real.pi * X * u)) : ℝ) : ℂ) := by
    intro X
    rw [← MeasureTheory.integral_sub hH (connes_pvCos_integrable g X)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    push_cast
    ring
  have hB : Tendsto (fun X : ℝ =>
      ∫ u : ℝ, connesPVintegrand G u * (((1 - Real.cos (2 * Real.pi * X * u)) : ℝ) : ℂ))
      atTop (𝓝 (connesPVinv G)) := by
    have hlim := (tendsto_const_nhds (x := ∫ u : ℝ, connesPVintegrand G u) (f := atTop)
      (α := ℝ)).sub (connes_H_cos_tendsto hH)
    rw [sub_zero] at hlim
    have hval : (∫ u : ℝ, connesPVintegrand G u) = connesPVinv G := by
      rw [hG]
      have := connes_integral_pvIntegrand (SchwartzMap.fourierTransformCLM ℂ g)
      have hHcoe : ((SchwartzMap.fourierTransformCLM ℂ g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
          = 𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
        rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe]
      rwa [hHcoe] at this
    rw [hval] at hlim
    have hsplit' : ∀ X : ℝ,
        (∫ u : ℝ, connesPVintegrand G u * (((1 - Real.cos (2 * Real.pi * X * u)) : ℝ) : ℂ))
          = connesPVinv G - ∫ u : ℝ, connesPVintegrand G u
              * (((Real.cos (2 * Real.pi * X * u)) : ℝ) : ℂ) := by
      intro X
      rw [hsplit X, hval]
    exact hlim.congr fun X => (hsplit' X).symm
  have hC : Tendsto (fun X : ℝ => (Complex.I / (Real.pi : ℂ)) *
      ∫ u : ℝ, connesPVintegrand G u * (((1 - Real.cos (2 * Real.pi * X * u)) : ℝ) : ℂ))
      atTop (𝓝 ((Complex.I / (Real.pi : ℂ)) * connesPVinv G)) := hB.const_mul _
  have hEq : (fun X : ℝ => ∫ x in (-X : ℝ)..X, (Real.sign x : ℂ) * g x)
      =ᶠ[atTop] fun X : ℝ => (Complex.I / (Real.pi : ℂ)) *
        ∫ u : ℝ, connesPVintegrand G u
          * (((1 - Real.cos (2 * Real.pi * X * u)) : ℝ) : ℂ) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
    exact connes_sgn_pairing_H g hX
  exact tendsto_nhds_unique (hA.congr' hEq) hC

end

end GaloisForLFunctions.RHTower
