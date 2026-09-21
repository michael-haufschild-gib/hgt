import GaloisForLFunctions.RHTower.ChronologicalTailL1StabilityNoGo

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

namespace RHTower

/-- A finite tail `L¹` norm controls every nonnegative Mellin weight. -/
theorem integrableOn_tailProfile_weight_of_integrable
    {θ : ℝ} (hθ0 : 0 < θ) {f : ℝ → ℂ} (hfm : Measurable f)
    (htail : IntegrableOn (tailProfile θ f) (Ioo (0 : ℝ) 1)) {s : ℝ} (hs : 0 ≤ s) :
    IntegrableOn (fun x : ℝ => ‖tailProfile θ f x‖ * x ^ (-s)) (Ioo (0 : ℝ) 1) := by
  refine Integrable.mono' (g := fun x : ℝ => ‖tailProfile θ f x‖ * θ ^ (-s)) ?_ (((measurable_tailProfile θ hfm).norm).mul
    (measurable_id.pow_const _)).aestronglyMeasurable ?_
  · simpa only [mul_comm] using htail.norm.const_mul (θ ^ (-s))
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hθpow : 0 ≤ θ ^ (-s) := Real.rpow_nonneg hθ0.le _
    by_cases hxθ : θ ≤ x
    · have hw : x ^ (-s) ≤ θ ^ (-s) := by
        rw [Real.rpow_neg hθ0.le, Real.rpow_neg hx0.le, ← one_div, ← one_div]
        exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hθ0 _)
          (Real.rpow_le_rpow hθ0.le hxθ hs)
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (norm_nonneg (tailProfile θ f x)) (Real.rpow_nonneg hx0.le _))]
      exact mul_le_mul_of_nonneg_left hw (norm_nonneg (tailProfile θ f x))
    · rw [tailProfile_of_lt (by linarith), norm_zero, zero_mul]
      simp

/-- Tail `L¹` alone supplies a locally uniform derivative dominator. -/
theorem hasDerivAt_tailMomentE_of_integrable
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {f : ℝ → ℂ}
    (hfm : Measurable f) (htail : IntegrableOn (tailProfile θ f) (Ioo (0 : ℝ) 1))
    (w₀ : ℂ) :
    HasDerivAt (tailMomentE θ f) (tailMomentEDeriv θ f w₀) w₀ := by
  set R : ℝ := |w₀.re| + 1 with hRdef
  have hR0 : 0 ≤ R := by positivity
  set B : ℝ := θ ^ (-R) * (-Real.log θ) with hBdef
  have hlogθ : 0 ≤ -Real.log θ := by
    have := Real.log_nonpos hθ0.le hθ1
    linarith
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (Real.rpow_nonneg hθ0.le _) hlogθ
  have hreball : ∀ w ∈ Metric.ball w₀ 1, |w.re| ≤ R := by
    intro w hw
    have h1 : |w.re - w₀.re| ≤ ‖w - w₀‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - w₀)
    have h2 : ‖w - w₀‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have h3 := abs_le.mp h1
    have h4 := abs_le.mp (le_refl |w₀.re|)
    rw [hRdef]
    rcases abs_cases w.re with ⟨he, -⟩ | ⟨he, -⟩ <;>
      rcases abs_cases w₀.re with ⟨he0, -⟩ | ⟨he0, -⟩ <;> · rw [he]; linarith [h3.1, h3.2]
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), ∀ w ∈ Metric.ball w₀ 1,
      ‖tailProfile θ f x *
        (Complex.exp (((Real.log x : ℝ) : ℂ) * (-w)) * (-((Real.log x : ℝ) : ℂ)))‖ ≤
        B * ‖tailProfile θ f x‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx w hw
    have hx0 : (0 : ℝ) < x := hx.1
    by_cases hxθ : θ ≤ x
    · rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        norm_exp_log_mul hx0]
      have hw1 : x ^ (-w.re) ≤ θ ^ (-R) := by
        refine rpow_le_rpow_neg_bound hθ0 hθ1 hxθ hx.2.le ?_
        rw [abs_neg]
        exact hreball w hw
      have hw2 : |Real.log x| ≤ -Real.log θ := abs_log_le hθ0 hxθ hx.2.le
      have hfac : x ^ (-w.re) * |Real.log x| ≤ θ ^ (-R) * (-Real.log θ) :=
        mul_le_mul hw1 hw2 (abs_nonneg _) (Real.rpow_nonneg hθ0.le _)
      calc
        ‖tailProfile θ f x‖ * (x ^ (-w.re) * |Real.log x|) ≤
            ‖tailProfile θ f x‖ * (θ ^ (-R) * (-Real.log θ)) :=
          mul_le_mul_of_nonneg_left hfac (norm_nonneg _)
        _ = B * ‖tailProfile θ f x‖ := by rw [hBdef]; ring
    · rw [tailProfile_of_lt (by linarith), zero_mul, norm_zero]
      simp
  have hdiff : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), ∀ w ∈ Metric.ball w₀ 1,
      HasDerivAt (fun w : ℂ => tailProfile θ f x * Complex.exp (((Real.log x : ℝ) : ℂ) * (-w)))
        (tailProfile θ f x *
          (Complex.exp (((Real.log x : ℝ) : ℂ) * (-w)) * (-((Real.log x : ℝ) : ℂ)))) w := by
    filter_upwards with x w _
    have hin : HasDerivAt (fun w : ℂ => ((Real.log x : ℝ) : ℂ) * (-w))
        (-((Real.log x : ℝ) : ℂ)) w := by
      simpa using ((hasDerivAt_id w).neg).const_mul ((Real.log x : ℝ) : ℂ)
    exact (hin.cexp).const_mul (tailProfile θ f x)
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun x : ℝ => B * ‖tailProfile θ f x‖) (Metric.ball_mem_nhds w₀ one_pos)
    (Filter.Eventually.of_forall fun w =>
      (measurable_tailMomentE_integrand θ hfm w).aestronglyMeasurable)
    (by
      refine Integrable.mono' (g := fun x : ℝ => ‖tailProfile θ f x‖ * θ ^ (-R)) ?_
        (measurable_tailMomentE_integrand θ hfm w₀).aestronglyMeasurable ?_
      · simpa only [mul_comm] using htail.norm.const_mul (θ ^ (-R))
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        have hx0 : (0 : ℝ) < x := hx.1
        by_cases hxθ : θ ≤ x
        · rw [norm_mul, norm_exp_log_mul hx0]
          have hw1 : x ^ (-w₀.re) ≤ θ ^ (-R) := by
            refine rpow_le_rpow_neg_bound hθ0 hθ1 hxθ hx.2.le ?_
            rw [abs_neg]
            exact hreball w₀ (Metric.mem_ball_self one_pos)
          exact mul_le_mul_of_nonneg_left hw1 (norm_nonneg _)
        · rw [tailProfile_of_lt (by linarith), zero_mul, norm_zero]
          simp)
    (measurable_tailMomentEDeriv_integrand θ hfm w₀).aestronglyMeasurable
    hbound (by simpa only [mul_comm] using htail.norm.const_mul B) hdiff
  exact hres.2

theorem differentiable_tailMomentE_of_integrable
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {f : ℝ → ℂ}
    (hfm : Measurable f) (htail : IntegrableOn (tailProfile θ f) (Ioo (0 : ℝ) 1)) :
    Differentiable ℂ (tailMomentE θ f) := fun w =>
  (hasDerivAt_tailMomentE_of_integrable hθ0 hθ1 hfm htail w).differentiableAt

theorem moment_identity_real_of_integrable
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    {f : ℝ → ℂ} (hfm : Measurable f)
    (htail : IntegrableOn (tailProfile θ f) (Ioo (0 : ℝ) 1))
    (h : ∀ t : ℝ, t ∈ Icc (1 : ℝ) 2 →
      boseTransform (criticalProfile θ ρ) (t : ℂ) = boseTransform (tailProfile θ f) (t : ℂ))
    {s : ℝ} (hs0 : 0 < s) (hs : s < 1 / 2) :
    criticalMomentE θ ρ (s : ℂ) = tailMomentE θ f (s : ℂ) := by
  have hcm : Measurable (criticalProfile θ ρ) := measurable_criticalProfile θ ρ
  have htm : Measurable (tailProfile θ f) := measurable_tailProfile θ hfm
  have hcw : IntegrableOn (fun x : ℝ => ‖criticalProfile θ ρ x‖ * x ^ (-s)) (Ioo (0 : ℝ) 1) := by
    refine integrableOn_criticalProfile_weight ?_
    rw [hρ]
    linarith
  have htw : IntegrableOn (fun x : ℝ => ‖tailProfile θ f x‖ * x ^ (-s)) (Ioo (0 : ℝ) 1) :=
    integrableOn_tailProfile_weight_of_integrable hθ0 hfm htail hs0.le
  have hci : IntegrableOn (criticalProfile θ ρ) (Ioo (0 : ℝ) 1) :=
    integrableOn_of_weight hcm hs0.le hcw
  have hti : IntegrableOn (tailProfile θ f) (Ioo (0 : ℝ) 1) :=
    integrableOn_of_weight htm hs0.le htw
  set g : ℝ → ℂ := fun x => criticalProfile θ ρ x - tailProfile θ f x with hgdef
  have hgm : Measurable g := hcm.sub htm
  have hgw : IntegrableOn (fun x : ℝ => ‖g x‖ * x ^ (-s)) (Ioo (0 : ℝ) 1) := by
    refine Integrable.mono' (hcw.add htw)
      ((hgm.norm).mul (measurable_id.pow_const _)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hw : (0 : ℝ) ≤ x ^ (-s) := Real.rpow_nonneg hx0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hw)]
    have hnorm : ‖g x‖ ≤ ‖criticalProfile θ ρ x‖ + ‖tailProfile θ f x‖ := norm_sub_le _ _
    calc
      ‖g x‖ * x ^ (-s) ≤
          (‖criticalProfile θ ρ x‖ + ‖tailProfile θ f x‖) * x ^ (-s) :=
        mul_le_mul_of_nonneg_right hnorm hw
      _ = ‖criticalProfile θ ρ x‖ * x ^ (-s) + ‖tailProfile θ f x‖ * x ^ (-s) := by ring
  have hzero : ∀ t : ℝ, t ∈ Icc (1 : ℝ) 2 → boseTransform g (t : ℂ) = 0 := by
    intro t ht
    have hmemD : ((t : ℝ) : ℂ) ∈ boseDomain :=
      ofReal_mem_boseDomain (by linarith [ht.1])
    rw [hgdef, boseTransform_sub hcm htm hci hti hmemD, h t ht, sub_self]
  have hmom := moment_eq_zero_of_transform_eqOn hgm hs0 (by linarith) hgw hzero
  have hsplit : ∫ x in Ioo (0 : ℝ) 1, g x * ((x ^ (-s) : ℝ) : ℂ)
      = (∫ x in Ioo (0 : ℝ) 1, criticalProfile θ ρ x * ((x ^ (-s) : ℝ) : ℂ))
        - ∫ x in Ioo (0 : ℝ) 1, tailProfile θ f x * ((x ^ (-s) : ℝ) : ℂ) := by
    rw [← integral_sub (integrableOn_profile_weight_mul hcm hcw)
      (integrableOn_profile_weight_mul htm htw)]
    refine setIntegral_congr_fun measurableSet_Ioo (fun x _ => ?_)
    rw [hgdef]
    ring
  rw [hsplit, sub_eq_zero] at hmom
  have hcrit : ∫ x in Ioo (0 : ℝ) 1, criticalProfile θ ρ x * ((x ^ (-s) : ℝ) : ℂ)
      = criticalMomentE θ ρ (s : ℂ) := by
    rw [criticalMomentE_eq_div hθ0]
    refine integral_criticalProfile_weight hθ0 hθ1.le ?_ ?_
    · rw [hρ]
      linarith
    · intro hz
      have hre : (ρ - (s : ℂ)).re = 1 / 2 - s := by
        rw [Complex.sub_re, Complex.ofReal_re, hρ]
      rw [hz] at hre
      simp only [Complex.zero_re] at hre
      linarith
  rw [hcrit] at hmom
  rw [tailMomentE_eq, tailMoment_ofReal θ s]
  exact hmom

theorem criticalMomentE_eq_tailMomentE_of_integrable
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) {f : ℝ → ℂ} (hfm : Measurable f)
    (htail : IntegrableOn (tailProfile θ f) (Ioo (0 : ℝ) 1))
    (h : ∀ t : ℝ, t ∈ Icc (1 : ℝ) 2 →
      boseTransform (criticalProfile θ ρ) (t : ℂ) = boseTransform (tailProfile θ f) (t : ℂ)) :
    ∀ w ∈ leftHalfPlane, criticalMomentE θ ρ w = tailMomentE θ f w := by
  have hanalytic : AnalyticOnNhd ℂ
      (fun w => criticalMomentE θ ρ w - tailMomentE θ f w) leftHalfPlane :=
    DifferentiableOn.analyticOnNhd
      ((differentiableOn_criticalMomentE hρ).sub
        ((differentiable_tailMomentE_of_integrable hθ0 hθ1.le hfm htail).differentiableOn))
      isOpen_leftHalfPlane
  have hz₀ : (((1 : ℝ) / 4 : ℝ) : ℂ) ∈ leftHalfPlane := by
    rw [mem_leftHalfPlane, Complex.ofReal_re]
    norm_num
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 5)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 5)) atTop atTop :=
      tendsto_atTop_add_const_right _ 5 tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 5)⁻¹) atTop (𝓝 0) := h1.inv_tendsto_atTop
    simpa [one_div] using h2
  have hfreq : ∃ᶠ w in 𝓝[≠] (((1 : ℝ) / 4 : ℝ) : ℂ),
      (fun w => criticalMomentE θ ρ w - tailMomentE θ f w) w = 0 := by
    have htend : Tendsto (fun n : ℕ => ((1 / 4 + 1 / (n + 5 : ℝ) : ℝ) : ℂ)) atTop
        (𝓝[≠] (((1 : ℝ) / 4 : ℝ) : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · refine (Complex.continuous_ofReal.tendsto _).comp ?_
        simpa using tendsto_const_nhds.add hinv
      · filter_upwards with n
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hcontra
        have hreal := Complex.ofReal_injective hcontra
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 5) := by positivity
        norm_num at hreal
        linarith
    refine htend.frequently (Frequently.of_forall fun n => ?_)
    have hs0 : (0 : ℝ) < 1 / 4 + 1 / ((n : ℝ) + 5) := by positivity
    have hn5 : (5 : ℝ) ≤ (n : ℝ) + 5 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hs : 1 / 4 + 1 / ((n : ℝ) + 5) < 1 / 2 := by
      have : 1 / ((n : ℝ) + 5) ≤ 1 / 5 :=
        one_div_le_one_div_of_le (by norm_num) hn5
      linarith
    simp only [sub_eq_zero]
    exact moment_identity_real_of_integrable hθ0 hθ1 hρ hfm htail h hs0 hs
  have heq := hanalytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_leftHalfPlane hz₀ hfreq
  intro w hw
  have hval := heq hw
  simp only [Pi.zero_apply, sub_eq_zero] at hval
  exact hval

/-- The Mellin tail moment has a bound depending only on tail `L¹` mass. -/
theorem norm_tailMomentE_le_tailL1
    {θ : ℝ} (hθ0 : 0 < θ) {f : ℝ → ℂ}
    (hfm : Measurable f) (htail : IntegrableOn (tailProfile θ f) (Ioo (0 : ℝ) 1))
    {w : ℂ} {s : ℝ} (hs0 : 0 ≤ s) (hws : w.re ≤ s) :
    ‖tailMomentE θ f w‖ ≤ θ ^ (-s) * ∫ x in Ioo (0 : ℝ) 1, ‖tailProfile θ f x‖ := by
  have htm : Measurable (tailProfile θ f) := measurable_tailProfile θ hfm
  have hweight : IntegrableOn (fun x : ℝ => ‖tailProfile θ f x‖ * x ^ (-s)) (Ioo (0 : ℝ) 1) :=
    integrableOn_tailProfile_weight_of_integrable hθ0 hfm htail hs0
  have hintegrand : IntegrableOn
      (fun x : ℝ => tailProfile θ f x * Complex.exp (((Real.log x : ℝ) : ℂ) * (-w)))
      (Ioo (0 : ℝ) 1) := by
    refine Integrable.mono' hweight
      (measurable_tailMomentE_integrand θ hfm w).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hx1 : x ≤ 1 := hx.2.le
    by_cases hxθ : θ ≤ x
    · rw [norm_mul, norm_exp_log_mul hx0]
      have hpow : x ^ (-w.re) ≤ x ^ (-s) := by
        exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
      exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    · rw [tailProfile_of_lt (by linarith), zero_mul, norm_zero]
      simp
  have hright : IntegrableOn (fun x : ℝ => θ ^ (-s) * ‖tailProfile θ f x‖)
      (Ioo (0 : ℝ) 1) := by
    exact htail.norm.const_mul (θ ^ (-s))
  unfold tailMomentE
  calc
    ‖∫ x in Ioo (0 : ℝ) 1,
        tailProfile θ f x * Complex.exp (((Real.log x : ℝ) : ℂ) * (-w))‖ ≤
        ∫ x in Ioo (0 : ℝ) 1,
          ‖tailProfile θ f x * Complex.exp (((Real.log x : ℝ) : ℂ) * (-w))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioo (0 : ℝ) 1, θ ^ (-s) * ‖tailProfile θ f x‖ := by
      apply integral_mono_ae hintegrand.norm hright
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hx0 : (0 : ℝ) < x := hx.1
      have hx1 : x ≤ 1 := hx.2.le
      by_cases hxθ : θ ≤ x
      · rw [norm_mul, norm_exp_log_mul hx0]
        have hpow : x ^ (-w.re) ≤ x ^ (-s) := by
          exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
        have htailpow : x ^ (-s) ≤ θ ^ (-s) := by
          rw [Real.rpow_neg hθ0.le, Real.rpow_neg hx0.le, ← one_div, ← one_div]
          exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hθ0 _)
            (Real.rpow_le_rpow hθ0.le hxθ hs0)
        calc
          ‖tailProfile θ f x‖ * x ^ (-w.re) ≤
              ‖tailProfile θ f x‖ * x ^ (-s) :=
            mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
          _ ≤ ‖tailProfile θ f x‖ * θ ^ (-s) :=
            mul_le_mul_of_nonneg_left htailpow (norm_nonneg _)
          _ = θ ^ (-s) * ‖tailProfile θ f x‖ := by ring
      · rw [tailProfile_of_lt (by linarith), zero_mul, norm_zero]
        simp
    _ = θ ^ (-s) * ∫ x in Ioo (0 : ℝ) 1, ‖tailProfile θ f x‖ := by
      rw [integral_const_mul]

/-- No finite-tail-`L¹` profile can have critical Bose response on a real interval. -/
theorem heatTransform_separation_of_integrable
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) {f : ℝ → ℂ} (hfm : Measurable f)
    (htail : IntegrableOn (tailProfile θ f) (Ioo (0 : ℝ) 1))
    (h : ∀ t : ℝ, t ∈ Icc (1 : ℝ) 2 →
      boseTransform (criticalProfile θ ρ) (t : ℂ) = boseTransform (tailProfile θ f) (t : ℂ)) :
    False := by
  set A : ℝ := ∫ x in Ioo (0 : ℝ) 1, ‖tailProfile θ f x‖ with hAdef
  have hA : 0 ≤ A := by
    rw [hAdef]
    exact integral_nonneg fun _ => norm_nonneg _
  have hAone : 0 < A + 1 := by linarith
  set δ : ℝ := min (1 / 2) (θ / (2 * (A + 1))) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]
    refine lt_min (by norm_num) ?_
    exact div_pos hθ0 (mul_pos (by norm_num) hAone)
  have hδ2 : δ ≤ 1 / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδA : δ ≤ θ / (2 * (A + 1)) := by rw [hδdef]; exact min_le_right _ _
  have hre : (ρ - (δ : ℂ)).re = 1 / 2 - δ := by
    rw [Complex.sub_re, Complex.ofReal_re, hρ]
  have hmem : ρ - (δ : ℂ) ∈ leftHalfPlane := by
    rw [mem_leftHalfPlane, hre]
    linarith
  have hid := criticalMomentE_eq_tailMomentE_of_integrable hθ0 hθ1 hρ hfm htail h _ hmem
  have hsub : ρ - (ρ - (δ : ℂ)) = (δ : ℂ) := by ring
  have hlhs : ‖criticalMomentE θ ρ (ρ - (δ : ℂ))‖ = θ ^ δ / δ := by
    rw [norm_criticalMomentE hθ0, hsub, Complex.ofReal_re, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hδ0]
  have hwre : (ρ - (δ : ℂ)).re ≤ 1 / 2 := by
    rw [hre]
    linarith
  have hrhs : ‖tailMomentE θ f (ρ - (δ : ℂ))‖ ≤ A * θ ^ (-(1 / 2) : ℝ) := by
    simpa only [hAdef, mul_comm] using
      (norm_tailMomentE_le_tailL1 hθ0 hfm htail (s := (1 / 2 : ℝ))
        (by norm_num) hwre)
  have hbound : θ ^ δ / δ ≤ A * θ ^ (-(1 / 2) : ℝ) := by
    rw [← hlhs, hid]
    exact hrhs
  have hθδ : θ ^ ((1 : ℝ) / 2) ≤ θ ^ δ :=
    Real.rpow_le_rpow_of_exponent_ge hθ0 hθ1.le hδ2
  have hhalf : θ ^ ((1 : ℝ) / 2) * θ ^ ((1 : ℝ) / 2) = θ := by
    rw [← Real.rpow_add hθ0]
    norm_num
  have hneg : θ ^ (-(1 / 2) : ℝ) * θ ^ ((1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hθ0]
    norm_num
  have hp1 : 0 < θ ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hθ0 _
  have h1 : θ ^ δ ≤ δ * (A * θ ^ (-(1 / 2) : ℝ)) := by
    rw [div_le_iff₀ hδ0] at hbound
    linarith
  have h2 : θ ≤ δ * A := by
    have hstep := mul_le_mul_of_nonneg_right (le_trans hθδ h1) hp1.le
    rw [hhalf] at hstep
    have hre2 : δ * (A * θ ^ (-(1 / 2) : ℝ)) * θ ^ ((1 : ℝ) / 2) =
        δ * A * (θ ^ (-(1 / 2) : ℝ) * θ ^ ((1 : ℝ) / 2)) := by ring
    rw [hre2, hneg, mul_one] at hstep
    exact hstep
  have h3 : δ * A < θ := by
    calc
      δ * A ≤ (θ / (2 * (A + 1))) * A := mul_le_mul_of_nonneg_right hδA hA
      _ = θ * (A / (2 * (A + 1))) := by ring
      _ < θ * 1 := by
        refine mul_lt_mul_of_pos_left ?_ hθ0
        rw [div_lt_one (by positivity)]
        linarith
      _ = θ := mul_one θ
  linarith

theorem tendsto_boseTransform_of_tailL1_of_integrable
    {θ : ℝ} {f : ℕ → ℝ → ℂ} {g : ℝ → ℂ}
    (hfm : ∀ n, Measurable (f n))
    (hfi : ∀ n, IntegrableOn (tailProfile θ (f n)) (Ioo (0 : ℝ) 1))
    (hgm : Measurable g) (hgi : IntegrableOn (tailProfile θ g) (Ioo (0 : ℝ) 1))
    (hL1 : Tendsto (fun n => ∫ x in Ioo (0 : ℝ) 1,
      ‖tailProfile θ (f n) x - tailProfile θ g x‖) atTop (𝓝 0))
    {u : ℂ} (hu : u ∈ boseDomain) :
    Tendsto (fun n => boseTransform (tailProfile θ (f n)) u) atTop
      (𝓝 (boseTransform (tailProfile θ g) u)) := by
  obtain ⟨M, hM0, hM⟩ := exists_kernel_bound_at hu
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hscaled : Tendsto (fun n => M * ∫ x in Ioo (0 : ℝ) 1,
      ‖tailProfile θ (f n) x - tailProfile θ g x‖) atTop (𝓝 0) :=
    by simpa using hL1.const_mul M
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hscaled ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hbound := boseTransform_le_kernelBound_mul_tailL1
    (measurable_tailProfile θ (hfm n)) (measurable_tailProfile θ hgm) (hfi n) hgi hu hM
  have hnear := hN n hn
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (mul_nonneg hM0 (integral_nonneg fun _ => norm_nonneg _))] at hnear
  rw [Complex.dist_eq]
  exact lt_of_le_of_lt hbound hnear

/-- Critical Bose response cannot be reached by a tail-`L¹`-convergent, finite-tail-`L¹` array. -/
theorem no_l1_stable_integrable_tail_repair :
    ¬ ∃ (θ : ℝ) (ρ : ℂ) (f : ℕ → ℝ → ℂ) (g : ℝ → ℂ),
      0 < θ ∧ θ < 1 ∧ ρ.re = 1 / 2 ∧
      (∀ n, Measurable (f n)) ∧
      (∀ n, IntegrableOn (tailProfile θ (f n)) (Ioo (0 : ℝ) 1)) ∧
      Measurable g ∧ IntegrableOn (tailProfile θ g) (Ioo (0 : ℝ) 1) ∧
      Tendsto (fun n => ∫ x in Ioo (0 : ℝ) 1,
        ‖tailProfile θ (f n) x - tailProfile θ g x‖) atTop (𝓝 0) ∧
      (∀ t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        Tendsto (fun n => boseTransform (tailProfile θ (f n)) (t : ℂ)) atTop
          (𝓝 (boseTransform (criticalProfile θ ρ) (t : ℂ)))) := by
  rintro ⟨θ, ρ, f, g, hθ0, hθ1, hρ, hfm, hfi, hgm, hgi, hL1, htarget⟩
  apply heatTransform_separation_of_integrable hθ0 hθ1 hρ hgm hgi
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  have htail := tendsto_boseTransform_of_tailL1_of_integrable hfm hfi hgm hgi hL1
    (ofReal_mem_boseDomain ht0)
  exact tendsto_nhds_unique (htarget t ht) htail

end RHTower
