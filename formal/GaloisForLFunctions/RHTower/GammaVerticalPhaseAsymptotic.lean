import GaloisForLFunctions.RHTower.DigammaImaginaryVerticalAsymptotic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The vertical Gamma phase grows like `T log T`

Along a vertical line the logarithmic derivative of `Γ` has real part `log t + o(1)`, so the
continuous phase of `Γ` — the integral of that real part — is

`∫₀^T Re ψ(σ + it) dt = T log T − T + O(1) + o(T)`.

The two ingredients are the corpus's vertical digamma asymptotic and the elementary Cesàro fact
that a vanishing continuous function has sublinear primitive.  No Stirling expansion is used.
-/

open Complex Filter Topology intervalIntegral MeasureTheory

noncomputable section

namespace RHTower

/-! ## Continuity of the vertical digamma -/

theorem analyticOnNhd_Gamma_rightHalf :
    AnalyticOnNhd ℂ Complex.Gamma {s : ℂ | 0 < s.re} := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  refine (Complex.differentiableAt_Gamma s fun m => ?_).differentiableWithinAt
  intro h
  have hre : s.re = -(m : ℝ) := by rw [h]; simp
  have : (0 : ℝ) < -(m : ℝ) := hre ▸ hs
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem continuousAt_digamma {s : ℂ} (hs : 0 < s.re) : ContinuousAt Complex.digamma s := by
  have hG : AnalyticAt ℂ Complex.Gamma s := analyticOnNhd_Gamma_rightHalf s hs
  have hd : AnalyticAt ℂ (deriv Complex.Gamma) s :=
    analyticOnNhd_Gamma_rightHalf.deriv s hs
  have hne : Complex.Gamma s ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m => ?_
    intro h
    have hre : s.re = -(m : ℝ) := by rw [h]; simp
    have : (0 : ℝ) < -(m : ℝ) := hre ▸ hs
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have : AnalyticAt ℂ (fun z => deriv Complex.Gamma z / Complex.Gamma z) s := hd.div hG hne
  exact this.continuousAt

theorem continuous_digammaVerticalRe {σ : ℝ} (hσ : 0 < σ) :
    Continuous fun t : ℝ => (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re := by
  refine Complex.continuous_re.comp ?_
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hpath : ContinuousAt (fun u : ℝ => (σ : ℂ) + (u : ℂ) * Complex.I) t := by fun_prop
  refine ContinuousAt.comp ?_ hpath
  refine continuousAt_digamma ?_
  simpa using hσ

/-! ## The vertical phase -/

/-- The continuous phase of `Γ` along the vertical line through `σ`. -/
def gammaVerticalPhase (σ T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re

/-! ## A vanishing function has sublinear primitive -/

theorem tendsto_integral_div_atTop {ε : ℝ → ℝ} (hcont : ContinuousOn ε (Set.Ici 1))
    (h : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun T => (∫ t in (1 : ℝ)..T, ε t) / T) atTop (𝓝 0) := by
  have hint : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → IntervalIntegrable ε MeasureTheory.volume a b := by
    intro a b ha hb
    refine (hcont.mono ?_).intervalIntegrable
    intro x hx
    rw [Set.uIcc, Set.mem_Icc] at hx
    exact le_trans (le_min ha hb) hx.1
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hhalf : 0 < δ / 2 := by linarith
  obtain ⟨T₀, hT₀⟩ := (Metric.tendsto_atTop.mp h) (δ / 2) hhalf
  set T₁ : ℝ := max T₀ 1 with hT₁
  have hT₁1 : (1 : ℝ) ≤ T₁ := le_max_right _ _
  set A : ℝ := |∫ t in (1 : ℝ)..T₁, ε t| with hA
  have hA0 : 0 ≤ A := abs_nonneg _
  refine ⟨max T₁ (2 * A / δ + 1), fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT
  have hTA : 2 * A / δ + 1 ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by
    have : (1 : ℝ) ≤ T := le_trans hT₁1 hTT₁
    linarith
  have hsplit : (∫ t in (1 : ℝ)..T, ε t)
      = (∫ t in (1 : ℝ)..T₁, ε t) + ∫ t in T₁..T, ε t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint 1 T₁ (le_refl _) hT₁1)
      (hint T₁ T hT₁1 (le_trans hT₁1 hTT₁))]
  have htail : |∫ t in T₁..T, ε t| ≤ δ / 2 * (T - T₁) := by
    have hbound : ∀ t ∈ Set.uIoc T₁ T, ‖ε t‖ ≤ δ / 2 := by
      intro t ht
      rw [Set.uIoc_of_le hTT₁] at ht
      have hge : T₀ ≤ t := le_trans (le_max_left _ _) (le_of_lt ht.1)
      have := hT₀ t hge
      rw [Real.dist_eq, sub_zero] at this
      exact this.le
    have := intervalIntegral.norm_integral_le_of_norm_le_const (C := δ / 2) hbound
    rw [Real.norm_eq_abs] at this
    calc |∫ t in T₁..T, ε t| ≤ δ / 2 * |T - T₁| := this
      _ = δ / 2 * (T - T₁) := by rw [abs_of_nonneg (by linarith)]
  have hnum : |∫ t in (1 : ℝ)..T, ε t| ≤ A + δ / 2 * T := by
    rw [hsplit]
    calc |(∫ t in (1 : ℝ)..T₁, ε t) + ∫ t in T₁..T, ε t|
        ≤ A + |∫ t in T₁..T, ε t| := abs_add_le _ _
      _ ≤ A + δ / 2 * (T - T₁) := by linarith [htail]
      _ ≤ A + δ / 2 * T := by nlinarith [hT₁1, hδ]
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hT0, div_lt_iff₀ hT0]
  have hAT : A < δ / 2 * T := by
    have h1 : 2 * A / δ < T := by linarith
    rw [div_lt_iff₀ hδ] at h1
    linarith
  linarith [hnum]

/-! ## The asymptotic -/

/-- **The vertical Gamma phase is asymptotically `T log T`.** -/
theorem tendsto_gammaVerticalPhase_ratio {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun T => gammaVerticalPhase σ T / (T * Real.log T)) atTop (𝓝 1) := by
  set f : ℝ → ℝ := fun t => (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re with hf
  have hcf : Continuous f := continuous_digammaVerticalRe hσ
  set ε : ℝ → ℝ := fun t => f t - Real.log t with hε
  have hεlim : Tendsto ε atTop (𝓝 0) := re_digamma_vertical_sub_log_tendsto_zero σ hσ.le
  have hcε : ContinuousOn ε (Set.Ici (1 : ℝ)) := by
    refine hcf.continuousOn.sub ?_
    exact Real.continuousOn_log.mono fun t ht => by
      simp only [Set.mem_Ici] at ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
  have hA : ∀ T : ℝ, 1 ≤ T →
      gammaVerticalPhase σ T
        = (∫ t in (0 : ℝ)..(1 : ℝ), f t) + (T * Real.log T - T + 1)
          + ∫ t in (1 : ℝ)..T, ε t := by
    intro T hT
    have hsplit : gammaVerticalPhase σ T
        = (∫ t in (0 : ℝ)..(1 : ℝ), f t) + ∫ t in (1 : ℝ)..T, f t := by
      rw [gammaVerticalPhase, ← intervalIntegral.integral_add_adjacent_intervals
        (hcf.intervalIntegrable 0 1) (hcf.intervalIntegrable 1 T)]
    have hlogint : IntervalIntegrable Real.log MeasureTheory.volume 1 T :=
      intervalIntegral.intervalIntegrable_log (by
        rw [Set.uIcc_of_le hT, Set.mem_Icc]
        intro hmem
        linarith [hmem.1])
    have hεint : IntervalIntegrable ε MeasureTheory.volume 1 T :=
      (hcf.intervalIntegrable 1 T).sub hlogint
    have hlog : ∫ t in (1 : ℝ)..T, Real.log t = T * Real.log T - T + 1 := by
      rw [integral_log]
      simp
    have hfsplit : ∫ t in (1 : ℝ)..T, f t
        = (∫ t in (1 : ℝ)..T, Real.log t) + ∫ t in (1 : ℝ)..T, ε t := by
      rw [← intervalIntegral.integral_add hlogint hεint]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp [hε]
    rw [hsplit, hfsplit, hlog]
    ring
  have hlogtop : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hmul : Tendsto (fun T : ℝ => T * Real.log T) atTop atTop :=
    Filter.Tendsto.atTop_mul_atTop₀ tendsto_id hlogtop
  have hu : Tendsto (fun T : ℝ => 1 / (T * Real.log T)) atTop (𝓝 0) := by
    have h := hmul.inv_tendsto_atTop
    refine h.congr fun T => ?_
    simp [Pi.inv_apply, one_div]
  have hv : Tendsto (fun T : ℝ => 1 / Real.log T) atTop (𝓝 0) := by
    have h := hlogtop.inv_tendsto_atTop
    refine h.congr fun T => ?_
    simp [Pi.inv_apply, one_div]
  have hw : Tendsto (fun T : ℝ => (∫ t in (1 : ℝ)..T, ε t) / T) atTop (𝓝 0) :=
    tendsto_integral_div_atTop hcε hεlim
  set A₀ : ℝ := ∫ t in (0 : ℝ)..(1 : ℝ), f t with hA₀
  have hcomb : Tendsto (fun T : ℝ => A₀ * (1 / (T * Real.log T)) + 1 - 1 / Real.log T
      + 1 / (T * Real.log T)
      + ((∫ t in (1 : ℝ)..T, ε t) / T) * (1 / Real.log T)) atTop (𝓝 1) := by
    have := (((hu.const_mul A₀).add_const 1).sub hv).add hu |>.add (hw.mul hv)
    simpa using this
  refine Tendsto.congr' ?_ hcomb
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have hT1 : (1 : ℝ) ≤ T := hT.le
  have hlogpos : 0 < Real.log T := Real.log_pos hT
  have hTpos : (0 : ℝ) < T := by linarith
  rw [hA T hT1]
  field_simp
  ring

end RHTower
