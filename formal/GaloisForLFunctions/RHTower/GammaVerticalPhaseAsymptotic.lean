import GaloisForLFunctions.RHTower.DigammaImaginaryVerticalAsymptotic
import GaloisForLFunctions.HTGeometry.IntegralCesaro
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
    Tendsto (fun T => (∫ t in (1 : ℝ)..T, ε t) / T) atTop (𝓝 0) :=
  HTGeometry.tendsto_integral_div_atTop hcont h

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
