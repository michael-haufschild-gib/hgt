import GaloisForLFunctions.RHTower.DeningerMeyerStrongLogTopology
import GaloisForLFunctions.RHTower.DeningerMeyerStrongLogMellin
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Complex MeasureTheory Set Topology
open scoped BoundedContinuousFunction

namespace RHTower

noncomputable section

private abbrev Strong := DeningerMeyerStrongLogTarget
private abbrev BCF := ℝ →ᵇ ℂ

private theorem integrable_strongMellinTopKernel_mul
    (a : ℂ) (ha : a.re < 0) (F : BCF) :
    Integrable (fun t : ℝ => Complex.exp (a * t) * F t)
      (volume.restrict (Ioi 0)) := by
  apply (integrableOn_exp_mul_complex_Ioi ha 0).mul_bdd
  · exact F.continuous.aestronglyMeasurable.restrict
  · exact Filter.Eventually.of_forall fun t => F.norm_coe_le_norm t

private theorem integrable_strongMellinBotKernel_mul
    (a : ℂ) (ha : 0 < a.re) (F : BCF) :
    Integrable (fun t : ℝ => Complex.exp (a * t) * F t)
      (volume.restrict (Iic 0)) := by
  apply (integrableOn_exp_mul_complex_Iic ha 0).mul_bdd
  · exact F.continuous.aestronglyMeasurable.restrict
  · exact Filter.Eventually.of_forall fun t => F.norm_coe_le_norm t

private def strongMellinTopIntegralLM (a : ℂ) (ha : a.re < 0) :
    BCF →ₗ[ℂ] ℂ where
  toFun F := ∫ t : ℝ in Ioi 0, Complex.exp (a * t) * F t
  map_add' F G := by
    rw [show (fun t : ℝ => Complex.exp (a * t) * (F + G) t) =
        (fun t : ℝ => Complex.exp (a * t) * F t) +
          fun t : ℝ => Complex.exp (a * t) * G t by
      funext t
      simp [mul_add]]
    exact integral_add
      (integrable_strongMellinTopKernel_mul a ha F)
      (integrable_strongMellinTopKernel_mul a ha G)
  map_smul' c F := by
    rw [show (fun t : ℝ => Complex.exp (a * t) * (c • F) t) =
        fun t : ℝ => c * (Complex.exp (a * t) * F t) by
      funext t
      simp
      ring]
    exact integral_const_mul c _

private theorem strongMellinTopIntegralLM_norm_le
    (a : ℂ) (ha : a.re < 0) (F : BCF) :
    ‖strongMellinTopIntegralLM a ha F‖ ≤
      (-1 / a.re) * ‖F‖ := by
  have hmajor : Integrable
      (fun t : ℝ => ‖F‖ * Real.exp (a.re * t))
      (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_mul_Ioi ha 0).const_mul ‖F‖
  have hbound := norm_integral_le_of_norm_le
    (f := fun t : ℝ => Complex.exp (a * t) * F t)
    (g := fun t : ℝ => ‖F‖ * Real.exp (a.re * t))
    (μ := volume.restrict (Ioi 0)) hmajor
    (Filter.Eventually.of_forall fun t => by
      rw [norm_mul, Complex.norm_exp]
      simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      change Real.exp (a.re * t) * ‖F t‖ ≤
        ‖F‖ * Real.exp (a.re * t)
      nlinarith [F.norm_coe_le_norm t, Real.exp_pos (a.re * t)])
  rw [integral_const_mul, integral_exp_mul_Ioi ha 0] at hbound
  simpa [strongMellinTopIntegralLM, mul_comm] using hbound

private def strongMellinTopIntegralCLM (a : ℂ) (ha : a.re < 0) :
    BCF →L[ℂ] ℂ :=
  LinearMap.mkContinuous (strongMellinTopIntegralLM a ha)
    (-1 / a.re) (strongMellinTopIntegralLM_norm_le a ha)

private def strongMellinBotIntegralLM (a : ℂ) (ha : 0 < a.re) :
    BCF →ₗ[ℂ] ℂ where
  toFun F := ∫ t : ℝ in Iic 0, Complex.exp (a * t) * F t
  map_add' F G := by
    rw [show (fun t : ℝ => Complex.exp (a * t) * (F + G) t) =
        (fun t : ℝ => Complex.exp (a * t) * F t) +
          fun t : ℝ => Complex.exp (a * t) * G t by
      funext t
      simp [mul_add]]
    exact integral_add
      (integrable_strongMellinBotKernel_mul a ha F)
      (integrable_strongMellinBotKernel_mul a ha G)
  map_smul' c F := by
    rw [show (fun t : ℝ => Complex.exp (a * t) * (c • F) t) =
        fun t : ℝ => c * (Complex.exp (a * t) * F t) by
      funext t
      simp
      ring]
    exact integral_const_mul c _

private theorem strongMellinBotIntegralLM_norm_le
    (a : ℂ) (ha : 0 < a.re) (F : BCF) :
    ‖strongMellinBotIntegralLM a ha F‖ ≤
      (1 / a.re) * ‖F‖ := by
  have hmajor : Integrable
      (fun t : ℝ => ‖F‖ * Real.exp (a.re * t))
      (volume.restrict (Iic 0)) :=
    (integrableOn_exp_mul_Iic ha 0).const_mul ‖F‖
  have hbound := norm_integral_le_of_norm_le
    (f := fun t : ℝ => Complex.exp (a * t) * F t)
    (g := fun t : ℝ => ‖F‖ * Real.exp (a.re * t))
    (μ := volume.restrict (Iic 0)) hmajor
    (Filter.Eventually.of_forall fun t => by
      rw [norm_mul, Complex.norm_exp]
      simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      change Real.exp (a.re * t) * ‖F t‖ ≤
        ‖F‖ * Real.exp (a.re * t)
      nlinarith [F.norm_coe_le_norm t, Real.exp_pos (a.re * t)])
  rw [integral_const_mul, integral_exp_mul_Iic ha 0] at hbound
  simpa [strongMellinBotIntegralLM, mul_comm] using hbound

private def strongMellinBotIntegralCLM (a : ℂ) (ha : 0 < a.re) :
    BCF →L[ℂ] ℂ :=
  LinearMap.mkContinuous (strongMellinBotIntegralLM a ha)
    (1 / a.re) (strongMellinBotIntegralLM_norm_le a ha)

private theorem strongMellinTop_gauge_eq
    (s : ℂ) (k : ℤ) (g : Strong) (t : ℝ) :
    Complex.exp ((s - (k : ℂ)) * t) *
        deningerMeyerStrongLogGauge 0 k g t =
      deningerMeyerStrongLogMellinJet 0 s g t := by
  rw [deningerMeyerStrongLogGauge_apply, iteratedDeriv_zero]
  simp only [deningerMeyerStrongLogMellinJet, pow_zero, one_mul]
  rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
  rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem strongMellinBot_gauge_eq
    (s : ℂ) (k : ℤ) (g : Strong) (t : ℝ) :
    Complex.exp ((s + (k : ℂ)) * t) *
        deningerMeyerStrongLogGauge 0 (-k) g t =
      deningerMeyerStrongLogMellinJet 0 s g t := by
  rw [deningerMeyerStrongLogGauge_apply, iteratedDeriv_zero]
  simp only [deningerMeyerStrongLogMellinJet, pow_zero, one_mul]
  rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
  rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem deningerMeyerStrongLogMellin_eq_weighted_gauges
    (s : ℂ) (k : ℤ)
    (htop : (s - (k : ℂ)).re < 0)
    (hbot : 0 < (s + (k : ℂ)).re)
    (g : Strong) :
    deningerMeyerStrongLogMellinLM s g =
      strongMellinBotIntegralCLM (s + (k : ℂ)) hbot
          (deningerMeyerStrongLogGaugeLinear 0 (-k) g) +
        strongMellinTopIntegralCLM (s - (k : ℂ)) htop
          (deningerMeyerStrongLogGaugeLinear 0 k g) := by
  change (∫ t : ℝ, deningerMeyerStrongLogMellinJet 0 s g t) = _
  change (∫ t : ℝ, deningerMeyerStrongLogMellinJet 0 s g t) =
    (∫ t : ℝ in Iic 0,
      Complex.exp ((s + (k : ℂ)) * t) *
        deningerMeyerStrongLogGauge 0 (-k) g t) +
    ∫ t : ℝ in Ioi 0,
      Complex.exp ((s - (k : ℂ)) * t) *
        deningerMeyerStrongLogGauge 0 k g t
  rw [show (∫ t : ℝ in Iic 0,
        Complex.exp ((s + (k : ℂ)) * t) *
          deningerMeyerStrongLogGauge 0 (-k) g t) =
      ∫ t : ℝ in Iic 0, deningerMeyerStrongLogMellinJet 0 s g t by
    apply setIntegral_congr_fun measurableSet_Iic
    intro t _
    exact strongMellinBot_gauge_eq s k g t]
  rw [show (∫ t : ℝ in Ioi 0,
        Complex.exp ((s - (k : ℂ)) * t) *
          deningerMeyerStrongLogGauge 0 k g t) =
      ∫ t : ℝ in Ioi 0, deningerMeyerStrongLogMellinJet 0 s g t by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    exact strongMellinTop_gauge_eq s k g t]
  exact (intervalIntegral.integral_Iic_add_Ioi
    (integrable_deningerMeyerStrongLogMellinJet g.property 0 s).integrableOn
    (integrable_deningerMeyerStrongLogMellinJet g.property 0 s).integrableOn).symm

theorem continuous_deningerMeyerStrongLogMellinLM_of_integer_bound
    (s : ℂ) (k : ℤ)
    (htop : (s - (k : ℂ)).re < 0)
    (hbot : 0 < (s + (k : ℂ)).re) :
    @Continuous Strong ℂ deningerMeyerStrongLogTopology inferInstance
      (deningerMeyerStrongLogMellinLM s) := by
  letI : TopologicalSpace Strong := deningerMeyerStrongLogTopology
  have hBot : Continuous (fun g : Strong =>
      strongMellinBotIntegralCLM (s + (k : ℂ)) hbot
        (deningerMeyerStrongLogGaugeLinear 0 (-k) g)) :=
    (strongMellinBotIntegralCLM (s + (k : ℂ)) hbot).continuous.comp
      (continuous_deningerMeyerStrongLogGaugeLinear 0 (-k))
  have hTop : Continuous (fun g : Strong =>
      strongMellinTopIntegralCLM (s - (k : ℂ)) htop
        (deningerMeyerStrongLogGaugeLinear 0 k g)) :=
    (strongMellinTopIntegralCLM (s - (k : ℂ)) htop).continuous.comp
      (continuous_deningerMeyerStrongLogGaugeLinear 0 k)
  convert hBot.add hTop using 1
  funext g
  exact deningerMeyerStrongLogMellin_eq_weighted_gauges s k htop hbot g

theorem continuous_deningerMeyerStrongLogMellinLM (s : ℂ) :
    @Continuous Strong ℂ deningerMeyerStrongLogTopology inferInstance
      (deningerMeyerStrongLogMellinLM s) := by
  obtain ⟨N : ℕ, hN : |s.re| < N⟩ := exists_nat_gt |s.re|
  let k : ℤ := N
  apply continuous_deningerMeyerStrongLogMellinLM_of_integer_bound s k
  · change s.re - (k : ℝ) < 0
    dsimp [k]
    have hs := le_abs_self s.re
    exact sub_neg.mpr (lt_of_le_of_lt hs hN)
  · change 0 < s.re + (k : ℝ)
    have hk : (k : ℝ) = (N : ℝ) := rfl
    rw [hk]
    have hs := neg_le_abs s.re
    have hN' : |s.re| < (N : ℝ) := hN
    linarith

end

end RHTower
