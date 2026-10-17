import GaloisForLFunctions.RHTower.ThetaRenewalCausalDecay
import GaloisForLFunctions.HTGeometry.CausalExponentialIntegrals
import GaloisForLFunctions.HTGeometry.SchurKernelComposition
import GaloisForLFunctions.HTGeometry.SquareIntegrableKernelOperator

/-! # The actual theta renewal causal operator is Hilbert--Schmidt -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace RHTower
open GaloisForLFunctions.HTGeometry

local notation "μ₊" => Measure.restrict (volume : Measure ℝ) (Ioi 0)

abbrev ThetaRenewalL2 := Lp ℂ 2 μ₊

/-- Literal causal transport of the positive theta half-density. -/
def thetaRenewalCausalKernel (t a : ℝ) : ℂ :=
  if 0 < a ∧ a < t then
    ((thetaRenewalHalfDensity t / thetaRenewalHalfDensity a : ℝ) : ℂ) else 0

theorem measurable_thetaRenewalCausalKernel :
    Measurable (Function.uncurry thetaRenewalCausalKernel) := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      ((thetaRenewalHalfDensity p.1 / thetaRenewalHalfDensity p.2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((continuous_thetaRenewalHalfDensity.comp continuous_fst).div
        (continuous_thetaRenewalHalfDensity.comp continuous_snd)
        (fun p => (thetaRenewalHalfDensity_pos p.2).ne'))
  exact Measurable.ite
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)) hc.measurable measurable_const

theorem thetaRenewalCausalKernel_eq_zero {t a : ℝ} (h : t ≤ a) :
    thetaRenewalCausalKernel t a = 0 := by
  simp [thetaRenewalCausalKernel, not_lt_of_ge h]

theorem thetaRenewalCausalKernel_enorm {t a : ℝ} (ha : 0 < a) (hat : a < t) :
    ‖thetaRenewalCausalKernel t a‖ₑ =
      ENNReal.ofReal (thetaRenewalHalfDensity t / thetaRenewalHalfDensity a) := by
  rw [thetaRenewalCausalKernel, if_pos ⟨ha, hat⟩, ← ofReal_norm,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (thetaRenewalHalfDensity_pos t) (thetaRenewalHalfDensity_pos a))]

theorem lintegral_thetaRenewalCausalKernel_row (t : ℝ) :
    (∫⁻ a, ‖thetaRenewalCausalKernel t a‖ₑ ∂μ₊) ≤ 2 := by
  let F : ℝ → ℝ≥0∞ := (Iic t).indicator fun a =>
    ENNReal.ofReal (Real.exp (-((1 / 2) * (t - a))))
  have hle (a : ℝ) : ‖thetaRenewalCausalKernel t a‖ₑ ≤ F a := by
    by_cases h : 0 < a ∧ a < t
    · rw [thetaRenewalCausalKernel_enorm h.1 h.2]
      dsimp only [F]
      rw [Set.indicator_of_mem (show a ∈ Iic t from h.2.le)]
      apply ENNReal.ofReal_le_ofReal
      rw [show -((1 / 2 : ℝ) * (t - a)) = -(t - a) / 2 by ring]
      exact thetaRenewalHalfDensity_ratio_le_uniform h.1.le h.2.le
    · simp only [thetaRenewalCausalKernel, if_neg h, enorm_zero]
      exact bot_le
  calc (∫⁻ a, ‖thetaRenewalCausalKernel t a‖ₑ ∂μ₊)
      ≤ ∫⁻ a, F a ∂μ₊ := lintegral_mono hle
    _ ≤ ∫⁻ a, F a := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = 2 := by
      dsimp only [F]
      rw [lintegral_indicator measurableSet_Iic,
        lintegral_anticausal_exponential (by norm_num : (0 : ℝ) < 1 / 2)]
      norm_num

theorem lintegral_thetaRenewalCausalKernel_col (a : ℝ) :
    (∫⁻ t, ‖thetaRenewalCausalKernel t a‖ₑ ∂μ₊) ≤ 2 := by
  by_cases ha : 0 < a
  · let F : ℝ → ℝ≥0∞ := (Ioi a).indicator fun t =>
      ENNReal.ofReal (Real.exp (-((1 / 2) * (t - a))))
    have hle (t : ℝ) : ‖thetaRenewalCausalKernel t a‖ₑ ≤ F t := by
      by_cases hat : a < t
      · rw [thetaRenewalCausalKernel_enorm ha hat]
        dsimp only [F]
        rw [Set.indicator_of_mem (show t ∈ Ioi a from hat)]
        apply ENNReal.ofReal_le_ofReal
        rw [show -((1 / 2 : ℝ) * (t - a)) = -(t - a) / 2 by ring]
        exact thetaRenewalHalfDensity_ratio_le_uniform ha.le hat.le
      · rw [thetaRenewalCausalKernel_eq_zero (le_of_not_gt hat), enorm_zero]
        exact bot_le
    calc (∫⁻ t, ‖thetaRenewalCausalKernel t a‖ₑ ∂μ₊)
        ≤ ∫⁻ t, F t ∂μ₊ := lintegral_mono hle
      _ ≤ ∫⁻ t, F t := lintegral_mono' Measure.restrict_le_self le_rfl
      _ = 2 := by
        dsimp only [F]
        rw [lintegral_indicator measurableSet_Ioi,
          lintegral_causal_exponential (by norm_num : (0 : ℝ) < 1 / 2)]
        norm_num
  · simp [thetaRenewalCausalKernel, ha]

/-- The column energy decays in its starting point, unlike the uniform Schur bound. -/
theorem lintegral_thetaRenewalCausalKernel_sq_col {a : ℝ} (ha : 0 < a) :
    (∫⁻ t, ‖thetaRenewalCausalKernel t a‖ₑ ^ 2 ∂μ₊) ≤
      ENNReal.ofReal (Real.exp (-a)) := by
  let F : ℝ → ℝ≥0∞ := (Ioi a).indicator fun t =>
    ENNReal.ofReal (Real.exp (-(Real.exp a * (t - a))))
  have hle (t : ℝ) : ‖thetaRenewalCausalKernel t a‖ₑ ^ 2 ≤ F t := by
    by_cases hat : a < t
    · rw [thetaRenewalCausalKernel_enorm ha hat,
        ← ENNReal.ofReal_pow (div_pos (thetaRenewalHalfDensity_pos t)
          (thetaRenewalHalfDensity_pos a)).le, thetaRenewalHalfDensity_ratio_sq]
      dsimp only [F]
      rw [Set.indicator_of_mem (show t ∈ Ioi a from hat)]
      exact ENNReal.ofReal_le_ofReal (thetaRenewalIncrement_ratio_le_exp ha.le hat.le)
    · rw [thetaRenewalCausalKernel_eq_zero (le_of_not_gt hat), enorm_zero,
        zero_pow (by decide : 2 ≠ 0)]
      exact bot_le
  calc (∫⁻ t, ‖thetaRenewalCausalKernel t a‖ₑ ^ 2 ∂μ₊)
      ≤ ∫⁻ t, F t ∂μ₊ := lintegral_mono hle
    _ ≤ ∫⁻ t, F t := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ENNReal.ofReal (Real.exp (-a)) := by
      dsimp only [F]
      rw [lintegral_indicator measurableSet_Ioi,
        lintegral_causal_exponential (Real.exp_pos a), Real.exp_neg, one_div]

theorem lintegral_thetaRenewalCausalKernel_sq_le_one :
    (∫⁻ t, ∫⁻ a, ‖thetaRenewalCausalKernel t a‖ₑ ^ 2 ∂μ₊ ∂μ₊) ≤ 1 := by
  rw [lintegral_lintegral_swap
    (measurable_thetaRenewalCausalKernel.enorm.pow_const 2).aemeasurable]
  calc (∫⁻ a, ∫⁻ t, ‖thetaRenewalCausalKernel t a‖ₑ ^ 2 ∂μ₊ ∂μ₊)
      ≤ ∫⁻ a, ENNReal.ofReal (Real.exp (-a)) ∂μ₊ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
        exact lintegral_thetaRenewalCausalKernel_sq_col ha
    _ = 1 := by
      simpa using lintegral_causal_exponential (by norm_num : (0 : ℝ) < 1) 0

def thetaRenewalSchurKernel : SchurKernel μ₊ where
  toFun := thetaRenewalCausalKernel
  measurable := measurable_thetaRenewalCausalKernel
  bound := 2
  row := lintegral_thetaRenewalCausalKernel_row
  col := lintegral_thetaRenewalCausalKernel_col

def thetaRenewalSqIntKernel : SqIntKernel μ₊ μ₊ where
  toFun := thetaRenewalCausalKernel
  measurable := measurable_thetaRenewalCausalKernel
  energy_lt_top := lintegral_thetaRenewalCausalKernel_sq_le_one.trans_lt (by simp)

/-- The bounded operator is constructed from the literal theta transport kernel. -/
def thetaRenewalCausalOperator : ThetaRenewalL2 →L[ℂ] ThetaRenewalL2 :=
  thetaRenewalSchurKernel.op

theorem thetaRenewalCausalOperator_isHilbertSchmidt :
    ContinuousLinearMap.IsHilbertSchmidt thetaRenewalCausalOperator :=
  thetaRenewalSchurKernel.isHilbertSchmidt_op thetaRenewalSqIntKernel.energy_lt_top

theorem thetaRenewalCausalOperator_isCompact :
    IsCompactOperator thetaRenewalCausalOperator :=
  thetaRenewalCausalOperator_isHilbertSchmidt.isCompactOperator

end RHTower
