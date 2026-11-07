import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarPaymentThresholdHierarchy
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarPaymentGrowsExponentiallyBelowTheOnset

/-!
# The polar-payment threshold grows exponentially in the onset aperture

Write `a*(ζ) = onsetAperture zetaZeroConfig` and let `R_c^{polar}(ζ) = polarPaymentCriticalThreshold`
be the supremum of the ratios `R > 0` at which every compact terminal window pays its polar capacity
(`PolarPaymentAt R A` for all `A ≥ 0`).

1. **Exponential polar band** (`exp_mul_le_polarPaymentCriticalThreshold`,
   `log_polarPaymentCriticalThreshold_ge_mul_onsetAperture`): there are universal `c₁, c₂ > 0` with
   `c₁ e^{c₂ a} ≤ R_c^{polar}(ζ)` for every `0 ≤ a ≤ a*(ζ)`; when `R_c^{polar}(ζ) < ⊤` this reads
   `log R_c^{polar}(ζ) ≥ c₂ a + log c₁`. The input is the zero-log-loss polar payment
   `exists_polarPaymentAt_exp_of_le_onsetAperture`.
2. **Continuum window thresholds under window positivity**
   (`windowThreshold_ge_exp_six_mul_of_zetaWindowPositive`,
   `windowThreshold_ge_exp_thirteen_quarters_mul_of_zetaWindowPositive`): `ZetaWindowPositive a`
   (`a ≥ 0`) is `a ≤ a*(ζ)`, so every window threshold satisfies
   `windowThreshold A ≥ c₀ e^{6a} ≥ c₀ e^{(13/4) a}` uniformly in `A ≥ 0`.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Zeta23 RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open CriticalArithmeticCorrelationTheory CohomologyOfWindowsOfSpecZ WindowTowerOfSpecZ
  WindowVisibilityLaw GaloisForLFunctions.SquareRootThreshold

/-- **The polar-payment threshold grows exponentially in the onset aperture.** There are
universal constants `c₁, c₂ > 0` such that `c₁ e^{c₂ a} ≤ polarPaymentCriticalThreshold` for
every `0 ≤ a ≤ a*(ζ)`. -/
theorem exp_mul_le_polarPaymentCriticalThreshold :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ {a : ℝ}, 0 ≤ a → (a : EReal) ≤ onsetAperture zetaZeroConfig →
        ((c₁ * Real.exp (c₂ * a) : ℝ) : EReal) ≤ polarPaymentCriticalThreshold := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hpay⟩ := exists_polarPaymentAt_exp_of_le_onsetAperture
  refine ⟨c₁, c₂, hc₁, hc₂, fun {a} ha0 ha => ?_⟩
  have hR : 0 < c₁ * Real.exp (c₂ * a) := mul_pos hc₁ (Real.exp_pos _)
  exact le_sSup ⟨c₁ * Real.exp (c₂ * a), ⟨hR, fun A hA => hpay ha0 ha hR le_rfl hA⟩, rfl⟩

/-- **Logarithmic form (`log R_c^{polar}(ζ) ≥ c₂ a + log c₁`).** With the constants of
`exp_mul_le_polarPaymentCriticalThreshold`, whenever `polarPaymentCriticalThreshold ≠ ⊤`,
`log c₁ + c₂ a ≤ log R_c^{polar}(ζ)` for every `0 ≤ a ≤ a*(ζ)`. -/
theorem log_polarPaymentCriticalThreshold_ge_mul_onsetAperture :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      (polarPaymentCriticalThreshold ≠ ⊤ →
        ∀ {a : ℝ}, 0 ≤ a → (a : EReal) ≤ onsetAperture zetaZeroConfig →
          Real.log c₁ + c₂ * a ≤ Real.log polarPaymentCriticalThreshold.toReal) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hle⟩ := exp_mul_le_polarPaymentCriticalThreshold
  refine ⟨c₁, c₂, hc₁, hc₂, fun htop {a} ha0 ha => ?_⟩
  have hexp_le := hle ha0 ha
  have hpos_thr := polarPaymentCriticalThreshold_pos
  cases hT : polarPaymentCriticalThreshold with
  | bot =>
    rw [hT] at hpos_thr
    exact absurd hpos_thr not_lt_bot
  | top => exact absurd hT htop
  | coe M =>
    rw [hT, EReal.coe_le_coe_iff] at hexp_le
    simp only [EReal.toReal_coe]
    have hlog := Real.log_le_log (mul_pos hc₁ (Real.exp_pos _)) hexp_le
    rwa [Real.log_mul hc₁.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog

/-- `ZetaWindowPositive a` at `a ≥ 0` places `a` below the onset aperture. -/
theorem le_onsetAperture_of_zetaWindowPositive {a : ℝ} (ha0 : 0 ≤ a)
    (hW : ZetaWindowPositive a) : (a : EReal) ≤ onsetAperture zetaZeroConfig :=
  (windowPositiveAt_iff_le_onsetAperture temperedConfig_zetaZeroConfig ha0).mp
    ((windowPositiveAt_zeta_iff a).mpr hW)

/-- **Continuum window thresholds under window positivity.** If `ZetaWindowPositive a` (`a ≥ 0`),
then `windowThresholdExponentialConstant * e^{6a} ≤ windowThreshold A` for every `A ≥ 0`. -/
theorem windowThreshold_ge_exp_six_mul_of_zetaWindowPositive {a : ℝ} (ha0 : 0 ≤ a)
    (hW : ZetaWindowPositive a) {A : ℝ} (hA : 0 ≤ A) :
    ((windowThresholdExponentialConstant * Real.exp (6 * a) : ℝ) : EReal) ≤ windowThreshold A :=
  (iInf_windowThreshold_ge_exp_six_mul_of_le_onsetAperture ha0
    (le_onsetAperture_of_zetaWindowPositive ha0 hW)).trans (iInf_le_of_le A (iInf_le _ hA))

/-- **Theorem 3 of the window-confinement card.** If `ZetaWindowPositive a` (`a ≥ 0`), then
`windowThresholdExponentialConstant * e^{(13/4) a} ≤ windowThreshold A` for every `A ≥ 0`. -/
theorem windowThreshold_ge_exp_thirteen_quarters_mul_of_zetaWindowPositive {a : ℝ} (ha0 : 0 ≤ a)
    (hW : ZetaWindowPositive a) {A : ℝ} (hA : 0 ≤ A) :
    ((windowThresholdExponentialConstant * Real.exp (13 / 4 * a) : ℝ) : EReal) ≤
      windowThreshold A := by
  refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (windowThreshold_ge_exp_six_mul_of_zetaWindowPositive ha0 hW hA)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
    windowThresholdExponentialConstant_pos.le

#print axioms exp_mul_le_polarPaymentCriticalThreshold
#print axioms log_polarPaymentCriticalThreshold_ge_mul_onsetAperture
#print axioms windowThreshold_ge_exp_thirteen_quarters_mul_of_zetaWindowPositive

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
