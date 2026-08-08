import GaloisForLFunctions.HTGeometry.GammaJumpTranslationEnergy
import GaloisForLFunctions.RHTower.SuzukiGammaShiftKappa

/-!
# The integrated numerical range of the shifted Gamma jump

Integrating the per-scale translation-energy bound against the Gamma kernel gives the exact
numerical-range statement the coercive tail estimate consumes:

`-kappa_sigma ‖F‖² ≤ ⟨R_sigma F, F⟩`.

Nothing here transforms.  The per-scale bound is the physical-space identity
`∫ [2F − e^{-σs}F(·+s) − e^{σs}F(·−s)] F = ∫ [F(·+s) − F]² − 2(cosh σs − 1) ∫ F(·+s) F`,
and `kappa_sigma` is by definition the scale integral of `2(cosh σs − 1)/(e^s − 1)`.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The shifted Gamma quadratic form of a profile: the scale integral of its pairings. -/
noncomputable def shiftedGammaForm (σ : ℝ) (F : ℝ → ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), (∫ L, shiftedSecondDifference σ F L s * F L) * gammaTransportKernel s

theorem suzukiGammaShiftLowerKernel_eq (σ s : ℝ) :
    suzukiGammaShiftLowerKernel σ s
      = 2 * (Real.cosh (σ * s) - 1) * gammaTransportKernel s := by
  rw [suzukiGammaShiftLowerKernel, gammaTransportKernel]
  ring

/-- **The integrated numerical-range bound `(11)`.**  The shifted Gamma form loses at most
`kappa_sigma` times the energy. -/
theorem neg_suzukiGammaShiftKappa_mul_le_shiftedGammaForm
    {F : ℝ → ℝ} (hmeas : AEStronglyMeasurable F volume)
    (hF2 : Integrable (fun L => F L ^ 2))
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hform : IntegrableOn
      (fun s => (∫ L, shiftedSecondDifference σ F L s * F L) * gammaTransportKernel s)
      (Ioi 0)) :
    -(suzukiGammaShiftKappa σ * ∫ L, F L ^ 2) ≤ shiftedGammaForm σ F := by
  have hker := integrableOn_suzukiGammaShiftLowerKernel hσ0 hσ1
  have hlow : IntegrableOn
      (fun s => -(suzukiGammaShiftLowerKernel σ s * ∫ L, F L ^ 2)) (Ioi 0) :=
    (hker.mul_const _).neg
  have hptw : ∀ s ∈ Ioi (0 : ℝ),
      -(suzukiGammaShiftLowerKernel σ s * ∫ L, F L ^ 2)
        ≤ (∫ L, shiftedSecondDifference σ F L s * F L) * gammaTransportKernel s := by
    intro s hs
    have hk : 0 < gammaTransportKernel s := gammaTransportKernel_pos hs
    have hb := neg_le_integral_shiftedSecondDifference hmeas hF2 σ s
    rw [suzukiGammaShiftLowerKernel_eq]
    nlinarith [hk.le, hb]
  have hmono := setIntegral_mono_on hlow hform measurableSet_Ioi hptw
  have hleft : (∫ s in Ioi (0 : ℝ), -(suzukiGammaShiftLowerKernel σ s * ∫ L, F L ^ 2))
      = -(suzukiGammaShiftKappa σ * ∫ L, F L ^ 2) := by
    rw [integral_neg, integral_mul_const, suzukiGammaShiftKappa]
  rw [hleft] at hmono
  exact hmono

/-- **The unshifted Gamma jump is a positive form.** -/
theorem shiftedGammaForm_zero_nonneg {F : ℝ → ℝ} (hmeas : AEStronglyMeasurable F volume)
    (hF2 : Integrable (fun L => F L ^ 2)) :
    0 ≤ shiftedGammaForm 0 F := by
  refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
  have hk : 0 < gammaTransportKernel s := gammaTransportKernel_pos hs
  have hb := neg_le_integral_shiftedSecondDifference hmeas hF2 0 s
  rw [zero_mul, Real.cosh_zero] at hb
  simp only [sub_self, mul_zero, zero_mul, neg_zero] at hb
  exact mul_nonneg hb hk.le

end GaloisForLFunctions.RHTower
