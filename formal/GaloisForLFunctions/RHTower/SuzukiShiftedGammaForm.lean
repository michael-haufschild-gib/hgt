import GaloisForLFunctions.HTGeometry.GammaPairingFubini
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
    (hF2 : Integrable (fun L => F L ^ (2 : ℕ)))
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hform : IntegrableOn
      (fun s => (∫ L, shiftedSecondDifference σ F L s * F L) * gammaTransportKernel s)
      (Ioi 0)) :
    -(suzukiGammaShiftKappa σ * ∫ L, F L ^ (2 : ℕ)) ≤ shiftedGammaForm σ F := by
  have hker := integrableOn_suzukiGammaShiftLowerKernel hσ0 hσ1
  have hlow : IntegrableOn
      (fun s => -(suzukiGammaShiftLowerKernel σ s * ∫ L, F L ^ (2 : ℕ))) (Ioi 0) :=
    (hker.mul_const _).neg
  have hptw : ∀ s ∈ Ioi (0 : ℝ),
      -(suzukiGammaShiftLowerKernel σ s * ∫ L, F L ^ (2 : ℕ))
        ≤ (∫ L, shiftedSecondDifference σ F L s * F L) * gammaTransportKernel s := by
    intro s hs
    have hk : 0 < gammaTransportKernel s := gammaTransportKernel_pos hs
    have hb := neg_le_integral_shiftedSecondDifference hmeas hF2 σ s
    rw [suzukiGammaShiftLowerKernel_eq]
    nlinarith [hk.le, hb]
  have hmono := setIntegral_mono_on hlow hform measurableSet_Ioi hptw
  have hleft : (∫ s in Ioi (0 : ℝ), -(suzukiGammaShiftLowerKernel σ s * ∫ L, F L ^ (2 : ℕ)))
      = -(suzukiGammaShiftKappa σ * ∫ L, F L ^ (2 : ℕ)) := by
    rw [integral_neg, integral_mul_const, suzukiGammaShiftKappa]
  rw [hleft] at hmono
  exact hmono

/-- **The unshifted Gamma jump is a positive form.** -/
theorem shiftedGammaForm_zero_nonneg {F : ℝ → ℝ} (hmeas : AEStronglyMeasurable F volume)
    (hF2 : Integrable (fun L => F L ^ (2 : ℕ))) :
    0 ≤ shiftedGammaForm 0 F := by
  refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
  have hk : 0 < gammaTransportKernel s := gammaTransportKernel_pos hs
  have hb := neg_le_integral_shiftedSecondDifference hmeas hF2 0 s
  rw [zero_mul, Real.cosh_zero] at hb
  simp only [sub_self, mul_zero, zero_mul, neg_zero] at hb
  exact mul_nonneg hb hk.le

/-- The operator action of the conjugated Gamma jump: integrate the shifted second difference
against the kernel over the scale ray. -/
noncomputable def shiftedGammaJump (σ : ℝ) (F : ℝ → ℝ) (L : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), shiftedSecondDifference σ F L s * gammaTransportKernel s

/-- **The operator pairing is the scale form.** -/
theorem integral_shiftedGammaJump_mul_self {U : ℝ → ℝ} {K B σ : ℝ}
    (hmeas : Measurable U)
    (hK : ∀ x y : ℝ, |U x - U y| ≤ K * |x - y|) (hB : ∀ x, |U x| ≤ B)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hUint : Integrable U) :
    (∫ L, shiftedGammaJump σ U L * U L) = shiftedGammaForm σ U :=
  integral_gammaPairing_swap hmeas hK hB hσ0 hσ1 hUint

/-- The scale form of a Lipschitz, bounded, integrable profile is integrable in the scale. -/
theorem integrableOn_shiftedGammaFormIntegrand {U : ℝ → ℝ} {K B σ : ℝ}
    (hmeas : Measurable U)
    (hK : ∀ x y : ℝ, |U x - U y| ≤ K * |x - y|) (hB : ∀ x, |U x| ≤ B)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hUint : Integrable U) :
    IntegrableOn
      (fun s => (∫ L, shiftedSecondDifference σ U L s * U L) * gammaTransportKernel s)
      (Ioi 0) := by
  have h := (integrable_gammaPairing hmeas hK hB hσ0 hσ1 hUint).swap.integral_prod_left
  refine h.congr ?_
  filter_upwards with s
  rw [← integral_mul_const]
  refine integral_congr_ae ?_
  filter_upwards with L
  simp only [Function.comp_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair]
  ring

/-- **The numerical-range bound in operator form.**  The conjugated Gamma jump loses at most
`kappa_sigma` times the energy, on the class of Lipschitz, bounded, integrable profiles. -/
theorem neg_suzukiGammaShiftKappa_mul_le_gammaJumpPairing {U : ℝ → ℝ} {K B σ : ℝ}
    (hmeas : Measurable U)
    (hK : ∀ x y : ℝ, |U x - U y| ≤ K * |x - y|) (hB : ∀ x, |U x| ≤ B)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hUint : Integrable U)
    (hU2 : Integrable (fun L => U L ^ (2 : ℕ))) :
    -(suzukiGammaShiftKappa σ * ∫ L, U L ^ (2 : ℕ)) ≤ ∫ L, shiftedGammaJump σ U L * U L := by
  rw [integral_shiftedGammaJump_mul_self hmeas hK hB hσ0 hσ1 hUint]
  exact neg_suzukiGammaShiftKappa_mul_le_shiftedGammaForm hmeas.aestronglyMeasurable hU2 hσ0 hσ1
    (integrableOn_shiftedGammaFormIntegrand hmeas hK hB hσ0 hσ1 hUint)


end GaloisForLFunctions.RHTower
