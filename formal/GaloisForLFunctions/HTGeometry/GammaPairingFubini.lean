import GaloisForLFunctions.HTGeometry.GammaPairingMajorant

/-!
# Joint integrability of the Gamma pairing

The scale majorant does not depend on the base point, so the Gamma pairing's double integrand is
dominated by a product of two separately integrable functions, one in each variable.  Joint
integrability on the product measure follows, which is the hypothesis `integral_integral_swap`
needs to exchange the base-point and scale integrations.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- On the product of the line with the positive scale ray, the scale variable is positive. -/
theorem ae_snd_pos_prod_restrict :
    ∀ᵐ z : ℝ × ℝ ∂((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))), (0 : ℝ) < z.2 := by
  have h : (volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))
      = ((volume : Measure ℝ).prod volume).restrict (univ ×ˢ Ioi (0 : ℝ)) := by
    rw [show (volume : Measure ℝ) = (volume : Measure ℝ).restrict univ from
      (Measure.restrict_univ).symm]
    rw [Measure.prod_restrict]
    simp
  rw [h]
  filter_upwards [self_mem_ae_restrict (MeasurableSet.univ.prod measurableSet_Ioi)] with z hz
  exact hz.2

/-- **Joint integrability of the Gamma pairing.**  A Lipschitz, bounded, integrable profile makes
the double integrand of the conjugated Gamma pairing integrable on the product. -/
theorem integrable_gammaPairing {U : ℝ → ℝ} {K B σ : ℝ}
    (hmeas : Measurable U)
    (hK : ∀ x y : ℝ, |U x - U y| ≤ K * |x - y|) (hB : ∀ x, |U x| ≤ B)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hUint : Integrable U) :
    Integrable
      (Function.uncurry fun L s => shiftedSecondDifference σ U L s * gammaTransportKernel s * U L)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmajInt : IntegrableOn (gammaPairingMajorant K B σ) (Ioi 0) :=
    integrableOn_gammaPairingMajorant hσ1
  have hdom : Integrable
      (fun z : ℝ × ℝ => |U z.1| * gammaPairingMajorant K B σ z.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    Integrable.mul_prod hUint.abs hmajInt
  have hD : Measurable (Function.uncurry fun L s : ℝ => shiftedSecondDifference σ U L s) := by
    unfold shiftedSecondDifference
    fun_prop
  have hmeas2 : Measurable
      (Function.uncurry fun L s => shiftedSecondDifference σ U L s
        * gammaTransportKernel s * U L) :=
    (hD.mul (measurable_gammaTransportKernel.comp measurable_snd)).mul (hmeas.comp measurable_fst)
  refine Integrable.mono' hdom hmeas2.aestronglyMeasurable ?_
  filter_upwards [ae_snd_pos_prod_restrict] with z hz
  have hbound := abs_shiftedSecondDifference_mul_kernel_le hK hB hσ0 hz z.1
  show ‖shiftedSecondDifference σ U z.1 z.2 * gammaTransportKernel z.2 * U z.1‖
      ≤ |U z.1| * gammaPairingMajorant K B σ z.2
  rw [Real.norm_eq_abs, abs_mul]
  calc |shiftedSecondDifference σ U z.1 z.2 * gammaTransportKernel z.2| * |U z.1|
      ≤ gammaPairingMajorant K B σ z.2 * |U z.1| :=
        mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
    _ = |U z.1| * gammaPairingMajorant K B σ z.2 := by ring

/-- **The exchange.**  The operator pairing of the conjugated Gamma jump equals its scale form. -/
theorem integral_gammaPairing_swap {U : ℝ → ℝ} {K B σ : ℝ}
    (hmeas : Measurable U)
    (hK : ∀ x y : ℝ, |U x - U y| ≤ K * |x - y|) (hB : ∀ x, |U x| ≤ B)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hUint : Integrable U) :
    (∫ L, (∫ s in Ioi (0 : ℝ), shiftedSecondDifference σ U L s * gammaTransportKernel s) * U L)
      = ∫ s in Ioi (0 : ℝ),
          (∫ L, shiftedSecondDifference σ U L s * U L) * gammaTransportKernel s := by
  have hswap := integral_integral_swap (integrable_gammaPairing hmeas hK hB hσ0 hσ1 hUint)
  have hl : ∀ L : ℝ,
      (∫ s in Ioi (0 : ℝ), shiftedSecondDifference σ U L s * gammaTransportKernel s * U L)
        = (∫ s in Ioi (0 : ℝ), shiftedSecondDifference σ U L s * gammaTransportKernel s) * U L :=
    fun L => integral_mul_const _ _
  have hr : ∀ s : ℝ, (∫ L, shiftedSecondDifference σ U L s * gammaTransportKernel s * U L)
      = (∫ L, shiftedSecondDifference σ U L s * U L) * gammaTransportKernel s := by
    intro s
    rw [← integral_mul_const]
    refine integral_congr_ae ?_
    filter_upwards with L
    ring
  simp only [hl, hr] at hswap
  exact hswap


end GaloisForLFunctions.HTGeometry
