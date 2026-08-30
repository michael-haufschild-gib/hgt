import GaloisForLFunctions.RHTower.BurnolSoninMellinHeadTail
import GaloisForLFunctions.RHTower.BurnolSoninFiniteJetEvaluation
import GaloisForLFunctions.RHTower.BurnolCoPoissonCompletedZeroJets

/-!
# Continuous completed first Mellin jet at Burnol's unit aperture

At the exceptional aperture `a = 1`, an extended Sonine vector has a literal
constant head and an `L²` tail.  The head--tail identity writes its Mellin
integral as

`c / (1 - w) + ∫₁∞ f(t)t⁻ʷ dt`.

This file packages both terms as bounded linear functionals and proves the
exact first-jet formula after Gamma completion.  It is the first genuine
higher-jet closure result for the literal `L₁` carrier: no zero, multiplicity,
or RH assertion is used.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The bounded raw Mellin tail functional at the unit aperture. -/
def soninMellinTailEvaluation (w : ℂ) (hlo : 1 / 2 < w.re) : SoninL2 →L[ℂ] ℂ :=
  (innerSL ℂ
      ((memLp_soninMellinKernel_Ioi hlo (by norm_num : (0 : ℝ) < 1)).star.toLp
        (star (soninMellinKernel w)))).comp
    (LpToLpRestrictCLM ℝ ℂ ℂ (volume : Measure ℝ) 2 (Ioi (1 : ℝ)))

/-- The Riesz realization of the tail functional is its literal Mellin tail. -/
theorem soninMellinTailEvaluation_apply (w : ℂ) (hlo : 1 / 2 < w.re) (f : SoninL2) :
    soninMellinTailEvaluation w hlo f =
      ∫ t in Ioi (1 : ℝ), (f : ℝ → ℂ) t * soninMellinKernel w t := by
  rw [soninMellinTailEvaluation, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (Ioi (1 : ℝ)) f,
    (memLp_soninMellinKernel_Ioi hlo (by norm_num : (0 : ℝ) < 1)).star.coeFn_toLp]
    with t hf hk
  rw [RCLike.inner_apply, hf, hk]
  change (f : ℝ → ℂ) t * star (star (soninMellinKernel w t)) =
    (f : ℝ → ℂ) t * soninMellinKernel w t
  rw [star_star]

/-- The intrinsic unit-aperture head coefficient, as a bounded functional on
the actual extended Sonine carrier. -/
def burnolExtendedSoninUnitHeadCoefficient :
    soninExtendedSpace (1 : ℝ) →L[ℂ] ℂ :=
  (innerSL ℂ (soninHeadIndicator (1 : ℝ))).comp
    (evenSubspace.subtypeL.comp (soninExtendedSpace (1 : ℝ)).subtypeL)

theorem burnolExtendedSoninUnitHeadCoefficient_apply (f : soninExtendedSpace (1 : ℝ)) :
    burnolExtendedSoninUnitHeadCoefficient f =
      inner ℂ (soninHeadIndicator (1 : ℝ))
        (((f : soninExtendedSpace (1 : ℝ)) : evenSubspace) : SoninL2) :=
  rfl

/-- The intrinsic head functional recovers the literal constant on the unit
head. -/
theorem burnolExtendedSoninUnitHeadCoefficient_eq_headConstant
    (f : soninExtendedSpace (1 : ℝ)) {c : ℂ}
    (hc : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (1 : ℝ))),
      ((((f : soninExtendedSpace (1 : ℝ)) : evenSubspace) : SoninL2) : ℝ → ℂ) t = c) :
    burnolExtendedSoninUnitHeadCoefficient f = c := by
  rw [burnolExtendedSoninUnitHeadCoefficient_apply, inner_soninHeadIndicator]
  rw [setIntegral_congr_ae measurableSet_Ioo
    (by
      filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hc] with t ht
      intro hmem
      exact ht hmem),
    setIntegral_const]
  norm_num

/-- The unit-aperture tail functional restricted to the extended Sonine
carrier. -/
def burnolExtendedSoninUnitTailEvaluation (w : ℂ) (hlo : 1 / 2 < w.re) :
    soninExtendedSpace (1 : ℝ) →L[ℂ] ℂ :=
  (soninMellinTailEvaluation w hlo).comp
    (evenSubspace.subtypeL.comp (soninExtendedSpace (1 : ℝ)).subtypeL)

theorem burnolExtendedSoninUnitTailEvaluation_apply
    (w : ℂ) (hlo : 1 / 2 < w.re) (f : soninExtendedSpace (1 : ℝ)) :
    burnolExtendedSoninUnitTailEvaluation w hlo f =
      soninMellinTailIntegral
        (((f : soninExtendedSpace (1 : ℝ)) : evenSubspace) : SoninL2) w := by
  rw [burnolExtendedSoninUnitTailEvaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, soninMellinTailEvaluation_apply]
  rfl

/-- The raw unit-aperture Mellin functional before Gamma completion. -/
def burnolExtendedSoninUnitRawEvaluation (w : ℂ) (hlo : 1 / 2 < w.re) :
    soninExtendedSpace (1 : ℝ) →L[ℂ] ℂ :=
  (1 - w)⁻¹ • burnolExtendedSoninUnitHeadCoefficient +
    burnolExtendedSoninUnitTailEvaluation w hlo

/-- The continuous first derivative functional of the Gamma-completed
unit-aperture Mellin evaluation. -/
def burnolExtendedSoninUnitFirstJetEvaluation
    (w : ℂ) (hlo : 1 / 2 < w.re) : soninExtendedSpace (1 : ℝ) →L[ℂ] ℂ :=
  (deriv mellinCompletionFactor w) • burnolExtendedSoninUnitRawEvaluation w hlo +
    mellinCompletionFactor w •
      ((1 - w)⁻¹ ^ 2 • burnolExtendedSoninUnitHeadCoefficient +
        (soninMellinTailDerivativeEvaluation w hlo).comp
          (evenSubspace.subtypeL.comp (soninExtendedSpace (1 : ℝ)).subtypeL))

/-- Literal formula for the packaged completed first jet. -/
theorem burnolExtendedSoninUnitFirstJetEvaluation_apply
    (w : ℂ) (hlo : 1 / 2 < w.re) (f : soninExtendedSpace (1 : ℝ)) {c : ℂ}
    (hc : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (1 : ℝ))),
      ((((f : soninExtendedSpace (1 : ℝ)) : evenSubspace) : SoninL2) : ℝ → ℂ) t = c) :
    burnolExtendedSoninUnitFirstJetEvaluation w hlo f =
      deriv mellinCompletionFactor w *
          (c * (1 - w)⁻¹ + soninMellinTailIntegral
            (((f : soninExtendedSpace (1 : ℝ)) : evenSubspace) : SoninL2) w) +
        mellinCompletionFactor w *
      (c * (1 - w)⁻¹ ^ 2 +
            soninMellinTailDerivativeEvaluation w hlo
              (((f : soninExtendedSpace (1 : ℝ)) : evenSubspace) : SoninL2)) := by
  have hhead := burnolExtendedSoninUnitHeadCoefficient_eq_headConstant f hc
  simp only [burnolExtendedSoninUnitFirstJetEvaluation,
    burnolExtendedSoninUnitRawEvaluation, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply]
  rw [hhead, burnolExtendedSoninUnitTailEvaluation_apply]
  simp only [smul_eq_mul, Submodule.subtypeL_apply]
  ring

/-- **Unit-aperture completed first-jet descent.** The literal completed
Mellin evaluation of every extended Sonine vector is complex differentiable
throughout the open critical strip, with derivative represented by the bounded
functional above. -/
theorem hasDerivAt_soninMellinEvaluation_unit_firstJet
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (f : soninExtendedSpace (1 : ℝ)) {c : ℂ}
    (hc : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (1 : ℝ))),
      ((((f : soninExtendedSpace (1 : ℝ)) : evenSubspace) : SoninL2) : ℝ → ℂ) t = c) :
    HasDerivAt
      (fun z : ℂ => soninMellinEvaluation z
        ((((f : soninExtendedSpace (1 : ℝ)) : evenSubspace) : SoninL2) : ℝ → ℂ))
      (burnolExtendedSoninUnitFirstJetEvaluation w hlo f) w := by
  rw [burnolExtendedSoninUnitFirstJetEvaluation_apply w hlo f hc]
  have hpos : 0 < w.re := by linarith
  have hgamma : HasDerivAt mellinCompletionFactor (deriv mellinCompletionFactor w) w :=
    (analyticAt_mellinCompletionFactor_of_re_pos hpos).differentiableAt.hasDerivAt
  have hsub : HasDerivAt (fun z : ℂ => 1 - z) (-1) w :=
    (hasDerivAt_id w).const_sub 1
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hinv : HasDerivAt ((fun z : ℂ => 1 - z)⁻¹) ((1 - w)⁻¹ ^ 2) w := by
    simpa only [neg_neg, one_div, inv_pow] using hsub.inv hne
  have hheadFun : (fun z : ℂ => c * (1 - z)⁻¹) =
      fun z : ℂ => c * ((fun y : ℂ => 1 - y)⁻¹) z := by
    funext z
    change c * (1 - z)⁻¹ = c * (1 - z)⁻¹
    rfl
  have hhead : HasDerivAt (fun z : ℂ => c * (1 - z)⁻¹)
      (c * (1 - w)⁻¹ ^ 2) w := by
    rw [hheadFun]
    exact hinv.const_mul c
  have htail := hasDerivAt_soninMellinTailIntegral_eq_tailDerivativeEvaluation hlo
    (((f : soninExtendedSpace (1 : ℝ)) : evenSubspace) : SoninL2)
  have hbracket := hhead.add htail
  have hmain := hgamma.mul hbracket
  have hUopen : IsOpen {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  apply hmain.congr_of_eventuallyEq
  filter_upwards [hUopen.mem_nhds ⟨hlo, hhi⟩] with z hz
  simpa [soninMellinTailIntegral] using
    (soninMellinEvaluation_head_tail hz.1 hz.2 (by norm_num : (0 : ℝ) < 1) f hc)

end RHTower
