import GaloisForLFunctions.RHTower.Sieve.MaynardPairedKernelBufferedHandoff

/-!
# Common-mode phase-extraction window

The *pointwise* narrow target window is close to the point-mass Mellin phase when
`mu > 80 / 49`.  A dyadic-shell integral pays its length once more, so the actual integrated
target error decays only when `mu > 160 / 49`.  An arbitrary-order tail removes the wide
reference below `1 / (1 - theta)`.  This file records the exact nonempty analytic interval; it
does not assert an arithmetic large-value receiver there.
-/

namespace RHTower.Sieve

noncomputable section

open Complex MeasureTheory Set

/-- Pointwise target-to-phase error becomes decaying at this height exponent. -/
def routeTPhaseExtractionTargetMu : ℝ := 80 / 49

/-- Height exponent at which the reference's arbitrary-order tail ceases to have a power reserve. -/
def routeTPhaseExtractionReferenceMu : ℝ :=
  1 / (1 - routeTPhysicalSliceHandoffTheta)

/-- The pointwise target phase error is scale-neutral at this endpoint. -/
theorem routeT_phaseExtraction_target_boundary :
    1 - routeTPhaseExtractionTargetMu * (49 / 80 : ℝ) = 0 := by
  norm_num [routeTPhaseExtractionTargetMu]

/-- Above the pointwise endpoint, replacement of the target kernel by its point-mass phase has a
strict negative pointwise exponent. -/
theorem routeT_phaseExtraction_targetErrorExponent_neg
    {mu : ℝ} (hmu : routeTPhaseExtractionTargetMu < mu) :
    1 - mu * (49 / 80 : ℝ) < 0 := by
  rw [routeTPhaseExtractionTargetMu] at hmu
  linarith

/-- The actual shell integral pays the pointwise Mellin defect and the shell length. -/
def routeTPhaseExtractionIntegratedTargetMu : ℝ := 160 / 49

/-- The integrated target-to-phase error is scale-neutral precisely at `160 / 49`. -/
theorem routeT_phaseExtraction_integratedTarget_boundary :
    2 - routeTPhaseExtractionIntegratedTargetMu * (49 / 80 : ℝ) = 0 := by
  norm_num [routeTPhaseExtractionIntegratedTargetMu]

/-- Above `160 / 49`, the target-to-phase error integrated across a dyadic shell has a strictly
negative power exponent. -/
theorem routeT_phaseExtraction_integratedTargetErrorExponent_neg
    {mu : ℝ} (hmu : routeTPhaseExtractionIntegratedTargetMu < mu) :
    2 - mu * (49 / 80 : ℝ) < 0 := by
  rw [routeTPhaseExtractionIntegratedTargetMu] at hmu
  linarith

/-- The reference endpoint is the exact equality boundary for arbitrary-order reference-tail
decay. -/
theorem routeT_phaseExtraction_reference_boundary :
    routeTPhaseExtractionReferenceMu *
        (1 - routeTPhysicalSliceHandoffTheta) = 1 := by
  have hden : 0 < 1 - routeTPhysicalSliceHandoffTheta := by
    linarith [routeTPhysicalSliceHandoffTheta_lt_three_fourths]
  rw [routeTPhaseExtractionReferenceMu]
  field_simp [hden.ne']

/-- Below the reference endpoint, the reference-tail power exponent is strictly below one. -/
theorem routeT_phaseExtraction_referenceTailExponent_lt_one
    {mu : ℝ} (hmu : mu < routeTPhaseExtractionReferenceMu) :
    mu * (1 - routeTPhysicalSliceHandoffTheta) < 1 := by
  have hden : 0 < 1 - routeTPhysicalSliceHandoffTheta := by
    linarith [routeTPhysicalSliceHandoffTheta_lt_three_fourths]
  calc
    mu * (1 - routeTPhysicalSliceHandoffTheta) <
        routeTPhaseExtractionReferenceMu *
          (1 - routeTPhysicalSliceHandoffTheta) :=
      mul_lt_mul_of_pos_right hmu hden
    _ = 1 := routeT_phaseExtraction_reference_boundary

/-- The pointwise target regime begins strictly below the reference-tail boundary. -/
theorem routeT_phaseExtraction_target_lt_reference :
    routeTPhaseExtractionTargetMu < routeTPhaseExtractionReferenceMu := by
  have hd : maynardLongGlobalAmplitudeDeficit < 1 / 100 :=
    maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  have hden : 0 < 1 - routeTPhysicalSliceHandoffTheta := by
    linarith [routeTPhysicalSliceHandoffTheta_lt_three_fourths]
  rw [routeTPhaseExtractionTargetMu, routeTPhaseExtractionReferenceMu]
  apply (lt_div_iff₀ hden).2
  dsimp only [routeTPhysicalSliceHandoffTheta]
  nlinarith

/-- The *integrated* target regime remains nonempty below the reference-tail boundary.  This is
the real analytic phase-extraction window; the weaker `80 / 49` condition only controls the
integrand before shell integration. -/
theorem routeT_phaseExtraction_integratedTarget_lt_reference :
    routeTPhaseExtractionIntegratedTargetMu < routeTPhaseExtractionReferenceMu := by
  have hd : maynardLongGlobalAmplitudeDeficit < 1 / 100 :=
    maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  have hden : 0 < 1 - routeTPhysicalSliceHandoffTheta := by
    linarith [routeTPhysicalSliceHandoffTheta_lt_three_fourths]
  rw [routeTPhaseExtractionIntegratedTargetMu, routeTPhaseExtractionReferenceMu]
  apply (lt_div_iff₀ hden).2
  dsimp only [routeTPhysicalSliceHandoffTheta]
  nlinarith

/-- The analytic phase window begins strictly beyond the complete `11 / 5` selected-cell
extraction presently available in Route T. -/
theorem routeT_elevenFifths_lt_phaseExtraction_integratedTarget :
    (11 / 5 : ℝ) < routeTPhaseExtractionIntegratedTargetMu := by
  norm_num [routeTPhaseExtractionIntegratedTargetMu]

/-- The analytic phase window ends strictly before the existing upper-seam selected-cell count
starts.  Thus neither known selected-cell regime can consume this phase transfer. -/
theorem routeT_phaseExtraction_reference_lt_upperSeam :
    routeTPhaseExtractionReferenceMu < (17 / 4 : ℝ) := by
  have hd : 0 < maynardLongGlobalAmplitudeDeficit :=
    maynardLongGlobalAmplitudeDeficit_pos
  have hden : 0 < 1 - routeTPhysicalSliceHandoffTheta := by
    linarith [routeTPhysicalSliceHandoffTheta_lt_three_fourths]
  rw [routeTPhaseExtractionReferenceMu]
  apply (div_lt_iff₀ hden).2
  dsimp only [routeTPhysicalSliceHandoffTheta]
  nlinarith

/-- Every exponent for which the integrated phase transfer has both target and reference power
reserve lies in the unresolved selected-cell gap. -/
theorem routeT_phaseExtraction_integratedWindow_in_selectedCellGap
    {mu : ℝ} (htarget : routeTPhaseExtractionIntegratedTargetMu < mu)
    (href : mu < routeTPhaseExtractionReferenceMu) :
    (11 / 5 : ℝ) < mu ∧ mu < 17 / 4 := by
  constructor
  · exact routeT_elevenFifths_lt_phaseExtraction_integratedTarget.trans htarget
  · exact href.trans routeT_phaseExtraction_reference_lt_upperSeam

/-- The reference cutoff is strictly below the derivative-count transition `mu = 4`.
This uses the positive long-factor deficit; it is stronger than the upper-seam comparison. -/
theorem routeT_phaseExtraction_reference_lt_four :
    routeTPhaseExtractionReferenceMu < (4 : ℝ) := by
  have hd : 0 < maynardLongGlobalAmplitudeDeficit :=
    maynardLongGlobalAmplitudeDeficit_pos
  have hden : 0 < 1 - routeTPhysicalSliceHandoffTheta := by
    linarith [routeTPhysicalSliceHandoffTheta_lt_three_fourths]
  rw [routeTPhaseExtractionReferenceMu]
  apply (div_lt_iff₀ hden).2
  dsimp only [routeTPhysicalSliceHandoffTheta]
  nlinarith

/-- Exact derivative-complement reserve available throughout the phase-extraction window. -/
def routeTPhaseExtractionDerivativeReserve : ℝ :=
  1 - routeTPhaseExtractionReferenceMu / 4

theorem routeT_phaseExtraction_derivativeReserve_pos :
    0 < routeTPhaseExtractionDerivativeReserve := by
  dsimp only [routeTPhaseExtractionDerivativeReserve]
  linarith [routeT_phaseExtraction_reference_lt_four]

/-- In the phase-extraction window, the Route-T large-value band `alpha >= 3/4` stays a fixed
distance below the derivative-count seam.  Thus derivative excision has a genuine reserve even
when the complementary logarithmic mass vanishes. -/
theorem routeT_phaseExtraction_derivativeComplement_margin
    {mu tau alpha s : ℝ}
    (hmu0 : 0 ≤ mu) (hmu : mu < routeTPhaseExtractionReferenceMu)
    (halphaLo : 3 / 4 ≤ alpha) (halphaHi : alpha ≤ 1)
    (htau : tau ≤ mu) (hs : 0 ≤ s) :
    maynardDerivativeComplementHeightExponent tau alpha s ≤
        mu * (1 - alpha) - routeTPhaseExtractionDerivativeReserve ∧
      maynardDerivativeComplementLengthExponent tau alpha ≤
        mu * (1 - alpha) - routeTPhaseExtractionDerivativeReserve := by
  have hdelta0 : 0 ≤ 1 - alpha := by linarith
  have hdeltaHi : 1 - alpha ≤ (1 / 4 : ℝ) := by linarith
  have htauDelta : tau * (1 - alpha) ≤ mu * (1 - alpha) :=
    mul_le_mul_of_nonneg_right htau hdelta0
  have hphase : mu * (1 - alpha) ≤
      1 - routeTPhaseExtractionDerivativeReserve := by
    have hquarter : mu * (1 - alpha) ≤ mu * (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hdeltaHi hmu0
    have hrefQuarter : mu * (1 / 4 : ℝ) <
        routeTPhaseExtractionReferenceMu / 4 := by
      nlinarith
    dsimp only [routeTPhaseExtractionDerivativeReserve]
    linarith
  constructor <;>
    dsimp only [maynardDerivativeComplementHeightExponent,
      maynardDerivativeComplementLengthExponent] <;>
    linarith

/-- The reference-tail boundary lies strictly below the paired-kernel buffer.  Thus phase
extraction cannot by itself cover the final buffered sliver. -/
theorem routeT_phaseExtraction_reference_lt_buffer :
    routeTPhaseExtractionReferenceMu < routeTPairedKernelBufferedMu := by
  have hd : 0 < maynardLongGlobalAmplitudeDeficit :=
    maynardLongGlobalAmplitudeDeficit_pos
  have hdenRef : 0 < 1 - routeTPhysicalSliceHandoffTheta := by
    linarith [routeTPhysicalSliceHandoffTheta_lt_three_fourths]
  have hdenBuffer : 0 < 1 + 3 * maynardLongGlobalAmplitudeDeficit / 2 := by
    positivity
  rw [routeTPhaseExtractionReferenceMu, routeTPairedKernelBufferedMu]
  apply (div_lt_div_iff₀ hdenRef hdenBuffer).2
  dsimp only [routeTPhysicalSliceHandoffTheta]
  nlinarith

/-- Exact width of the upper phase-extraction gap.  This is a genuine positive-width band,
not a logarithmic endpoint artefact. -/
theorem routeT_phaseExtraction_buffer_gap_identity :
    routeTPairedKernelBufferedMu - routeTPhaseExtractionReferenceMu =
      (2 * maynardLongGlobalAmplitudeDeficit) /
        ((1 + 3 * maynardLongGlobalAmplitudeDeficit / 2) *
          (1 + 2 * maynardLongGlobalAmplitudeDeficit)) := by
  have hd : 0 < maynardLongGlobalAmplitudeDeficit :=
    maynardLongGlobalAmplitudeDeficit_pos
  have hrefDen : 1 + 2 * maynardLongGlobalAmplitudeDeficit ≠ 0 := by
    nlinarith
  have hbufferDen : 1 + 3 * maynardLongGlobalAmplitudeDeficit / 2 ≠ 0 := by
    nlinarith
  have href : routeTPhaseExtractionReferenceMu =
      4 / (1 + 2 * maynardLongGlobalAmplitudeDeficit) := by
    rw [routeTPhaseExtractionReferenceMu]
    have hrewrite :
        1 - routeTPhysicalSliceHandoffTheta =
          (1 + 2 * maynardLongGlobalAmplitudeDeficit) / 4 := by
      rw [routeTPhysicalSliceHandoffTheta]
      ring
    rw [hrewrite]
    field_simp [hrefDen]
  rw [routeTPairedKernelBufferedMu, href]
  field_simp [hrefDen, hbufferDen]
  ring

/-- On a positive ordinate shell, replacing the narrow target kernel by its point-mass phase
costs only the sharp local Mellin error.  Unlike the central-band estimate, this keeps the
actual shell length `|V - U|`; it is the analytic term needed to preserve common-mode
cancellation until phase extraction. -/
theorem norm_intervalIntegral_fixedSource_targetPointMassError_le
    (a : ℝ → ℂ) {P N W U V : ℝ}
    (hP : 0 ≤ P) (haBound : ∀ y, ‖a y‖ ≤ P)
    (hN : 0 < N) (hW : 0 < W) (hU : 0 ≤ U) (hUV : U ≤ V)
    (hsmall : V * (2 * W / N) ≤ 1) :
    ‖∫ y in U..V,
      a y * (routeTNormalizedSmoothWindowMellin N W
        ((1 : ℂ) + (y : ℝ) * Complex.I) -
        (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1))‖ ≤
      (4 * P * V * (W / N)) * |V - U| := by
  have hpoint : ∀ y ∈ Set.uIoc U V,
      ‖a y *
        (routeTNormalizedSmoothWindowMellin N W
            ((1 : ℂ) + (y : ℝ) * Complex.I) -
          (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1))‖ ≤
        4 * P * V * (W / N) := by
    intro y hy
    rw [Set.uIoc_of_le hUV] at hy
    have hV : 0 ≤ V := hU.trans hUV
    have hyabs : |y| ≤ V := abs_le.mpr ⟨by nlinarith [hy.1], hy.2⟩
    let s : ℂ := (1 : ℂ) + (y : ℝ) * Complex.I
    have hsre : 0 < s.re := by simp [s]
    have hsnorm : ‖s - 1‖ = |y| := by
      dsimp only [s]
      simp [Real.norm_eq_abs]
    have hsmallY : ‖s - 1‖ * (2 * W / N) ≤ 1 := by
      rw [hsnorm]
      exact (mul_le_mul_of_nonneg_right hyabs (by positivity)).trans hsmall
    have hk := norm_routeTNormalizedSmoothWindowMellin_sub_pointMass_le
      hN hW hsre hsmallY
    have hNpow : N ^ (s.re - 1) = 1 := by simp [s]
    norm_num [hNpow, hsnorm] at hk
    rw [norm_mul]
    calc
      ‖a y‖ *
          ‖routeTNormalizedSmoothWindowMellin N W
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1)‖ ≤
          P * (4 * |y| * (W / N)) :=
        mul_le_mul (haBound y) (by simpa only [s] using hk)
          (norm_nonneg _) hP
      _ ≤ P * (4 * V * (W / N)) := by
        gcongr
      _ = 4 * P * V * (W / N) := by ring
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (a := U) (b := V) (C := 4 * P * V * (W / N)) hpoint

/-- A positive shell is contained in its symmetric far tail.  This transports an arbitrary-order
tail bound, naturally stated on `|y| ≥ U`, to the particular shell whose paired lower bound was
selected. -/
theorem norm_intervalIntegral_le_integral_norm_centralTail
    {f : ℝ → ℂ} {U V : ℝ} (hf : Integrable f)
    (hU : 0 ≤ U) (hUV : U ≤ V) :
    ‖∫ y in U..V, f y‖ ≤
      ∫ y in {y : ℝ | U ≤ |y|}, ‖f y‖ := by
  let tail : Set ℝ := {y : ℝ | U ≤ |y|}
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hUV
    (Filter.Eventually.of_forall fun y _hy => le_rfl)
    hf.norm.intervalIntegrable
  have hsubset : Set.Ioc U V ⊆ tail := by
    intro y hy
    have hy0 : 0 ≤ y := hU.trans (le_of_lt hy.1)
    change U ≤ |y|
    rw [abs_of_nonneg hy0]
    exact le_of_lt hy.1
  have hmono : (∫ y in Set.Ioc U V, ‖f y‖) ≤
      ∫ y in tail, ‖f y‖ := by
    apply MeasureTheory.setIntegral_mono_set hf.norm.integrableOn
      (Filter.Eventually.of_forall fun y => norm_nonneg _)
      (Filter.Eventually.of_forall fun y hy => hsubset hy)
  calc
    ‖∫ y in U..V, f y‖ ≤ ∫ y in U..V, ‖f y‖ := hnorm
    _ = ∫ y in Set.Ioc U V, ‖f y‖ := intervalIntegral.integral_of_le hUV
    _ ≤ ∫ y in tail, ‖f y‖ := hmono
    _ = _ := by rfl

/-- **Phase-extraction transfer.** A large paired shell forces a large point-mass phase
integral after subtracting the independently controlled wide-reference and narrow-target errors.
This is where linear common-mode cancellation is retained; no positive Gram step is taken. -/
theorem norm_intervalIntegral_fixedSource_pointMass_ge_of_paired
    (a : ℝ → ℂ) {N H R U V B ER EH : ℝ}
    (ha : Continuous a) (hN : 0 < N) (hH : 0 < H) (hR : 0 < R)
    (hpaired : B ≤ ‖∫ y in U..V,
      a y * (routeTNormalizedSmoothWindowMellin N R
        ((1 : ℂ) + (y : ℝ) * Complex.I) -
        routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + (y : ℝ) * Complex.I))‖)
    (href : ‖∫ y in U..V,
      a y * routeTNormalizedSmoothWindowMellin N R
        ((1 : ℂ) + (y : ℝ) * Complex.I)‖ ≤ ER)
    (htarget : ‖∫ y in U..V,
      a y * (routeTNormalizedSmoothWindowMellin N H
        ((1 : ℂ) + (y : ℝ) * Complex.I) -
        (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1))‖ ≤ EH) :
    B - ER - EH ≤ ‖∫ y in U..V,
      a y * (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1)‖ := by
  let fR : ℝ → ℂ := fun y =>
    a y * routeTNormalizedSmoothWindowMellin N R
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let fH : ℝ → ℂ := fun y =>
    a y * routeTNormalizedSmoothWindowMellin N H
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let fP : ℝ → ℂ := fun y =>
    a y * (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1)
  let e : ℝ → ℂ := fun y =>
    a y * (routeTNormalizedSmoothWindowMellin N H
      ((1 : ℂ) + (y : ℝ) * Complex.I) -
      (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1))
  have hfR : Continuous fR := by
    apply ha.mul
    exact continuous_routeTNormalizedSmoothWindowMellin_line hN hR (by norm_num)
  have hfH : Continuous fH := by
    apply ha.mul
    exact continuous_routeTNormalizedSmoothWindowMellin_line hN hH (by norm_num)
  have hfP : Continuous fP := by
    apply ha.mul
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl (by exact_mod_cast hN.ne')
  have he : Continuous e := by
    apply ha.mul
    exact (continuous_routeTNormalizedSmoothWindowMellin_line hN hH (by norm_num)).sub
      (by
        apply Continuous.const_cpow
        · fun_prop
        · exact Or.inl (by exact_mod_cast hN.ne'))
  have hdecomp :
      (∫ y in U..V,
        a y * (routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * Complex.I))) =
        (∫ y in U..V, fR y) - (∫ y in U..V, fP y) - (∫ y in U..V, e y) := by
    calc
      (∫ y in U..V,
        a y * (routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * Complex.I))) =
          ∫ y in U..V, (fR y - fP y) - e y := by
            apply intervalIntegral.integral_congr
            intro y _hy
            dsimp only [fR, fH, fP, e]
            ring
      _ = (∫ y in U..V, fR y - fP y) - ∫ y in U..V, e y :=
        intervalIntegral.integral_sub ((hfR.sub hfP).intervalIntegrable U V)
          (he.intervalIntegrable U V)
      _ = (∫ y in U..V, fR y) - (∫ y in U..V, fP y) - (∫ y in U..V, e y) := by
        rw [intervalIntegral.integral_sub (hfR.intervalIntegrable U V)
          (hfP.intervalIntegrable U V)]
  have hbound :
      ‖∫ y in U..V,
        a y * (routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * Complex.I))‖ ≤
        ER + ‖∫ y in U..V, fP y‖ + EH := by
    have hfirst :
        ‖(∫ y in U..V, fR y) - ∫ y in U..V, fP y‖ ≤
          ER + ‖∫ y in U..V, fP y‖ := by
      calc
        ‖(∫ y in U..V, fR y) - ∫ y in U..V, fP y‖ ≤
            ‖∫ y in U..V, fR y‖ + ‖∫ y in U..V, fP y‖ := norm_sub_le _ _
        _ ≤ ER + ‖∫ y in U..V, fP y‖ := by
          exact add_le_add (by simpa only [fR] using href) le_rfl
    have heBound : ‖∫ y in U..V, e y‖ ≤ EH := by
      simpa only [e] using htarget
    rw [hdecomp]
    calc
      ‖(∫ y in U..V, fR y) - (∫ y in U..V, fP y) - ∫ y in U..V, e y‖ ≤
          ‖(∫ y in U..V, fR y) - ∫ y in U..V, fP y‖ +
            ‖∫ y in U..V, e y‖ := norm_sub_le _ _
      _ ≤ (ER + ‖∫ y in U..V, fP y‖) + EH :=
        add_le_add hfirst heBound
      _ = ER + ‖∫ y in U..V, fP y‖ + EH := by ring
  have h := hpaired.trans hbound
  dsimp only [fP] at h ⊢
  linarith

/-- A wide reference can be removed from a fixed-source shell without replacing it by the
narrow target.  This is strictly stronger than the paired-tail estimate in the non-comparable
regime: its decay scale is `N / R`, which is precisely the scale that creates the phase-extraction
window below `routeTPhaseExtractionReferenceMu`. -/
theorem exists_integral_norm_fixedSource_mul_oneKernel_natOrder_tail_le
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ Cj : ℝ, 1 ≤ Cj ∧
      ∀ (L X k : ℕ) (T0 t : ℝ) {M N R U : ℝ},
        1 ≤ X → 0 < M → 1 ≤ N → 0 < R → R ≤ N → 0 < U →
        ∫ y in {y : ℝ | U ≤ |y|},
          ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
                ((1 : ℂ) + (y : ℝ) * Complex.I) *
            routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * Complex.I)‖ ≤
          heathBrownWindowRelevantFixedPolylogBound L X k M 1 *
            (Cj * (N / R) ^ (j + 1) * U ^ (-(j : ℝ))) := by
  obtain ⟨Cj, hCj, htail⟩ :=
    exists_integral_routeTNormalizedSmoothWindowMellin_one_natOrder_tail_le j hj
  refine ⟨Cj, hCj, ?_⟩
  intro L X k T0 t M N R U hX hM hN hR hRN hU
  let A : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let KR : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N R
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X k M 1
  let tail : Set ℝ := {y : ℝ | U ≤ |y|}
  have hA : ∀ y : ℝ, ‖A y‖ ≤ P := by
    intro y
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T0 t M 1 y hM (by norm_num)
  have hP : 0 ≤ P := (norm_nonneg (A 0)).trans (hA 0)
  have hKRint := integrable_routeTNormalizedSmoothWindowMellin_one
    (zero_lt_one.trans_le hN) hR
  have hAcont : Continuous A :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k T0 t M 1
  have hprod : Integrable (fun y => ‖A y * KR y‖) := by
    exact (hKRint.bdd_mul hAcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hA)).norm
  have hmajor : Integrable (fun y => P * ‖KR y‖) :=
    hKRint.norm.const_mul P
  have hmono : (∫ y in tail, ‖A y * KR y‖) ≤
      ∫ y in tail, P * ‖KR y‖ := by
    apply setIntegral_mono_on hprod.integrableOn hmajor.integrableOn
      (measurableSet_le measurable_const continuous_abs.measurable)
    intro y _hy
    rw [norm_mul]
    exact mul_le_mul (hA y) le_rfl (norm_nonneg _) hP
  have hscale : (∫ y in tail, P * ‖KR y‖) =
      P * (∫ y in tail, ‖KR y‖) := by
    rw [MeasureTheory.integral_const_mul]
  have htailR := htail N R U hN hR hRN hU
  calc
    (∫ y in {y : ℝ | U ≤ |y|}, ‖A y * KR y‖) ≤
        ∫ y in tail, P * ‖KR y‖ := hmono
    _ = P * (∫ y in tail, ‖KR y‖) := hscale
    _ ≤ P * (Cj * (N / R) ^ (j + 1) * U ^ (-(j : ℝ))) := by
      gcongr
    _ = _ := by rfl

/-- **Cancellation-preserving phase extraction on one positive shell.**  A paired common-mode
lower bound transfers to the point-mass phase after paying exactly two errors: the reference
tail at its own wide scale `R`, and the narrow target-to-phase error at scale `H/N`.
The theorem is unconditional; it does not assert the missing large-value receiver, but it
reduces the transition shell to the literal phase-modulated Heath--Brown aggregate. -/
theorem exists_fixedSource_pointMassPhase_lower_of_pairedShell
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ Cj : ℝ, 1 ≤ Cj ∧
      ∀ (L X k : ℕ) (T0 t : ℝ) {M N H R U V B : ℝ},
        1 ≤ X → 0 < M → 1 ≤ N → 0 < H → 0 < R → R ≤ N →
        0 < U → U ≤ V →
        V * (2 * H / N) ≤ 1 →
        B ≤ ‖∫ y in U..V,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
                ((1 : ℂ) + (y : ℝ) * Complex.I) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * Complex.I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * Complex.I))‖ →
        B - heathBrownWindowRelevantFixedPolylogBound L X k M 1 *
              (Cj * (N / R) ^ (j + 1) * U ^ (-(j : ℝ))) -
            (4 * heathBrownWindowRelevantFixedPolylogBound L X k M 1 * V * (H / N)) *
              |V - U| ≤
          ‖∫ y in U..V,
            heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
                  ((1 : ℂ) + (y : ℝ) * Complex.I) *
              (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1)‖ := by
  obtain ⟨Cj, hCj, htail⟩ :=
    exists_integral_norm_fixedSource_mul_oneKernel_natOrder_tail_le j hj
  refine ⟨Cj, hCj, ?_⟩
  intro L X k T0 t M N H R U V B hX hM hN hH hR hRN hU hUV hsmall hpaired
  let A : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let KR : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N R
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X k M 1
  have hA : ∀ y : ℝ, ‖A y‖ ≤ P := by
    intro y
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T0 t M 1 y hM (by norm_num)
  have hP : 0 ≤ P := (norm_nonneg (A 0)).trans (hA 0)
  have hAcont : Continuous A :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k T0 t M 1
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hKRint := integrable_routeTNormalizedSmoothWindowMellin_one
    hN0 hR
  have hprod : Integrable (fun y => A y * KR y) := by
    exact hKRint.bdd_mul hAcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hA)
  have hrefTail := htail L X k T0 t hX hM hN hR hRN hU
  have href : ‖∫ y in U..V, A y * KR y‖ ≤
      P * (Cj * (N / R) ^ (j + 1) * U ^ (-(j : ℝ))) := by
    calc
      ‖∫ y in U..V, A y * KR y‖ ≤
          ∫ y in {y : ℝ | U ≤ |y|}, ‖A y * KR y‖ :=
        norm_intervalIntegral_le_integral_norm_centralTail hprod hU.le hUV
      _ ≤ P * (Cj * (N / R) ^ (j + 1) * U ^ (-(j : ℝ))) := by
        simpa only [A, KR, P] using hrefTail
  have htarget : ‖∫ y in U..V,
      A y * (routeTNormalizedSmoothWindowMellin N H
        ((1 : ℂ) + (y : ℝ) * Complex.I) -
        (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1))‖ ≤
      (4 * P * V * (H / N)) * |V - U| :=
    norm_intervalIntegral_fixedSource_targetPointMassError_le
      A hP hA hN0 hH hU.le hUV hsmall
  have htransfer := norm_intervalIntegral_fixedSource_pointMass_ge_of_paired
    A hAcont hN0 hH hR (by simpa only [A] using hpaired) href htarget
  simpa only [A, P] using htransfer

end
end RHTower.Sieve
