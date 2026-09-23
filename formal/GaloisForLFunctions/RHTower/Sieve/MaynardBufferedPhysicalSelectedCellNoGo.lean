import GaloisForLFunctions.RHTower.Sieve.MaynardPairedKernelBufferedHandoff

/-!
# Buffered physical/selected-cell interface obstruction

The paired common-mode Route-T shell has two existing receivers. Below the buffered exponent,
arbitrary-order physical localization needs `1 < mu * (1 - alpha)`. Every available arithmetic
selected-cell receiver starts at the transition threshold `(1 + routeTGapMomentNu) / 2`.

These regions do not meet. The exact gap is a positive rational function of the fixed global
amplitude deficit. Thus a low-shell weld cannot be obtained by merely composing current theorems:
it requires a genuinely new reciprocal paired bad-set estimate below the transition threshold, or a
new localization whose phase condition is different.
-/

namespace RHTower.Sieve

/-- Exact power reserve separating the buffered physical phase from the weakest existing
selected-cell threshold. -/
theorem routeT_buffered_selectedCell_phase_deficit :
    1 - routeTPairedKernelBufferedMu *
        (1 - (1 + routeTGapMomentNu) / 2) =
      maynardLongGlobalAmplitudeDeficit /
        (2 + 3 * maynardLongGlobalAmplitudeDeficit) := by
  have hd : 0 < maynardLongGlobalAmplitudeDeficit :=
    maynardLongGlobalAmplitudeDeficit_pos
  rw [routeTPairedKernelBufferedMu, routeTGapMomentNu]
  field_simp
  ring

/-- No exponent in the buffered physical range can simultaneously enter the existing
selected-cell transition range and retain the strict physical localization phase. -/
theorem not_exists_routeT_buffered_physical_selectedCell_phase :
    ¬ ∃ mu alpha : ℝ,
      0 < mu ∧
      mu ≤ routeTPairedKernelBufferedMu ∧
      (1 + routeTGapMomentNu) / 2 ≤ alpha ∧
      1 < mu * (1 - alpha) := by
  rintro ⟨mu, alpha, hmu0, hmub, halpha, hphase⟩
  have hd : 0 < maynardLongGlobalAmplitudeDeficit :=
    maynardLongGlobalAmplitudeDeficit_pos
  have hden : 0 < 1 + 3 * maynardLongGlobalAmplitudeDeficit / 2 := by
    positivity
  have hbuffer0 : 0 < routeTPairedKernelBufferedMu := by
    rw [routeTPairedKernelBufferedMu]
    positivity
  have hfactor0 : 0 ≤ 1 - alpha := by
    by_contra h
    have hneg : 1 - alpha < 0 := lt_of_not_ge h
    have hprod : mu * (1 - alpha) < 0 := mul_neg_of_pos_of_neg hmu0 hneg
    linarith
  have hmufactor : mu * (1 - alpha) ≤
      routeTPairedKernelBufferedMu * (1 - alpha) :=
    mul_le_mul_of_nonneg_right hmub hfactor0
  have halphaFactor : 1 - alpha ≤ 1 - (1 + routeTGapMomentNu) / 2 := by
    linarith
  have hbufferFactor :
      routeTPairedKernelBufferedMu * (1 - alpha) ≤
        routeTPairedKernelBufferedMu * (1 - (1 + routeTGapMomentNu) / 2) :=
    mul_le_mul_of_nonneg_left halphaFactor hbuffer0.le
  have hcritical :
      routeTPairedKernelBufferedMu *
          (1 - (1 + routeTGapMomentNu) / 2) < 1 := by
    rw [routeTPairedKernelBufferedMu, routeTGapMomentNu]
    field_simp [hden.ne']
    nlinarith
  linarith

/-- Positive survivor of the obstruction: every genuine buffered physical-phase weld must use
an amplitude strictly below the current selected-cell transition threshold. -/
theorem routeT_buffered_physical_phase_alpha_lt_selectedCell_threshold
    {mu alpha : ℝ} (hmu0 : 0 < mu)
    (hmub : mu ≤ routeTPairedKernelBufferedMu)
    (hphase : 1 < mu * (1 - alpha)) :
    alpha < (1 + routeTGapMomentNu) / 2 := by
  by_contra h
  exact not_exists_routeT_buffered_physical_selectedCell_phase
    ⟨mu, alpha, hmu0, hmub, le_of_not_gt h, hphase⟩

/-- The unpolarized Guth--Maynard cubic middle term is incompatible with *every* physical
Route-T phase, not merely the buffered witness below.  After cancellation against the desired
second receiver exponent, its excess is
`mu * (3 / 5 - routeTGapMomentNu) + 2 * mu * (1 - alpha) - 1`.
Both summands are strictly positive in the physical phase.  Thus any viable cubic-trace weld
must be polarised before the ordinary large-value count. -/
theorem routeT_guthMaynard_middleTerm_fails_physicalPhase
    {mu alpha : ℝ} (hmu : 0 < mu) (hphase : 1 < mu * (1 - alpha)) :
    1 + mu * (1 + routeTGapMomentNu - 2 * alpha) <
      mu * (18 / 5 - 4 * alpha) := by
  have hnu : routeTGapMomentNu < 3 / 5 :=
    routeTGapMomentNu_lt_half.trans (by norm_num)
  have hgap : 0 < 3 / 5 - routeTGapMomentNu := sub_pos.mpr hnu
  have hpositive : 0 < mu * (3 / 5 - routeTGapMomentNu) :=
    mul_pos hmu hgap
  nlinarith

/-- The unpolarized Guth--Maynard middle term cannot directly supply the missing paired
low-shell receiver.  At this explicit buffered physical-phase point, its exponent
`mu * (18 / 5 - 4 * alpha)` is strictly larger than Route T's required second-alternative
exponent.  Thus a viable import of cubic-trace technology must retain paired cancellation
*before* the ordinary large-value count, rather than applying its three-term bound verbatim. -/
theorem routeT_buffered_guthMaynard_middleTerm_direct_noGo :
    let mu : ℝ := 19 / 5
    let alpha : ℝ := 18 / 25
    mu ≤ routeTPairedKernelBufferedMu ∧
      1 < mu * (1 - alpha) ∧
      1 + mu * (1 + routeTGapMomentNu - 2 * alpha) <
        mu * (18 / 5 - 4 * alpha) := by
  dsimp only
  have hdsmall : maynardLongGlobalAmplitudeDeficit < (1 / 100 : ℝ) := by
    dsimp only [maynardLongGlobalAmplitudeDeficit, maynardDerivativeDeficit]
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (47 : ℕ) := one_le_pow₀ (by norm_num)
    nlinarith
  have hdpos : 0 < maynardLongGlobalAmplitudeDeficit :=
    maynardLongGlobalAmplitudeDeficit_pos
  have hden : 0 < 1 + 3 * maynardLongGlobalAmplitudeDeficit / 2 := by
    nlinarith
  constructor
  · rw [routeTPairedKernelBufferedMu]
    apply (le_div_iff₀ hden).2
    nlinarith
  constructor
  · norm_num
  · have hnu : routeTGapMomentNu < 1 / 2 := routeTGapMomentNu_lt_half
    nlinarith

end RHTower.Sieve
