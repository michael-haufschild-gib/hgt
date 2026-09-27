import GaloisForLFunctions.RHTower.CCMCoherentMidpointGauge

/-!
# Exact removal of midpoint-even energy from the actual Weil source

The complete coherent Gamma cost and phase square contain the same
midpoint-even energy. This module proves integrability and cancels that
energy from the actual source identity. The remaining phase gap is still
signed; the nonnegativity of an individual square does not settle it.
-/

noncomputable section
open Complex MeasureTheory Filter
open scoped InnerProduct BigOperators

namespace RHTower

def ccmActualHeadMidpointOddGammaCost (T : ℝ) (N : ℕ) (f : SoninL2) : ℝ :=
  ∫ r : ℝ, ‖ccmActualHeadMidpointOddField T N f r‖ ^ 2 * ccmGammaHigherBinetDualDensity |r|

def ccmActualHeadMidpointEvenGammaCost (T : ℝ) (N : ℕ) (f : SoninL2) : ℝ :=
  ∫ r : ℝ, ‖ccmActualHeadMidpointEvenField T N f r‖ ^ 2 * ccmGammaHigherBinetDualDensity |r|

def ccmActualHeadMidpointOddGammaSquare (T : ℝ) (N : ℕ) (f : SoninL2) : ℝ :=
  ∫ r : ℝ,
    ‖(Real.sqrt (ccmGammaHigherBinetModeDensity |r|) : ℂ) • (logTranslationCLM r f - f) +
      (Real.sqrt (ccmGammaHigherBinetDualDensity |r|) : ℂ) • ccmActualHeadMidpointOddField T N f r‖ ^ 2

private theorem dual_measurable :
    AEStronglyMeasurable (fun r : ℝ => ccmGammaHigherBinetDualDensity |r|) := by
  apply Continuous.aestronglyMeasurable
  unfold ccmGammaHigherBinetDualDensity
  fun_prop

private theorem odd_measurable (T : ℝ) (N : ℕ) (f : SoninL2) :
    AEStronglyMeasurable (ccmActualHeadMidpointOddField T N f) := by
  unfold ccmActualHeadMidpointOddField
  have hc : AEStronglyMeasurable (fun _ : ℝ => ((1 / 2 : ℝ) : ℂ)) := aestronglyMeasurable_const
  exact hc.smul
    ((aestronglyMeasurable_ccmActualHeadQuantileCompletedCoherentField T N f).sub
      (aestronglyMeasurable_ccmActualHeadReflectedCoherentField T N f))

private theorem even_measurable (T : ℝ) (N : ℕ) (f : SoninL2) :
    AEStronglyMeasurable (ccmActualHeadMidpointEvenField T N f) := by
  unfold ccmActualHeadMidpointEvenField
  have hc : AEStronglyMeasurable (fun _ : ℝ => ((1 / 2 : ℝ) : ℂ)) := aestronglyMeasurable_const
  exact hc.smul
    ((aestronglyMeasurable_ccmActualHeadQuantileCompletedCoherentField T N f).add
      (aestronglyMeasurable_ccmActualHeadReflectedCoherentField T N f))

theorem integrable_ccmActualHeadMidpointOddGammaDensity (T : ℝ) (N : ℕ) (f : SoninL2) :
    Integrable (fun r : ℝ =>
      ‖ccmActualHeadMidpointOddField T N f r‖ ^ 2 * ccmGammaHigherBinetDualDensity |r|) := by
  refine (integrable_ccmActualHeadCoherentQuantileGammaChiSquareDensity T N f).mono'
    (((odd_measurable T N f).norm.pow 2).mul dual_measurable) ?_
  filter_upwards with r
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)))]
  exact mul_le_mul_of_nonneg_right (norm_sq_ccmActualHeadMidpointOddField_le T N f r)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))

theorem integrable_ccmActualHeadMidpointEvenGammaDensity (T : ℝ) (N : ℕ) (f : SoninL2) :
    Integrable (fun r : ℝ =>
      ‖ccmActualHeadMidpointEvenField T N f r‖ ^ 2 * ccmGammaHigherBinetDualDensity |r|) := by
  refine (integrable_ccmActualHeadCoherentQuantileGammaChiSquareDensity T N f).mono'
    (((even_measurable T N f).norm.pow 2).mul dual_measurable) ?_
  filter_upwards with r
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)))]
  apply mul_le_mul_of_nonneg_right _ (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))
  rw [norm_sq_ccmActualHeadCoherentField_midpoint_split]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem ccmActualHeadMidpointOddGammaCost_nonneg (T : ℝ) (N : ℕ) (f : SoninL2) :
    0 ≤ ccmActualHeadMidpointOddGammaCost T N f :=
  integral_nonneg fun r => mul_nonneg (sq_nonneg _)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))

theorem ccmActualHeadMidpointEvenGammaCost_nonneg (T : ℝ) (N : ℕ) (f : SoninL2) :
    0 ≤ ccmActualHeadMidpointEvenGammaCost T N f :=
  integral_nonneg fun r => mul_nonneg (sq_nonneg _)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))

/-- The coherent cost splits with no cross-prime or terminal term omitted. -/
theorem ccmActualHeadCoherentGammaCost_midpoint_split (T : ℝ) (N : ℕ) (f : SoninL2) :
    ccmActualHeadCoherentQuantileGammaChiSquare T N f =
      ccmActualHeadMidpointOddGammaCost T N f + ccmActualHeadMidpointEvenGammaCost T N f := by
  unfold ccmActualHeadCoherentQuantileGammaChiSquare
    ccmActualHeadMidpointOddGammaCost ccmActualHeadMidpointEvenGammaCost
  rw [← integral_add (integrable_ccmActualHeadMidpointOddGammaDensity T N f)
    (integrable_ccmActualHeadMidpointEvenGammaDensity T N f)]
  apply integral_congr_ae
  filter_upwards with r
  rw [norm_sq_ccmActualHeadCoherentField_midpoint_split, add_mul]

theorem ccmActualHeadMidpointOddGammaCost_le_full (T : ℝ) (N : ℕ) (f : SoninL2) :
    ccmActualHeadMidpointOddGammaCost T N f ≤ ccmActualHeadCoherentQuantileGammaChiSquare T N f := by
  rw [ccmActualHeadCoherentGammaCost_midpoint_split]
  exact le_add_of_nonneg_right (ccmActualHeadMidpointEvenGammaCost_nonneg T N f)

theorem integrable_ccmActualHeadMidpointGaugeAction (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (N : ℕ) (θ : ℝ) :
    Integrable (fun r => ccmActualHeadMidpointGaugeAction (2*a.1) N
      (ccmArchimedeanFormToAperture a u).1 r θ) := by
  simp_rw [ccmActualHeadMidpointGaugeAction_eq_actual_terms]
  exact (integrable_ccmGammaHigherBinetSymmetricEnergy_formDomain a u).add
    ((integrable_ccmActualHeadCompletedCoherentInnerField (2*a.1) N
      (ccmArchimedeanFormToAperture a u).1).const_mul 2)

/-- Integrated action conservation, including the literal completed current. -/
theorem integral_ccmActualHeadMidpointGaugeAction (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (θ : ℝ) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2*a.1)) + 1
    (∫ r : ℝ, ccmActualHeadMidpointGaugeAction (2*a.1) N f.1 r θ) =
      2 * ccmActualHeadGammaHigherBinetModeEnergy f.1 +
        2 * ccmActualHeadCompletedQuantileCurrent a f := by
  dsimp only
  simp_rw [ccmActualHeadMidpointGaugeAction_eq_actual_terms]
  rw [integral_add (integrable_ccmGammaHigherBinetSymmetricEnergy_formDomain a u)
    ((integrable_ccmActualHeadCompletedCoherentInnerField _ _ _).const_mul 2),
    integral_const_mul, integral_ccmGammaHigherBinetSymmetricEnergy_formDomain a u,
    ← ccmActualHeadCompletedQuantileCurrent_eq_integral_coherentField]
  rfl

/-- The continuous gauge orbit represents precisely the original Weil source. -/
theorem ccmRestrictedWeilSourceQuadratic_eq_midpointGaugeAction
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) (θ : ℝ) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2*a.1)) + 1
    ccmRestrictedWeilSourceQuadratic a u =
      (2 * gammaHardyPhaseRate 0 + 4) * ‖f‖ ^ 2 - ccmActualHeadGammaHigherBinetModeEnergy f.1 +
        ∫ r : ℝ, ccmActualHeadMidpointGaugeAction (2*a.1) N f.1 r θ := by
  have hsource := ccmRestrictedWeilSourceQuadratic_eq_coherentQuantileGammaPhaseSquare_normalForm a u
  have hphase := ccmActualHeadCoherentQuantileGammaPhaseSquare_eq_actual_terms a u
  have haction := integral_ccmActualHeadMidpointGaugeAction a u θ
  dsimp only at hsource hphase haction ⊢
  linarith only [hsource, hphase, haction]

private theorem odd_square_integrand (T : ℝ) (N : ℕ) (f : SoninL2) (r : ℝ) :
    ‖(Real.sqrt (ccmGammaHigherBinetModeDensity |r|) : ℂ) • (logTranslationCLM r f - f) +
      (Real.sqrt (ccmGammaHigherBinetDualDensity |r|) : ℂ) • ccmActualHeadMidpointOddField T N f r‖ ^ 2 =
      ccmActualHeadMidpointGaugeAction T N f r 0 +
        ‖ccmActualHeadMidpointOddField T N f r‖ ^ 2 * ccmGammaHigherBinetDualDensity |r| := by
  rw [ccmActualHeadMidpointGaugeAction, ccmActualHeadMidpointGaugeField_zero]
  ring

theorem ccmActualHeadMidpointOddGammaSquare_eq_actual_terms
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2*a.1)) + 1
    ccmActualHeadMidpointOddGammaSquare (2*a.1) N f.1 =
      2 * ccmActualHeadGammaHigherBinetModeEnergy f.1 +
        2 * ccmActualHeadCompletedQuantileCurrent a f +
          ccmActualHeadMidpointOddGammaCost (2*a.1) N f.1 := by
  dsimp only
  unfold ccmActualHeadMidpointOddGammaSquare
  simp_rw [odd_square_integrand]
  rw [integral_add (integrable_ccmActualHeadMidpointGaugeAction a u _ 0)
    (integrable_ccmActualHeadMidpointOddGammaDensity _ _ _),
    integral_ccmActualHeadMidpointGaugeAction]
  rfl

/-- The same even energy occurs in both the full phase square and its cost. -/
theorem ccmActualHeadCoherentGammaPhaseSquare_midpoint_split
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2*a.1)) + 1
    ccmActualHeadCoherentQuantileGammaPhaseSquare (2*a.1) N f.1 =
      ccmActualHeadMidpointOddGammaSquare (2*a.1) N f.1 +
        ccmActualHeadMidpointEvenGammaCost (2*a.1) N f.1 := by
  have hfull := ccmActualHeadCoherentQuantileGammaPhaseSquare_eq_actual_terms a u
  have hodd := ccmActualHeadMidpointOddGammaSquare_eq_actual_terms a u
  have hcost := ccmActualHeadCoherentGammaCost_midpoint_split (2*a.1)
    (Nat.floor (Real.exp (2*a.1)) + 1) (ccmArchimedeanFormToAperture a u).1
  dsimp only at hfull hodd ⊢
  linarith only [hfull, hodd, hcost]

/-- Exact cancellation removes the entire midpoint-even channel from the source. -/
theorem ccmRestrictedWeilSourceQuadratic_eq_midpointOdd_normalForm
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2*a.1)) + 1
    ccmRestrictedWeilSourceQuadratic a u =
      (2 * gammaHardyPhaseRate 0 + 4) * ‖f‖ ^ 2 +
        ccmActualHeadMidpointOddGammaSquare (2*a.1) N f.1 -
          ccmActualHeadGammaHigherBinetModeEnergy f.1 -
          ccmActualHeadMidpointOddGammaCost (2*a.1) N f.1 := by
  have hsource := ccmRestrictedWeilSourceQuadratic_eq_coherentQuantileGammaPhaseSquare_normalForm a u
  have hphase := ccmActualHeadCoherentGammaPhaseSquare_midpoint_split a u
  have hcost := ccmActualHeadCoherentGammaCost_midpoint_split (2*a.1)
    (Nat.floor (Real.exp (2*a.1)) + 1) (ccmArchimedeanFormToAperture a u).1
  dsimp only at hsource hphase ⊢
  linarith only [hsource, hphase, hcost]

end RHTower
