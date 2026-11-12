import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CriticalPowerCombGrowthDetectsRH
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ContactSymbolsContinueAcrossZeros
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.LogarithmicAbelIntegrability

/-!
# Absolute critical-comb integrability pays the literal contact transform

Harmonic subtraction and the convergent elementary remainder preserve
absolute logarithmic Abel integrability. The resulting contact integral
is holomorphic on the right half-plane and carries the actual critical
Dirichlet symbol. The initial series uses only the unconditional outer
zero bound, not RH or ordinary comb convergence.
-/

noncomputable section

open Complex Finset Filter Topology Set

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity TransHorizonIncidenceMechanics

/-- Absolute critical-comb integrability pays the centered contacts. -/
theorem logarithmicAbelIntegrable_criticalHarmonicContacts
    (hc : LogarithmicAbelIntegrable (powerCombTail (1 / 2))) :
    LogarithmicAbelIntegrable criticalHarmonicContacts := by
  have hE := logarithmicAbelIntegrable_of_strictGrowth
    (strictPowerGrowth_zero_of_tendsto tendsto_criticalPowerCombElementaryRemainder)
  apply ((hE.sub hc).const_mul (1 / 2)).congr_pos
  intro N hN
  rw [powerCombTail_half_eq_elementary_sub_contacts hN]
  ring

/-- Restoring the harmonic term preserves absolute integrability at
every positive logarithmic damping. -/
theorem logarithmicAbelIntegrable_criticalPowerContactPrefix
    (hc : LogarithmicAbelIntegrable (powerCombTail (1 / 2))) :
    LogarithmicAbelIntegrable (powerContactPrefix (1 / 2)) := by
  have hg := logarithmicAbelIntegrable_criticalHarmonicContacts hc
  have hh := logarithmicAbelIntegrable_of_strictGrowth strictGrowth_harm
  apply (hg.sub (hh.const_mul (-criticalPowerContactCoefficient))).congr_pos
  intro N _
  rw [criticalHarmonicContacts]
  ring

/-- Absolute critical-comb integrability gives holomorphy of its literal
contact integral throughout the open right half-plane. -/
theorem differentiableOn_criticalContactIntegral_of_abelIntegrable
    (hc : LogarithmicAbelIntegrable (powerCombTail (1 / 2))) :
    DifferentiableOn ℂ (oneSidedStepMellin (powerContactPrefix (1 / 2)))
      {s : ℂ | 0 < s.re} := by
  apply differentiableOn_oneSidedStepMellin_of_normalized_abel (le_refl (0 : ℝ))
  simpa only [neg_zero, Real.rpow_zero, one_mul] using
    logarithmicAbelIntegrable_criticalPowerContactPrefix hc

/-- The unconditional outer zero bound supplies a linear initial contact
bound even at the critical power parameter. -/
theorem exists_linear_bound_criticalPowerContactPrefix :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |powerContactPrefix (1 / 2) N| ≤ C * (N : ℝ) := by
  have hXi : RHTower.XiZeroHalfPlaneBound (1 / 2) := by
    intro ρ hρ
    have hb := SquareRootThreshold.xiZeroHalfPlaneBound_zetaZeroWidth ρ hρ
    have hw := SquareRootThreshold.zetaZeroWidth_le_half
    linarith only [hb, hw]
  have hg := (strictGrowth_criticalPowerContactPrefix_iff_zeroHalfPlane
    (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr hXi
  obtain ⟨C, hC, hb⟩ := hg (1 / 2) (by norm_num)
  refine ⟨C, hC, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [powerContactPrefix]
  · simpa only [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one] using hb N hN

/-- The literal critical integral equals its contact Dirichlet series
in the initial absolute-convergence half-plane. -/
theorem oneSidedStepMellin_criticalPowerContacts_initial
    {s : ℂ} (hs : 2 < s.re) :
    oneSidedStepMellin (powerContactPrefix (1 / 2)) s =
      riemannZeta (s + 1) * criticalPowerContactFactor s := by
  obtain ⟨C, hC, hb⟩ := exists_linear_bound_criticalPowerContactPrefix
  have hf0 : powerContactPrefix (1 / 2) 0 = 0 := by simp [powerContactPrefix]
  have hb' : ∀ N : ℕ, |powerContactPrefix (1 / 2) N| ≤ C * (N : ℝ) ^ (1 : ℝ) := by
    simpa only [Real.rpow_one] using hb
  have hs0 : 0 < s.re := by linarith only [hs]
  have hgap : 1 < s.re := by linarith only [hs]
  rw [oneSidedStepMellin_eq_complexMellinPairing hf0 hs0
    (summable_mellin_majorant_of_power_bound hf0 hb' hgap)]
  rw [show powerContactPrefix (1 / 2) = RHTower.sourcePartialSum
      (fun n => (powerTailZeta (2 * (1 / 2)) * powerTailPrimeDeviation (1 / 2)) n) from rfl,
    complexMellinPairing_sourcePartialSum_eq hC hb' hs0 hgap,
    RHTower.abelTailSeries_sourcePartialSum hC hb' hs0 hgap
      (LSeriesSummable_powerContacts (by norm_num : (0 : ℝ) < 1 / 2)
        (by linarith only [hs])),
    LSeries_powerContacts (by norm_num : (0 : ℝ) < 1 / 2) (by linarith only [hs])]
  norm_num [criticalPowerContactFactor]

/-- The entire residue-unit identity continues the actual critical
contact symbol throughout the half-plane paid by absolute integrability. -/
theorem oneSidedStepMellin_criticalPowerContacts_eq_of_abelIntegrable
    (hc : LogarithmicAbelIntegrable (powerCombTail (1 / 2)))
    {s : ℂ} (hs : 0 < s.re) (hs1 : s + 1 / 2 ≠ 1)
    (hζ : riemannZeta (s + 1 / 2) ≠ 0) :
    oneSidedStepMellin (powerContactPrefix (1 / 2)) s =
      riemannZeta (s + 1) * criticalPowerContactFactor s := by
  have hh := contactSymbol_eq_of_holomorphic (a := 1 / 2) (by norm_num)
    (F := oneSidedStepMellin (powerContactPrefix (1 / 2)))
    (by simpa using differentiableOn_criticalContactIntegral_of_abelIntegrable hc)
    (fun z hz => by simpa [criticalPowerContactFactor] using
      oneSidedStepMellin_criticalPowerContacts_initial hz)
    (s := s) (by simpa using hs) (by simpa using hs1) (by simpa using hζ)
  simpa [criticalPowerContactFactor] using hh

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
