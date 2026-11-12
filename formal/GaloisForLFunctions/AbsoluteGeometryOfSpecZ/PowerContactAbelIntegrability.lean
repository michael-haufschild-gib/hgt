import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ContactSymbolsContinueAcrossZeros
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ConvergentPowerCombsHaveNoNonrealBoundaryResidues
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.LogarithmicAbelIntegrability

/-!
# Absolute comb integrability gives the actual contact symbol

The convergent elementary remainder transfers absolute logarithmic Abel
integrability from the literal comb to its normalized contacts. Their
literal Mellin integral is holomorphic in the open contact half-plane.
An unconditional coarse contact bound identifies its initial Dirichlet
series, and the entire residue unit continues that identity.
-/

noncomputable section

open Complex Finset Filter Topology Set MeasureTheory

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity TransHorizonIncidenceMechanics

/-- Absolute comb integrability pays absolute integrability of the
normalized prime-contact prefix. -/
theorem logarithmicAbelIntegrable_normalizedPowerContacts
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (hc : LogarithmicAbelIntegrable (powerCombTail a)) :
    LogarithmicAbelIntegrable (normalizedPowerContacts a) := by
  let E : ℕ → ℝ := fun N => (N : ℝ) ^ (2 * a - 1) * powerTailArchimedean a N -
    2 * tailRiemannSum (powerTailReferenceProfile a) N + powerTailCombRemainder a N
  have hE : Tendsto E atTop (𝓝 (powerTailArchimedeanRowLimit a / (1 - 2 * a) -
      2 * (∫ t in Ioc (0 : ℝ) 1, powerTailReferenceProfile a t))) := by
    have hh := ((tendsto_normalized_powerTailArchimedean ha ha2).sub
      ((riemannOn_powerTailReferenceProfile ha ha2).2.const_mul 2)).add
        (tendsto_powerTailCombRemainder ha ha2)
    simpa only [add_zero] using hh
  have hEi := logarithmicAbelIntegrable_of_strictGrowth (strictPowerGrowth_zero_of_tendsto hE)
  apply ((hEi.sub hc).const_mul (1 / 2)).congr_pos
  intro N hN
  rw [powerCombTail_eq_mellin_meshes a hN]
  dsimp only [E, normalizedPowerContacts]
  ring

/-- The zero-free outer half-plane already supplies a coarse linear
bound on the unnormalized contact prefix. -/
theorem exists_linear_bound_powerContactPrefix
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |powerContactPrefix a N| ≤ C * (N : ℝ) := by
  have hXi : RHTower.XiZeroHalfPlaneBound (1 / 2 - a + a) := by
    intro ρ hρ
    have hb := SquareRootThreshold.xiZeroHalfPlaneBound_zetaZeroWidth ρ hρ
    have hw := SquareRootThreshold.zetaZeroWidth_le_half
    linarith only [hb, hw]
  have hcenter := (strictGrowth_centeredContact_iff_zeroHalfPlane ha ha2 ha.le).mpr hXi
  have href : _root_.HTGeometry.StrictNaturalPowerGrowth
      (fun N => ∑ n ∈ Icc 1 N, powerTailReference a n) (1 - 2 * a) := by
    apply (_root_.HTGeometry.strictNaturalPowerGrowth_iff_succ (by simp)
      (by linarith only [ha2] : 0 ≤ 1 - 2 * a)).mpr
    simpa only [RHTower.PartialSumPowerBound, RHTower.sum_range_succ_eq_sourcePartialSum,
      RHTower.sourcePartialSum] using partialSumPowerBound_powerTailReference ha ha2
  have hg := hcenter.sub (href.mono (by linarith only [ha] : 1 - 2 * a ≤ 1 - 2 * a + a))
  have he : (fun N => (∑ n ∈ Icc 1 N, powerTailCenteredContact a n) -
      ∑ n ∈ Icc 1 N, powerTailReference a n) = powerContactPrefix a := by
    funext N
    simp only [powerTailCenteredContact_eq, ArithmeticFunction.add_apply,
      sum_add_distrib, add_sub_cancel_right, powerContactPrefix]
  rw [he] at hg
  obtain ⟨C, hC, hb⟩ := hg a ha
  refine ⟨C, hC, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [powerContactPrefix]
  · simpa only [show 1 - 2 * a + a + a = 1 by ring, Real.rpow_one] using hb N hN

/-- In the initial half-plane, the literal integral has the contact
Dirichlet symbol without any endpoint assumption. -/
theorem oneSidedStepMellin_powerContact_initial
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) {s : ℂ} (hs : 2 < s.re) :
    oneSidedStepMellin (powerContactPrefix a) s =
      riemannZeta (s + ((2 * a : ℝ) : ℂ)) *
        (-deriv riemannZeta (s + (a : ℂ)) / riemannZeta (s + (a : ℂ)) -
          riemannZeta (s + (a : ℂ))) := by
  obtain ⟨C, hC, hb⟩ := exists_linear_bound_powerContactPrefix ha ha2
  have hf0 : powerContactPrefix a 0 = 0 := by simp [powerContactPrefix]
  have hb' : ∀ N : ℕ, |powerContactPrefix a N| ≤ C * (N : ℝ) ^ (1 : ℝ) := by
    simpa only [Real.rpow_one] using hb
  have hs0 : 0 < s.re := by linarith only [hs]
  have hgap : 1 < s.re := by linarith only [hs]
  rw [oneSidedStepMellin_eq_complexMellinPairing hf0 hs0
    (summable_mellin_majorant_of_power_bound hf0 hb' hgap)]
  rw [show powerContactPrefix a = RHTower.sourcePartialSum
      (fun n => (powerTailZeta (2 * a) * powerTailPrimeDeviation a) n) from rfl,
    complexMellinPairing_sourcePartialSum_eq hC hb' hs0 hgap,
    RHTower.abelTailSeries_sourcePartialSum hC hb' hs0 hgap
      (LSeriesSummable_powerContacts ha (by linarith only [ha, hs])),
    LSeries_powerContacts ha (by linarith only [ha, hs])]

/-- Absolute Abel integrability alone gives contact holomorphy throughout
the open power half-plane. -/
theorem differentiableOn_powerContactMellin_of_abelIntegrable
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (hc : LogarithmicAbelIntegrable (powerCombTail a)) :
    DifferentiableOn ℂ (oneSidedStepMellin (powerContactPrefix a))
      {s : ℂ | 1 - 2 * a < s.re} := by
  have hn := logarithmicAbelIntegrable_normalizedPowerContacts ha ha2 hc
  have he : normalizedPowerContacts a =
      fun N : ℕ => (N : ℝ) ^ (-(1 - 2 * a)) * powerContactPrefix a N := by
    funext N
    change (N : ℝ) ^ (2 * a - 1) * powerContactPrefix a N = _
    rw [show -(1 - 2 * a) = 2 * a - 1 by ring]
  rw [he] at hn
  exact differentiableOn_oneSidedStepMellin_of_normalized_abel
    (by linarith only [ha2]) hn

/-- The literal contact integral continues the actual symbol throughout
the half-plane paid by absolute comb integrability. -/
theorem oneSidedStepMellin_powerContact_eq_of_abelIntegrable
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (hc : LogarithmicAbelIntegrable (powerCombTail a))
    {s : ℂ} (hs : 1 - 2 * a < s.re) (hs1 : s + (a : ℂ) ≠ 1)
    (hζ : riemannZeta (s + (a : ℂ)) ≠ 0) :
    oneSidedStepMellin (powerContactPrefix a) s =
      riemannZeta (s + ((2 * a : ℝ) : ℂ)) *
        (-deriv riemannZeta (s + (a : ℂ)) / riemannZeta (s + (a : ℂ)) -
          riemannZeta (s + (a : ℂ))) :=
  contactSymbol_eq_of_holomorphic ha
    (differentiableOn_powerContactMellin_of_abelIntegrable ha ha2 hc)
    (fun _ hz => oneSidedStepMellin_powerContact_initial ha ha2 hz) hs hs1 hζ

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
