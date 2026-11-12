import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ContactSymbolsContinueAcrossZeros
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ConvergentPowerCombsHaveNoNonrealBoundaryResidues
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.StrictPowerGrowthHasAnOpenMellinHalfPlane

/-!
# The contact symbol at the closed zero-width boundary

The actual zero width gives strict power growth of the centered contacts.
Removing the elementary reference term preserves that growth threshold.
The resulting open Mellin half-plane carries the actual Dirichlet symbol,
without assuming convergence of the boundary comb.
-/

noncomputable section

open Complex Finset Filter Topology Set

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity TransHorizonIncidenceMechanics

/-- At the closed width boundary, the literal contact prefix has strict
growth threshold `1-2a`. -/
theorem strictGrowth_powerContactPrefix_of_add_width_le_half
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (haw : a + SquareRootThreshold.zetaZeroWidth ≤ 1 / 2) :
    _root_.HTGeometry.StrictNaturalPowerGrowth (powerContactPrefix a) (1 - 2 * a) := by
  have hθ : 0 ≤ 1 - 2 * a := by linarith only [ha2]
  have hXi : RHTower.XiZeroHalfPlaneBound (1 / 2 - a + 0) := by
    intro ρ hρ
    have hb := SquareRootThreshold.xiZeroHalfPlaneBound_zetaZeroWidth ρ hρ
    linarith only [hb, haw]
  have hcenter := (strictGrowth_centeredContact_iff_zeroHalfPlane ha ha2 (le_refl (0 : ℝ))).mpr hXi
  simp only [add_zero] at hcenter
  have href : _root_.HTGeometry.StrictNaturalPowerGrowth
      (fun N => ∑ n ∈ Icc 1 N, powerTailReference a n) (1 - 2 * a) := by
    apply (_root_.HTGeometry.strictNaturalPowerGrowth_iff_succ (by simp) hθ).mpr
    simpa only [RHTower.PartialSumPowerBound, RHTower.sum_range_succ_eq_sourcePartialSum,
      RHTower.sourcePartialSum] using partialSumPowerBound_powerTailReference ha ha2
  have hh := hcenter.sub href
  have he : (fun N => (∑ n ∈ Icc 1 N, powerTailCenteredContact a n) -
      ∑ n ∈ Icc 1 N, powerTailReference a n) = powerContactPrefix a := by
    funext N
    simp only [powerTailCenteredContact_eq, ArithmeticFunction.add_apply,
      sum_add_distrib, add_sub_cancel_right, powerContactPrefix]
  simpa only [he] using hh

private theorem closedWidth_contact_initial
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (haw : a + SquareRootThreshold.zetaZeroWidth ≤ 1 / 2)
    {s : ℂ} (hs : 2 < s.re) :
    complexMellinPairing (powerContactPrefix a) s =
      riemannZeta (s + ((2 * a : ℝ) : ℂ)) *
        (-deriv riemannZeta (s + (a : ℂ)) / riemannZeta (s + (a : ℂ)) -
          riemannZeta (s + (a : ℂ))) := by
  have hg := strictGrowth_powerContactPrefix_of_add_width_le_half ha ha2 haw
  obtain ⟨C, hC, hb⟩ := hg 1 (by norm_num)
  have hb' : ∀ N : ℕ, |powerContactPrefix a N| ≤ C * (N : ℝ) ^ (1 - 2 * a + 1) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have hz : powerContactPrefix a 0 = 0 := by simp [powerContactPrefix]
      rw [hz, abs_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg 0) _)
    · exact hb N hN
  have hs0 : 0 < s.re := by linarith only [hs]
  have hgap : 1 - 2 * a + 1 < s.re := by linarith only [ha, hs]
  rw [show powerContactPrefix a = RHTower.sourcePartialSum
      (fun n => (powerTailZeta (2 * a) * powerTailPrimeDeviation a) n) from rfl,
    complexMellinPairing_sourcePartialSum_eq hC hb' hs0 hgap,
    RHTower.abelTailSeries_sourcePartialSum hC hb' hs0 hgap
      (LSeriesSummable_powerContacts ha (by linarith only [ha, hs])),
    LSeries_powerContacts ha (by linarith only [ha, hs])]

/-- The contact symbol holds throughout its open Mellin half-plane even
when the boundary comb itself has no ordinary limit. -/
theorem complexMellinPairing_powerContacts_eq_of_add_width_le_half
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (haw : a + SquareRootThreshold.zetaZeroWidth ≤ 1 / 2)
    {s : ℂ} (hs : 1 - 2 * a < s.re) (hs1 : s + (a : ℂ) ≠ 1)
    (hζ : riemannZeta (s + (a : ℂ)) ≠ 0) :
    complexMellinPairing (powerContactPrefix a) s =
      riemannZeta (s + ((2 * a : ℝ) : ℂ)) *
        (-deriv riemannZeta (s + (a : ℂ)) / riemannZeta (s + (a : ℂ)) -
          riemannZeta (s + (a : ℂ))) := by
  exact contactSymbol_eq_of_holomorphic ha
    (differentiableOn_complexMellinPairing_of_strict_power_growth
      (by simp [powerContactPrefix]) (by linarith only [ha2])
      (strictGrowth_powerContactPrefix_of_add_width_le_half ha ha2 haw))
    (fun _ hz => closedWidth_contact_initial ha ha2 haw hz) hs hs1 hζ

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
