import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarPaymentHasAStrictInteriorMargin
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePolarSourceIsContinuousInTheWeightedNorm
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalFormHasAGammaLiminf

/-!
# Polar payment in physical collar coordinates

Undoing the half-weight converts the continuum window capacity into the charged
physical quadratic form. Both the actual pole cost and source normalization are
retained exactly.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory SpacingScaleHarmonicAnalysis WindowTowerOfSpecZ
  RenormalizedArithmeticPotentialTheory

/-- Polar payment in physical coordinates retains the scalar pole energy and the exact
continuous polar source. -/
theorem physical_charged_window_nonneg_of_polarPaymentAt {R A : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A) (hpay : PolarPaymentAt R A) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hsupp : ∀ u, u ∉ Icc (-A) 0 → F u = 0) (β : ℝ) :
    0 ≤ weilQuad F + criticalAliasCoefficient R * exponentialMass 8 F +
      (∫ u, tiltedUnitSpline u ^ 2) * criticalPoleWindowCost R * β ^ 2 +
      2 * (∫ u, tiltedUnitSpline u) * β * (∫ u, F u * polarSourceProfile u) := by
  let h : ℝ → ℝ := fun u => Real.exp (-u / 2) * F u
  have hh : ContDiff ℝ 2 h := by
    dsimp only [h]
    exact (Real.contDiff_exp.comp (contDiff_id.neg.div_const 2)).mul hF
  have hs : ∀ u, u ∉ Icc (-A) 0 → h u = 0 := by
    intro u hu
    dsimp only [h]
    rw [hsupp u hu, mul_zero]
  have hhalf : halfWeight h = F := by
    funext u
    unfold halfWeight
    dsimp only [h]
    rw [← mul_assoc, ← Real.exp_add]
    have he : u / 2 + -u / 2 = 0 := by ring
    rw [he, Real.exp_zero, one_mul]
  have hp := charged_window_nonneg_of_polarPaymentAt hR hpay hh hs
    ((∫ u, tiltedUnitSpline u) * β)
  rw [hhalf, generalTerminalPolarSource_eq_integral_polarSourceProfile hh hA hs, hhalf] at hp
  have hnorm : 0 < splineAtom := splineAtom_pos
  have hscaled := mul_nonneg (inv_pos.mpr hnorm).le hp
  have hI₁ : (∫ u, tiltedUnitSpline u) ≠ 0 := integral_tiltedUnitSpline_ne_zero
  have hI₂ : (∫ u, tiltedUnitSpline u ^ 2) ≠ 0 := integral_tiltedUnitSpline_sq_pos.ne'
  convert hscaled using 1
  unfold windowPencil splineAtom criticalAliasCoefficient
  field_simp [hI₁, hI₂, hR.ne']
  ring
#print axioms physical_charged_window_nonneg_of_polarPaymentAt
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
