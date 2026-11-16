import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheCriticalHalfLineStateHasNoBoundaryLaplaceZero
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ExponentialBarrierPoleComparison

/-!
# The growing polar charge cannot vanish

The polar kernel splits into half-exponentials with coefficients `C-S`
and `C+S`. Its growing coefficient on the negative half-line is the
Laplace transform at `1/2`, which never vanishes for a critical state.
Thus its absolute row bound has a strictly positive forcing coefficient.
-/

noncomputable section
open MeasureTheory Set
open _root_.RHTower

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry

/-- The literal polar kernel separates into decaying and growing half-exponentials. -/
theorem polarKernel_halfExponential_decomposition (F : ℝ → ℝ) (u : ℝ) :
    2 * coshHalfMoment F * Real.cosh (u / 2) -
        2 * sinhHalfMoment F * Real.sinh (u / 2) =
      (coshHalfMoment F - sinhHalfMoment F) * Real.exp (u / 2) +
        (coshHalfMoment F + sinhHalfMoment F) * Real.exp (-(u / 2)) := by
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

/-- The coefficient of the growing half-exponential is a nonzero Laplace value. -/
theorem criticalState_growingPolarCharge_ne_zero {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    coshHalfMoment F + sinhHalfMoment F ≠ 0 := by
  have hn := criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW ht hF
    (z := ((1 / 2 : ℝ) : ℂ)) (by norm_num)
  rw [(negativeHalfLineLaplace_halfPole_real
    (criticalHalfLineEnergyDomain_of_groundState hF).weighted).1] at hn
  intro h
  exact hn (by rw [h, Complex.ofReal_zero])

/-- The coefficient used in the absolute polar row estimate is strictly positive. -/
theorem criticalState_poleReadoutSize_pos {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    0 < halfLinePoleReadoutSize F := by
  have hn := abs_pos.mpr (criticalState_growingPolarCharge_ne_zero hW ht hF)
  have h := abs_add_le (coshHalfMoment F) (sinhHalfMoment F)
  unfold halfLinePoleReadoutSize
  linarith only [hn, h]

/-- Failure of RH supplies a critical state with nonzero growing polar charge. -/
theorem riemannHypothesis_or_criticalState_growingPolarCharge_ne_zero :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ coshHalfMoment F + sinhHalfMoment F ≠ 0 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl h
  · exact Or.inr ⟨W₀, F, hW, ht, hF, criticalState_growingPolarCharge_ne_zero hW ht hF⟩

#print axioms criticalState_growingPolarCharge_ne_zero
#print axioms criticalState_poleReadoutSize_pos
#print axioms riemannHypothesis_or_criticalState_growingPolarCharge_ne_zero

end GaloisForLFunctions.ExclusionOfTheCriticalState
