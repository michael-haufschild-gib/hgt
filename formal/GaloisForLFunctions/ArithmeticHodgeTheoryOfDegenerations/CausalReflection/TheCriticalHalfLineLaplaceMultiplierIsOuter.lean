import GaloisForLFunctions.HTGeometry.HardyBoundary.NegativeHalfLineLaplaceOuter
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheCriticalHalfLineStateHasNoBoundaryLaplaceZero
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheCriticalHalfLineStateHasNoTerminalSupportGap

/-!
# The critical half-line Laplace multiplier is outer

Boundary zero exclusion confines the canonical inner factor to a delay.
Endpoint mass excludes every positive delay, so the actual Cayley-composed
Laplace transform is cyclic for the disk Hardy shift.
-/

noncomputable section
open MeasureTheory Filter Set Topology Metric Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry WindowTowerOfSpecZ

/-- The actual critical state's bounded Laplace transform in disk coordinates. -/
def criticalHalfLineGroundStateLaplaceMultiplier {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) : DiskMultiplier :=
  negativeHalfLineLaplaceDiskMultiplier (cx F)
    ((criticalHalfLineEnergyDomain_of_groundState hF).integrable.ofReal (𝕜 := ℂ))
    (criticalHalfLineEnergyDomain_of_groundState hF).memLp_complex
    (fun u hu => by
      change (F u : ℂ) = 0
      rw [(criticalHalfLineEnergyDomain_of_groundState hF).support u hu, Complex.ofReal_zero])

/-- The canonical inner factor of the actual critical state's Laplace transform
is constant; equivalently, its disk Hardy multiplier has dense range. -/
theorem criticalHalfLineGroundState_laplaceMultiplier_outer
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    IsOuterDiskMultiplier (criticalHalfLineGroundStateLaplaceMultiplier hF) := by
  apply isOuter_negativeHalfLineLaplaceDiskMultiplier
  · intro z hz
    exact criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW hthreshold hF hz
  · intro a ha
    have hpos := criticalHalfLineGroundState_endpoint_mass_pos hW hthreshold hF ha
    simpa only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hpos

/-- Failure of RH supplies an actual critical state with an outer Laplace multiplier. -/
theorem riemannHypothesis_or_exists_outerLaplace_criticalHalfLineGroundState :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ)
      (hF : IsCriticalHalfLineGroundState W₀ F), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsOuterDiskMultiplier (criticalHalfLineGroundStateLaplaceMultiplier hF) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hF, hW, ht, criticalHalfLineGroundState_laplaceMultiplier_outer hW ht hF⟩

#print axioms riemannHypothesis_or_exists_outerLaplace_criticalHalfLineGroundState

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
