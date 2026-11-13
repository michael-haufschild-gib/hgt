import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ExponentialBarrierSmallGammaJumps
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineGammaLargeJumps

/-!
# The full Gamma comparison for exponential positive levels

Small jumps have a cutoff-independent loss. Large jumps contribute a
divergent diagonal row and a bounded ordinary-mass loss. Their exact split
retains the full Gamma symbol, including its constant mass term.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory

/-- A positive cutoff splits the absolutely integrable mixed jump energy without an endpoint loss. -/
theorem integral_halfLineGammaMixedJump_split {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ h in Ioi 0, halfLineGammaMixedJump F G h) =
      (∫ h in Ioc 0 δ, halfLineGammaMixedJump F G h) +
        ∫ h in Ioi δ, halfLineGammaMixedJump F G h := by
  have hi := integrableOn_halfLineGammaMixedJump hF hG
  have he : Ioi (0 : ℝ) = Ioc 0 δ ∪ Ioi δ := by
    ext h
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hh
      by_cases hd : h ≤ δ
      · exact Or.inl ⟨hh, hd⟩
      · exact Or.inr (lt_of_not_ge hd)
    · rintro (hh | hh)
      · exact hh.1
      · exact hδ.trans hh
  rw [he]
  apply setIntegral_union _ measurableSet_Ioi
    (hi.mono_set (fun _ hh => hh.1)) (hi.mono_set (fun _ hh => hδ.trans hh))
  apply disjoint_left.mpr
  intro h hh ht
  exact (not_lt_of_ge hh.2) ht

/-- The complete Gamma form has a divergent diagonal row and a level-independent mass loss. -/
theorem CriticalHalfLineEnergyDomain.exponentialBarrier_gammaMixed_lower {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {β t δ : ℝ}
    (hβ : 0 < β) (ht : 0 ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((2 * ∫ h in Ioi δ, archLevyDensity h) -
        halfLineBarrierSmallJumpConstant β - 2 * |gammaHardyPhaseRate 0|) *
        (∫ u, F u * exponentialBarrierPositiveLevel β t F u) -
      2 * Real.sqrt ((∫ h in Ioi δ, archLevyDensity h ^ 2) * ∫ u, F u ^ 2) *
        (∫ u, exponentialBarrierPositiveLevel β t F u) ≤
      gammaMixedForm F (exponentialBarrierPositiveLevel β t F) := by
  have hG := hF.exponentialBarrierPositiveLevel_mem hβ ht
  have hsmall := hF.exponentialBarrier_smallGamma_lower hβ ht hδ1
  have hlarge := halfLineGamma_largeJump_lower hδ hF hG
    (fun u => (exponentialBarrierPositiveLevel_le_abs ht β F u).1)
  have hM : 0 ≤ ∫ u, F u * exponentialBarrierPositiveLevel β t F u :=
    integral_nonneg fun u => hF.mul_exponentialBarrierPositiveLevel_nonneg ht β u
  have hoffset := mul_le_mul_of_nonneg_right
    (neg_abs_le (gammaHardyPhaseRate 0)) hM
  rw [gammaMixedForm_eq_halfLineGammaMixedJump hF hG,
    integral_halfLineGammaMixedJump_split hF hG hδ]
  linarith only [hsmall, hlarge, hoffset]

#print axioms integral_halfLineGammaMixedJump_split
#print axioms CriticalHalfLineEnergyDomain.exponentialBarrier_gammaMixed_lower
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
