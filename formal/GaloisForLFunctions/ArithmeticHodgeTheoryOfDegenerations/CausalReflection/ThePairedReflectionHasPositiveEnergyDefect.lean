import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ThePairedReflectionPreservesArithmeticEnergy
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalHalfLineStateHasNoPositiveLaplaceZero

/-!
# The exact positive defect of the full arithmetic energy

Prime, Gamma and pole terms are unchanged. The only difference is the
exponential mass, whose loss is the positive coefficient times the sum
of the two actual weighted resolvent energies.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry

private theorem integral_weighted_cx_sq (F : ℝ → ℝ) :
    (∫ u, ‖causalLaplaceWeighted (4 / Real.pi) (cx F) u‖ ^ 2) =
      ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  rw [norm_sq_causalLaplaceWeighted,
    show 2 * Real.pi * (4 / Real.pi) = 8 by field_simp]
  change ‖(F u : ℂ)‖ ^ 2 * Real.exp (-(8 * u)) = F u ^ 2 * Real.exp (-(8 * u))
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The two complex defects give the exact physical mass loss of the real representative. -/
theorem realPairedCausalReflection_weighted_energy {a : ℝ} (ha : 0 < a) (b : ℝ)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    (∫ u, F u ^ 2 * Real.exp (-(8 * u))) =
      (∫ u, realPairedCausalReflection a b F u ^ 2 * Real.exp (-(8 * u))) +
        (4 * a * (4 / Real.pi)) * pairedCausalResolventEnergy a b (4 / Real.pi) (cx F) := by
  have he : cx (realPairedCausalReflection a b F) =ᵐ[volume]
      pairedCausalReflection a b (cx F) := coe_realPairedCausalReflection_ae ha b hF.integrable
  have hmass : (∫ u, ‖causalLaplaceWeighted (4 / Real.pi)
        (pairedCausalReflection a b (cx F)) u‖ ^ 2) =
      ∫ u, ‖causalLaplaceWeighted (4 / Real.pi) (cx (realPairedCausalReflection a b F)) u‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [he] with u hu
    unfold causalLaplaceWeighted
    rw [hu]
  have hm := integral_weighted_pairedCausalReflection_energy
    (add_pos ha (by positivity)) b hF.memLp_weightedComplex
  rw [integral_weighted_cx_sq, hmass, integral_weighted_cx_sq] at hm
  exact hm

/-- At a nonreal Laplace zero, the full form loses exactly the paired resolvent energy. -/
theorem criticalHalfLineFullEnergy_realPairedCausalReflection {a : ℝ} (ha : 0 < a)
    {b : ℝ} (hb : b ≠ 0) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate a b) = 0) (R : ℝ) :
    criticalHalfLineFullEnergy R (realPairedCausalReflection a b F) =
      criticalHalfLineFullEnergy R F - criticalAliasCoefficient R * (4 * a * (4 / Real.pi)) *
        pairedCausalResolventEnergy a b (4 / Real.pi) (cx F) := by
  have hH := hF.realPairedCausalReflection ha hb hz
  have hm := realPairedCausalReflection_weighted_energy ha b hF
  unfold criticalHalfLineFullEnergy
  rw [archForm_realPairedCausalReflection ha b hF.integrable,
    primeSum_realPairedCausalReflection ha hb hF hz,
    poleTerm_realPairedCausalReflection ha hb hF hz,
    halfLineExpMass_eq_full hH.support, halfLineExpMass_eq_full hF.support, hm]
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
