import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ActualHalfLineLevyEnergy
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineWeakEquation

/-!
# The actual mixed Gamma form in jump coordinates

Polarization of the finite diagonal Lévy identity gives an absolutely
integrable mixed jump form. This permits positive-level tests and cutoff
row estimates on measurable half-line profiles.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory

/-- The mixed physical jump integrand in the literal Gamma normalization. -/
def halfLineGammaMixedJump (F G : ℝ → ℝ) (h : ℝ) : ℝ :=
  archLevyDensity h * ∫ u, (F u - F (u + h)) * (G u - G (u + h))

private theorem jump_square_sum {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) (h : ℝ) :
    (∫ u, ((F u + G u) - (F (u + h) + G (u + h))) ^ 2) =
      (∫ u, (F u - F (u + h)) ^ 2) +
        2 * (∫ u, (F u - F (u + h)) * (G u - G (u + h))) +
        ∫ u, (G u - G (u + h)) ^ 2 := by
  have hf := hF.memLp_real.sub
    (hF.memLp_real.comp_measurePreserving (measurePreserving_add_right volume h))
  have hg := hG.memLp_real.sub
    (hG.memLp_real.comp_measurePreserving (measurePreserving_add_right volume h))
  have hff := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hgg := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hfg : Integrable (fun u => (F u - F (u + h)) * (G u - G (u + h))) :=
    hf.integrable_mul hg
  simp only [Pi.sub_apply, Function.comp_apply, Real.norm_eq_abs, sq_abs] at hff hgg
  calc
    _ = ∫ u, ((F u - F (u + h)) ^ 2 +
        2 * ((F u - F (u + h)) * (G u - G (u + h)))) +
          (G u - G (u + h)) ^ 2 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun u => by ring
    _ = _ := by
      rw [integral_add (hff.add (hfg.const_mul 2)) hgg,
        integral_add hff (hfg.const_mul 2), integral_const_mul]

private theorem halfLineGammaMixedJump_eq {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) (h : ℝ) :
    halfLineGammaMixedJump F G h =
      ((archLevyDensity h * ∫ u, ((F u + G u) - (F (u + h) + G (u + h))) ^ 2) -
        (archLevyDensity h * ∫ u, (F u - F (u + h)) ^ 2) -
        (archLevyDensity h * ∫ u, (G u - G (u + h)) ^ 2)) / 2 := by
  rw [jump_square_sum hF hG h, halfLineGammaMixedJump]
  ring

/-- The mixed jump form is absolutely integrable on the full actual domain. -/
theorem integrableOn_halfLineGammaMixedJump {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    IntegrableOn (halfLineGammaMixedJump F G) (Ioi 0) := by
  have hsum : CriticalHalfLineEnergyDomain (fun u => F u + G u) := by
    simpa only [one_mul] using hF.add_const_mul hG 1
  apply (((hsum.integrableOn_levyIntegrand.sub hF.integrableOn_levyIntegrand).sub
    hG.integrableOn_levyIntegrand).div_const 2).congr
  exact Eventually.of_forall fun h => (halfLineGammaMixedJump_eq hF hG h).symm

theorem integral_halfLineGammaMixedJump {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    (∫ h in Ioi 0, halfLineGammaMixedJump F G h) =
      (levyEnergy (fun u => F u + G u) - levyEnergy F - levyEnergy G) / 2 := by
  have hsum : CriticalHalfLineEnergyDomain (fun u => F u + G u) := by
    simpa only [one_mul] using hF.add_const_mul hG 1
  simp_rw [halfLineGammaMixedJump_eq hF hG]
  rw [integral_div,
    integral_sub (hsum.integrableOn_levyIntegrand.sub hF.integrableOn_levyIntegrand)
      hG.integrableOn_levyIntegrand,
    integral_sub hsum.integrableOn_levyIntegrand hF.integrableOn_levyIntegrand]
  rfl

/-- Polarization retains the complete Gamma symbol and its exact mass offset. -/
theorem gammaMixedForm_eq_halfLineGammaMixedJump {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    gammaMixedForm F G = 2 * gammaHardyPhaseRate 0 * (∫ u, F u * G u) +
      ∫ h in Ioi 0, halfLineGammaMixedJump F G h := by
  have hsum : CriticalHalfLineEnergyDomain (fun u => F u + G u) := by
    simpa only [one_mul] using hF.add_const_mul hG 1
  have he := archForm_add_const_mul_of_integrable
    hF.integrable hG.integrable hF.gamma hG.gamma 1
  have hm := criticalHalfLine_square_mass_add_const_mul hF hG 1
  simp only [one_mul, one_pow] at he hm
  rw [hsum.archForm_eq_levyEnergy, hF.archForm_eq_levyEnergy, hG.archForm_eq_levyEnergy, hm] at he
  rw [integral_halfLineGammaMixedJump hF hG]
  linear_combination - he / 2

#print axioms integrableOn_halfLineGammaMixedJump
#print axioms gammaMixedForm_eq_halfLineGammaMixedJump
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
