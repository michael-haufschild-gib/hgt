import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ExponentialBarrierPositiveLevels
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.WeightedPositiveLevelAlgebra
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineGammaMixedEnergy

/-!
# Gamma jumps against exponential positive levels

The exponential barrier turns the two-point row inequality into a scalar
translation correction. Integrating it gives a lower bound for each mixed
jump, valid on the full half-line domain without smoothness.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- The exponential change of unknown controls every translated mixed edge. -/
theorem CriticalHalfLineEnergyDomain.exponentialBarrier_edge_lower {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {t : ℝ} (ht : 0 ≤ t) (β u h : ℝ) :
    (1 - Real.exp (β * h)) * (F u * exponentialBarrierPositiveLevel β t F u) +
      (1 - Real.exp (-(β * h))) *
        (F (u + h) * exponentialBarrierPositiveLevel β t F (u + h)) ≤
      (F u - F (u + h)) *
        (exponentialBarrierPositiveLevel β t F u -
          exponentialBarrierPositiveLevel β t F (u + h)) := by
  have hr := weighted_positiveLevel_row (Real.exp_pos (β * u))
    (Real.exp_pos (β * (u + h))) t (F u) (F (u + h))
  have hq : Real.exp (β * (u + h)) / Real.exp (β * u) = Real.exp (β * h) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hp : Real.exp (β * u) / Real.exp (β * (u + h)) = Real.exp (-(β * h)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hq, hp, ← hF.exponentialBarrierPositiveLevel_eq ht β u,
    ← hF.exponentialBarrierPositiveLevel_eq ht β (u + h)] at hr
  nlinarith only [hr]

/-- The integrated mixed jump is bounded below by the exact exponential correction. -/
theorem CriticalHalfLineEnergyDomain.exponentialBarrier_jump_lower {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) (h : ℝ) :
    (2 - Real.exp (β * h) - Real.exp (-(β * h))) *
      (∫ u, F u * exponentialBarrierPositiveLevel β t F u) ≤
      ∫ u, (F u - F (u + h)) *
        (exponentialBarrierPositiveLevel β t F u -
          exponentialBarrierPositiveLevel β t F (u + h)) := by
  let G := exponentialBarrierPositiveLevel β t F
  have hG := hF.exponentialBarrierPositiveLevel hβ ht
  have hFG : Integrable (fun u => F u * G u) := hF.memLp_real.integrable_mul hG.memLp_real
  have hshift : Integrable (fun u => F (u + h) * G (u + h)) :=
    hFG.comp_measurePreserving (measurePreserving_add_right volume h)
  have hdiff : Integrable (fun u => (F u - F (u + h)) * (G u - G (u + h))) :=
    (hF.memLp_real.sub
      (hF.memLp_real.comp_measurePreserving (measurePreserving_add_right volume h))).integrable_mul
      (hG.memLp_real.sub
        (hG.memLp_real.comp_measurePreserving (measurePreserving_add_right volume h)))
  have hi := integral_mono
    ((hFG.const_mul (1 - Real.exp (β * h))).add
      (hshift.const_mul (1 - Real.exp (-(β * h))))) hdiff
    (fun u => hF.exponentialBarrier_edge_lower ht β u h)
  have he : (∫ u, (1 - Real.exp (β * h)) * (F u * G u) +
      (1 - Real.exp (-(β * h))) * (F (u + h) * G (u + h))) =
      (2 - Real.exp (β * h) - Real.exp (-(β * h))) * (∫ u, F u * G u) := by
    rw [integral_add (hFG.const_mul _) (hshift.const_mul _), integral_const_mul,
      integral_const_mul, integral_add_right_eq_self (fun u => F u * G u) h]
    ring
  rw [he] at hi
  exact hi

/-- Multiplication by the positive Lévy density preserves the mixed-jump lower bound. -/
theorem CriticalHalfLineEnergyDomain.exponentialBarrier_levyJump_lower {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {β t h : ℝ}
    (hβ : 0 < β) (ht : 0 ≤ t) (hh : 0 < h) :
    archLevyDensity h * (2 - Real.exp (β * h) - Real.exp (-(β * h))) *
      (∫ u, F u * exponentialBarrierPositiveLevel β t F u) ≤
      halfLineGammaMixedJump F (exponentialBarrierPositiveLevel β t F) h := by
  have hi := mul_le_mul_of_nonneg_left (hF.exponentialBarrier_jump_lower hβ ht h)
    (archLevyDensity_pos hh).le
  simpa only [mul_assoc, halfLineGammaMixedJump] using hi

#print axioms CriticalHalfLineEnergyDomain.exponentialBarrier_jump_lower
#print axioms CriticalHalfLineEnergyDomain.exponentialBarrier_levyJump_lower
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
