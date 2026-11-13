import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineWeakEquation
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalTerminalWallEnergy
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineSharpCutDomain

/-!
# Energy forced into a terminal collar

Subtracting a minimizer leaves its shifted quadratic form unchanged.
The complement of a terminal collar lies behind a displaced wall, whose
exact translation deficit therefore gives a lower bound for collar energy.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- The attained ordinary-mass floor strengthens the wall bound at every positive confinement. -/
theorem criticalHalfLineFullEnergy_shifted_terminal_wall {R : ℝ} (hR : 0 < R)
    {H : ℝ → ℝ} (hH : CriticalHalfLineEnergyDomain H) (h : ℝ)
    (hgap : ∀ u, -h ≤ u → H u = 0) :
    criticalAliasCoefficient R * (1 - Real.exp (-(8 * h))) *
        (∫ u, H u ^ 2 * Real.exp (-(8 * u))) ≤
      criticalHalfLineFullEnergy R H - criticalHalfLineGroundEnergy R * (∫ u, H u ^ 2) := by
  have hd := hH.comp_add_right (-h) (fun u hu => hgap _ (by linarith only [hu]))
  have hb := criticalHalfLineGroundEnergy_mul_mass_le_all hR hd
  have he := criticalHalfLineFullEnergy_terminal_wall_deficit R hH h hgap
  rw [criticalHalfLineExponentialPair_self] at he
  rw [integral_add_right_eq_self (fun u => H u ^ 2) (-h)] at hb
  linarith only [hb, he]

/-- A minimizing profile is a null direction of the shifted quadratic form on the actual domain. -/
theorem IsHalfLineEnergyMinimizer.sub_shifted_energy {R : ℝ} (hR : 0 < R)
    {F G : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F)
    (hG : CriticalHalfLineEnergyDomain G) :
    criticalHalfLineFullEnergy R (fun u => F u - G u) -
        criticalHalfLineGroundEnergy R * (∫ u, (F u - G u) ^ 2) =
      criticalHalfLineFullEnergy R G - criticalHalfLineGroundEnergy R * (∫ u, G u ^ 2) := by
  have he := criticalHalfLineFullEnergy_add_const_mul R hF.1 hG (-1)
  have hm := criticalHalfLine_square_mass_add_const_mul hF.1 hG (-1)
  have hd : (fun u => F u + (-1) * G u) = (fun u => F u - G u) := by
    funext u
    ring
  rw [hd, hF.2.2, hF.weakEquation hR hG] at he
  rw [hd, hF.2.1] at hm
  linear_combination he - criticalHalfLineGroundEnergy R * hm

/-- The tail's exponential mass bounds the shifted energy of a terminal collar from below. -/
theorem IsHalfLineEnergyMinimizer.terminalCut_energy_lower {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) (h : ℝ) :
    criticalAliasCoefficient R * (1 - Real.exp (-(8 * h))) *
        (∫ u, (F u - halfLineTerminalCut h F u) ^ 2 * Real.exp (-(8 * u))) ≤
      criticalHalfLineFullEnergy R (halfLineTerminalCut h F) -
        criticalHalfLineGroundEnergy R * (∫ u, halfLineTerminalCut h F u ^ 2) := by
  have hB := hF.1.terminalCut h
  have hD : CriticalHalfLineEnergyDomain (fun u => F u - halfLineTerminalCut h F u) := by
    simpa only [neg_one_mul, ← sub_eq_add_neg] using hF.1.add_const_mul hB (-1)
  have hgap : ∀ u, -h ≤ u → F u - halfLineTerminalCut h F u = 0 := by
    intro u hu
    by_cases hu0 : u ≤ 0
    · rw [halfLineTerminalCut, indicator_of_mem (show u ∈ Icc (-h) 0 from ⟨hu, hu0⟩),
        sub_self]
    · rw [hF.1.support u (lt_of_not_ge hu0).le, hB.support u (lt_of_not_ge hu0).le, sub_self]
  have hw := criticalHalfLineFullEnergy_shifted_terminal_wall hR hD h hgap
  rwa [hF.sub_shifted_energy hR hB] at hw

#print axioms criticalHalfLineFullEnergy_shifted_terminal_wall
#print axioms IsHalfLineEnergyMinimizer.sub_shifted_energy
#print axioms IsHalfLineEnergyMinimizer.terminalCut_energy_lower
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
