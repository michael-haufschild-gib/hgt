import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineGroundStateSeparation

/-!
# Strict curvature of the confining ground energy

The full energy is affine in the reciprocal ratio. Attainment and the
absence of a common minimizer make its lower envelope strictly concave.
The same comparison orders the exponential masses of its minimizers.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- Ground energy as a function of the confinement strength. -/
def confiningHalfLineGroundEnergy (t : ℝ) : ℝ :=
  criticalHalfLineGroundEnergy t⁻¹

theorem criticalAliasCoefficient_inv (t : ℝ) :
    criticalAliasCoefficient t⁻¹ = criticalAliasCoefficient 1 * t := by
  rw [criticalAliasCoefficient_eq_div, div_eq_mul_inv, inv_inv]

/-- Each fixed profile has affine energy in the reciprocal ratio. -/
theorem criticalHalfLineFullEnergy_reciprocal_parameter (t : ℝ) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    criticalHalfLineFullEnergy t⁻¹ F = criticalHalfLineFullEnergy 1 F +
      (criticalAliasCoefficient 1 * t - criticalAliasCoefficient 1) *
        (∫ u, F u ^ 2 * Real.exp (-(8 * u))) := by
  rw [criticalHalfLineFullEnergy_change_ratio t⁻¹ 1 hF, criticalAliasCoefficient_inv]

theorem criticalHalfLineFullEnergy_reciprocal_affine (x y α β : ℝ)
    (hweights : α + β = 1) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    criticalHalfLineFullEnergy (α * x + β * y)⁻¹ F =
      α * criticalHalfLineFullEnergy x⁻¹ F + β * criticalHalfLineFullEnergy y⁻¹ F := by
  rw [criticalHalfLineFullEnergy_reciprocal_parameter (α * x + β * y) hF,
    criticalHalfLineFullEnergy_reciprocal_parameter x hF,
    criticalHalfLineFullEnergy_reciprocal_parameter y hF]
  have hconst := congrArg (fun c : ℝ => c *
    (criticalHalfLineFullEnergy 1 F - criticalAliasCoefficient 1 *
      (∫ u, F u ^ 2 * Real.exp (-(8 * u))))) hweights
  nlinarith only [hconst]

/-- The variational floor is strictly concave on positive confinement strengths. -/
theorem confiningHalfLineGroundEnergy_strict_jensen
    {x y α β : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y)
    (hα : 0 < α) (hβ : 0 < β) (hweights : α + β = 1) :
    α * confiningHalfLineGroundEnergy x + β * confiningHalfLineGroundEnergy y <
      confiningHalfLineGroundEnergy (α * x + β * y) := by
  have hm : 0 < α * x + β * y := add_pos (mul_pos hα hx) (mul_pos hβ hy)
  obtain ⟨F, hF⟩ := exists_criticalHalfLineGroundEnergy_minimizer (inv_pos.mpr hm)
  have hfirst := criticalHalfLineGroundEnergy_le (inv_pos.mpr hx) hF.1 hF.2.1
  have hsecond := criticalHalfLineGroundEnergy_le (inv_pos.mpr hy) hF.1 hF.2.1
  have he := criticalHalfLineFullEnergy_reciprocal_affine x y α β hweights hF.1
  rw [hF.2.2] at he
  have hdistinct : x⁻¹ ≠ y⁻¹ := by
    intro h
    apply hxy
    simpa only [inv_inv] using congrArg (fun t : ℝ => t⁻¹) h
  have hstrict : criticalHalfLineGroundEnergy x⁻¹ < criticalHalfLineFullEnergy x⁻¹ F ∨
      criticalHalfLineGroundEnergy y⁻¹ < criticalHalfLineFullEnergy y⁻¹ F := by
    by_contra h
    push Not at h
    have hminX : IsHalfLineEnergyMinimizer x⁻¹ F :=
      ⟨hF.1, hF.2.1, le_antisymm h.1 hfirst⟩
    have hminY : IsHalfLineEnergyMinimizer y⁻¹ F :=
      ⟨hF.1, hF.2.1, le_antisymm h.2 hsecond⟩
    exact hdistinct (halfLineEnergyMinimizer_ratio_unique
      (inv_pos.mpr hx) (inv_pos.mpr hy) hminX hminY)
  change α * criticalHalfLineGroundEnergy x⁻¹ + β * criticalHalfLineGroundEnergy y⁻¹ < _
  change _ < criticalHalfLineGroundEnergy (α * x + β * y)⁻¹
  rw [he]
  rcases hstrict with hstrict | hstrict
  · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hstrict hα)
      (mul_le_mul_of_nonneg_left hsecond hβ.le)
  · exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hfirst hα.le)
      (mul_lt_mul_of_pos_left hstrict hβ)

/-- Increasing confinement strictly decreases the minimizing exponential mass. -/
theorem halfLineEnergyMinimizer_exponential_mass_strict_antitone
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) {F G : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer x⁻¹ F) (hG : IsHalfLineEnergyMinimizer y⁻¹ G) :
    (∫ u, G u ^ 2 * Real.exp (-(8 * u))) <
      ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
  have hy := hx.trans hxy
  have hdistinct : x⁻¹ ≠ y⁻¹ := by
    intro h
    exact hxy.ne (by simpa only [inv_inv] using congrArg (fun t : ℝ => t⁻¹) h)
  have htestF := criticalHalfLineGroundEnergy_le (inv_pos.mpr hy) hF.1 hF.2.1
  have htestG := criticalHalfLineGroundEnergy_le (inv_pos.mpr hx) hG.1 hG.2.1
  have hstrictF : criticalHalfLineGroundEnergy y⁻¹ < criticalHalfLineFullEnergy y⁻¹ F := by
    rcases lt_or_eq_of_le htestF with hlt | he
    · exact hlt
    · exact False.elim (hdistinct (halfLineEnergyMinimizer_ratio_unique (inv_pos.mpr hx)
        (inv_pos.mpr hy) hF ⟨hF.1, hF.2.1, he.symm⟩))
  have hFchange := criticalHalfLineFullEnergy_change_ratio y⁻¹ x⁻¹ hF.1
  have hGchange := criticalHalfLineFullEnergy_change_ratio x⁻¹ y⁻¹ hG.1
  rw [hF.2.2, criticalAliasCoefficient_inv y, criticalAliasCoefficient_inv x] at hFchange
  rw [hG.2.2, criticalAliasCoefficient_inv x, criticalAliasCoefficient_inv y] at hGchange
  have hproduct : criticalAliasCoefficient 1 * (y - x) *
      ((∫ u, F u ^ 2 * Real.exp (-(8 * u))) -
        (∫ u, G u ^ 2 * Real.exp (-(8 * u)))) > 0 := by
    nlinarith only [hstrictF, htestG, hFchange, hGchange]
  have hcoef : 0 < criticalAliasCoefficient 1 * (y - x) :=
    mul_pos (criticalAliasCoefficient_positive zero_lt_one) (sub_pos.mpr hxy)
  have hdiff : 0 < (∫ u, F u ^ 2 * Real.exp (-(8 * u))) -
      (∫ u, G u ^ 2 * Real.exp (-(8 * u))) :=
    (mul_pos_iff_of_pos_left hcoef).mp hproduct
  exact sub_pos.mp hdiff

#print axioms confiningHalfLineGroundEnergy_strict_jensen
#print axioms halfLineEnergyMinimizer_exponential_mass_strict_antitone

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
