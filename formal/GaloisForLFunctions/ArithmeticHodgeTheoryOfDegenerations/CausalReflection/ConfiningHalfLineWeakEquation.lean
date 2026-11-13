import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineEnergyBranch

/-!
# The weak equation at an arbitrary confining minimum

Subtracting the attained mass-normalized floor gives a nonnegative
quadratic form with a null vector. Its mixed form vanishes at that vector.
Compact negative-support tests lie in the actual Gamma domain.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri

/-- Every compactly supported negative-half-line C² profile has finite full energy. -/
theorem criticalHalfLineEnergyDomain_of_compact_negative {G : ℝ → ℝ}
    (hG : ContDiff ℝ 2 G) (hc : HasCompactSupport G)
    (hs : ∀ u, 0 ≤ u → G u = 0) : CriticalHalfLineEnergyDomain G := by
  have hsq : HasCompactSupport (fun u => G u ^ 2) := by
    have heq : (fun u => G u ^ 2) = G * G := by funext u; exact pow_two (G u)
    rw [heq]
    exact hc.mul_right
  exact ⟨hG.continuous.measurable,
    hG.continuous.integrable_of_hasCompactSupport hc,
    (hG.continuous.pow 2).integrable_of_hasCompactSupport hsq,
    ((hG.continuous.pow 2).mul (by fun_prop)).integrable_of_hasCompactSupport hsq.mul_right,
    hs, _root_.RHTower.integrable_normSq_paperFT_mul_gammaBracket hG hc⟩

private theorem linear_eq_zero_of_nonnegative_quadratic {A B : ℝ} (hA : 0 ≤ A)
    (h : ∀ c : ℝ, 0 ≤ 2 * c * B + c ^ 2 * A) : B = 0 := by
  have hden : A + 1 ≠ 0 := by linarith only [hA]
  have he : (2 * (-B / (A + 1)) * B + (-B / (A + 1)) ^ 2 * A) * (A + 1) ^ 2 =
      -(A + 2) * B ^ 2 := by
    field_simp
    ring
  have hp := mul_nonneg (h (-B / (A + 1))) (sq_nonneg (A + 1))
  rw [he] at hp
  nlinarith only [hp, mul_nonneg hA (sq_nonneg B), sq_nonneg B]

/-- Every confining minimizer solves its full-domain weak eigenvalue equation. -/
theorem IsHalfLineEnergyMinimizer.weakEquation
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F)
    {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) :
    criticalHalfLineMixedEnergy R F G = criticalHalfLineGroundEnergy R * (∫ u, F u * G u) := by
  apply sub_eq_zero.mp
  apply linear_eq_zero_of_nonnegative_quadratic
    (sub_nonneg.mpr (criticalHalfLineGroundEnergy_mul_mass_le_all hR hG))
  intro c
  have hp := criticalHalfLineGroundEnergy_mul_mass_le_all hR (hF.1.add_const_mul hG c)
  rw [criticalHalfLineFullEnergy_add_const_mul R hF.1 hG,
    criticalHalfLine_square_mass_add_const_mul hF.1 hG, hF.2.1, hF.2.2] at hp
  nlinarith only [hp]

/-- The mixed form changes only through its exponential cross integral. -/
theorem criticalHalfLineMixedEnergy_change_ratio (R S : ℝ) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    criticalHalfLineMixedEnergy R F G = criticalHalfLineMixedEnergy S F G +
      (criticalAliasCoefficient R - criticalAliasCoefficient S) * criticalHalfLineExponentialPair F G := by
  have hR := criticalHalfLineFullEnergy_add_const_mul R hF hG 1
  have hS := criticalHalfLineFullEnergy_add_const_mul S hF hG 1
  have hsum := criticalHalfLineFullEnergy_change_ratio R S (hF.add_const_mul hG 1)
  have hfirst := criticalHalfLineFullEnergy_change_ratio R S hF
  have hsecond := criticalHalfLineFullEnergy_change_ratio R S hG
  have hweight := criticalHalfLine_exponential_mass_add_const_mul hF hG 1
  rw [hsum, hfirst, hsecond, hS, hweight] at hR
  nlinarith only [hR]

/-- The confinement coefficient is a fixed positive numerator divided by the ratio. -/
theorem criticalAliasCoefficient_eq_div (R : ℝ) :
    criticalAliasCoefficient R = criticalAliasCoefficient 1 / R := by
  simp only [criticalAliasCoefficient, mul_one, div_div]

theorem criticalAliasCoefficient_injective_positive {R S : ℝ}
    (hR : 0 < R) (hS : 0 < S)
    (he : criticalAliasCoefficient R = criticalAliasCoefficient S) : R = S := by
  have hmass : criticalAliasCoefficient R * R = criticalAliasCoefficient S * S := by
    rw [criticalAliasCoefficient_eq_div R, criticalAliasCoefficient_eq_div S]
    field_simp [hR.ne', hS.ne']
  rw [← he] at hmass
  have hp : criticalAliasCoefficient R * (R - S) = 0 := by nlinarith only [hmass]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (criticalAliasCoefficient_positive hR).ne')

#print axioms IsHalfLineEnergyMinimizer.weakEquation

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
