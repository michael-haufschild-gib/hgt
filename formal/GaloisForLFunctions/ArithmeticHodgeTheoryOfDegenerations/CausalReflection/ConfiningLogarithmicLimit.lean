import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningRescaledEnergy

/-!
# Convergence to the logarithmic variational floor

Fixed trials give the upper limit; the rescaled minimizing energy identity
gives the lower limit. The two nonnegative errors then vanish uniformly:
excess logarithmic energy and error in linearizing the potential.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- The actual ground energy has a universal constant after its linear and logarithmic terms. -/
theorem tendsto_renormalizedConfiningGroundEnergy :
    Tendsto renormalizedConfiningGroundEnergy atTop (𝓝 softLogarithmicHalfLineGroundEnergy) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨A, hA, hrem⟩ := exists_minimizer_remainder_lower (half_pos hε)
  filter_upwards [eventually_renormalizedConfiningGroundEnergy_lt hε,
    eventually_ge_atTop A] with a hupper ha
  have ha1 := hA.trans ha
  have ha0 := zero_lt_one.trans_le ha1
  obtain ⟨F, hF⟩ := exists_criticalHalfLineGroundEnergy_minimizer (confiningHalfLineRatio_pos ha0)
  have hg := hF.1.rescaled_softLogarithmic ha0
  have hm : (∫ u, rescaledConfiningProfile a F u ^ 2) = 1 := by
    rw [integral_sq_rescaledConfiningProfile ha0, hF.2.1]
  have hfloor := softLogarithmicHalfLineGroundEnergy_le hg hm
  have hp := hF.1.rescaled_potential_error_nonneg ha0
  have he := hF.rescaled_energy_identity ha1
  have hr := hrem ha hF
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith only [he, hr, hfloor, hp, hupper, hε]

/-- Rescaled minimizers approach the logarithmic floor, and their potential error vanishes uniformly. -/
theorem exists_minimizer_softLogarithmic_error_small {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {a : ℝ}, A ≤ a → ∀ {F : ℝ → ℝ},
      IsHalfLineEnergyMinimizer (confiningHalfLineRatio a) F →
      0 ≤ softLogarithmicHalfLineEnergy (rescaledConfiningProfile a F) -
        softLogarithmicHalfLineGroundEnergy ∧
      0 ≤ a * criticalHalfLineExponentialDefect F -
        8 * criticalHalfLineFirstMoment (rescaledConfiningProfile a F) ∧
      (softLogarithmicHalfLineEnergy (rescaledConfiningProfile a F) -
        softLogarithmicHalfLineGroundEnergy) +
        (a * criticalHalfLineExponentialDefect F -
          8 * criticalHalfLineFirstMoment (rescaledConfiningProfile a F)) < ε := by
  obtain ⟨A₀, hA₀, hrem⟩ := exists_minimizer_remainder_lower (half_pos hε)
  obtain ⟨A₁, hu⟩ := eventually_atTop.mp
    (eventually_renormalizedConfiningGroundEnergy_lt (half_pos hε))
  refine ⟨max A₀ A₁, hA₀.trans (le_max_left _ _), ?_⟩
  intro a ha F hF
  have hAa := (le_max_left _ _).trans ha
  have ha1 := hA₀.trans hAa
  have ha0 := zero_lt_one.trans_le ha1
  have hg := hF.1.rescaled_softLogarithmic ha0
  have hm : (∫ u, rescaledConfiningProfile a F u ^ 2) = 1 := by
    rw [integral_sq_rescaledConfiningProfile ha0, hF.2.1]
  refine ⟨sub_nonneg.mpr (softLogarithmicHalfLineGroundEnergy_le hg hm),
    hF.1.rescaled_potential_error_nonneg ha0, ?_⟩
  have he := hF.rescaled_energy_identity ha1
  have hr := hrem hAa hF
  have hh := hu a ((le_max_right _ _).trans ha)
  linarith only [he, hr, hh]

#print axioms tendsto_renormalizedConfiningGroundEnergy
#print axioms exists_minimizer_softLogarithmic_error_small
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
