import GaloisForLFunctions.RHTower.DeBruijnNewmanEnergyTransition
import GaloisForLFunctions.RHTower.XiCenteredOrderTwentyThreeSourceBudgetClosure
import GaloisForLFunctions.RHTower.PrimeArchExplicitCircleStateReflection
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockMaxGrowthRate

/-!
# The de Bruijn–Newman energy law up to unit time

The growth constant of the Hadamard approximants is `S = 2 Σ_ρ |ρ − ½|⁻² < 1/10`
(`xiApproxGrowth_lt`): the inverse-square mass of the zeros is at most `85/84` times the
zeroth normalized prime–archimedean moment, which is below `0.04623`.  Hence the horizon
`8 S t < 1` holds for all `0 < t ≤ 1`, which contains the whole nontrivial range `0 < t < 1/8`
(for `t ≥ 1/8` every zero of `H_t` is real).  So the energy law holds there without a horizon
hypothesis (`riemannHeat_upper_energy_le_of_le_one`).
-/

namespace RHTower.DeBruijn

noncomputable section

theorem xiApproxGrowth_eq : xiApproxGrowth = 2 * xiShiftAbsoluteMass 0 := by
  rw [xiApproxGrowth, ← tsum_norm_inv_xiSpectralPoint_sq]
  congr 1
  refine tsum_congr fun q => ?_
  rw [norm_inv, inv_pow, one_div]

/-- **The growth constant is below `1/10`.** -/
theorem xiApproxGrowth_lt : xiApproxGrowth < 1 / 10 := by
  rw [xiApproxGrowth_eq]
  have h1 := eightyFour_div_eightyFive_mul_xiShiftAbsoluteMass_zero_le_head
  have h2 :=
    normalizedPrimeArchMoment_zero_lt_fourThousandSixHundredTwentyThree_over_oneHundredThousand
  linarith

/-- **Energy dissipation along the de Bruijn–Newman flow for `0 < t ≤ 1`.** -/
theorem riemannHeat_upper_energy_le_of_le_one {t c K : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hc : 0 ≤ c)
    (hK : ∀ T : Finset XiZeroCopy,
      ∑ q ∈ T.filter (fun q => 0 < (xiSpectralPoint q).im),
        max ((xiSpectralPoint q).im ^ 2 - 2 * t - c) 0 ≤ K)
    (Z : Finset ℂ) :
    ∑ w ∈ Z, (GaloisForLFunctions.HTGeometry.zeroMult (riemannHeat t) w : ℝ) *
      max ((max w.im 0) ^ 2 - c) 0 ≤ K := by
  have hS := xiApproxGrowth_lt
  have hS0 := xiApproxGrowth_nonneg
  refine riemannHeat_upper_energy_le ht ?_ hc hK Z
  nlinarith

end

end RHTower.DeBruijn
