import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainAverageDecay
import GaloisForLFunctions.RHTower.XiRightDiscAdjointSeamSupremum

/-!
# The unconditional three-quarter ceiling for averaged Narain decay

Hardy supplies a critical-line xi zero. Its pole survives in every fixed target
average and rules out every stronger power remainder, independently of RH.
-/

open Complex RHTower Set Filter Topology Asymptotics
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Hardy's critical-line zero gives an unconditional three-quarter ceiling
for every fixed averaged scalar source, whatever main terms are subtracted. -/
theorem narainScalarHeatAverage_no_better_than_three_quarters (Y Z : Height)
    {α : ℝ} (hα : 3 / 4 < α) :
    ¬ ∃ a b : ℂ,
      (fun y : ℝ => (y : ℂ) * narainScalarHeatAverage Y Z y -
        (a * (Real.log y : ℂ) + b)) =O[𝓝[>] 0] (fun y : ℝ => y ^ α) := by
  obtain ⟨ρ, hre, hzero⟩ := RHTower.XiSeamSupremum.exists_xi_zero_on_line
  let p : Resonance := ⟨(ρ - 1) / 2, by
    rw [show 1 + 2 * ((ρ - 1) / 2) = ρ by ring]
    exact hzero⟩
  have hp : p.val.re = -(1 / 4 : ℝ) := by norm_num [p, hre]
  exact narainScalarHeatAverage_no_faster_decay p Y Z
    (by rw [hp]; linarith only [hα])

#print axioms narainScalarHeatAverage_no_better_than_three_quarters
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
