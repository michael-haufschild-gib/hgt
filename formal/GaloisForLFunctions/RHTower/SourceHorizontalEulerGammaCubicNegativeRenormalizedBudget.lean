import GaloisForLFunctions.RHTower.SourceHorizontalEulerGammaCubicNegativeRenormalizedChannel
import GaloisForLFunctions.RHTower.SourceHorizontalWoldBVCompleteSplitPrimitiveBudgetFirewall

/-!
# Downstream budget consequences of the Euler--Gamma cubic negative channel

This module isolates heavyweight BV/Krein and Route-P dependencies from the source-local cubic
channel. Import it only when the compensated energy or Julia-orbit budget comparison is needed.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Gamma/Wold compensated BV energy with the source-forced four-orientation coefficient. -/
def sourceHorizontalWoldBVKreinEulerGammaCubicCompensatedEnergy
    (c : ℂ) (N : ℕ) : ℝ :=
  sourceHorizontalWoldBVKreinSignedSplitEnergy c N -
    8 * Complex.normSq c * sourceHorizontalEulerGammaCubicNormalizedMoment N

theorem tendsto_sourceHorizontalWoldBVKreinEulerGammaCubicCompensatedEnergy (c : ℂ) :
    Tendsto (sourceHorizontalWoldBVKreinEulerGammaCubicCompensatedEnergy c)
      atTop (nhds 0) := by
  have h := (tendsto_sourceHorizontalWoldBVKreinSignedSplitEnergy c).sub
    (tendsto_sourceHorizontalEulerGammaCubicNormalizedMoment.const_mul
      (8 * Complex.normSq c))
  convert h using 1
  · rfl
  · ring_nf

theorem sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_pos
    {c : ℂ} (hc : c ≠ 0) :
    0 < sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c := by
  rw [sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget]
  exact mul_pos
    (mul_pos (by norm_num) (Complex.normSq_pos.mpr hc))
    routePPrimitiveBaseCauchyCubicTraceBudget_pos

/-- The new cubic source channel removes the firewall asymptotically and enters every nonzero
literal primitive source budget cofinally. -/
theorem eventually_sourceHorizontalWoldBVKreinEulerGammaCubicCompensatedEnergy_lt_sourceBudget
    {c : ℂ} (hc : c ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      sourceHorizontalWoldBVKreinEulerGammaCubicCompensatedEnergy c N <
        sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c := by
  exact
    (tendsto_sourceHorizontalWoldBVKreinEulerGammaCubicCompensatedEnergy c).eventually_lt_const
      (sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_pos hc)

end

end RHTower
