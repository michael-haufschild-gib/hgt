import GaloisForLFunctions.RHTower.Sieve.GenericFibreStepOne
import GaloisForLFunctions.RHTower.Sieve.ScaledBudgetLimit
import GaloisForLFunctions.RHTower.Sieve.ScaledTwoRangeWindow

/-!
# Step 1 of the reciprocal-marker Hall law at a shrunk window

The Möbius fibre mean square holds at every window `c·exp((log x)^β)` with `0 < c ≤ 1` and
`0 < β < 1`, so the three conclusions of `Sieve/GenericFibreStepOne` hold there verbatim.  A
shrunk window is what a marker block at a lifted scale needs: the cofactor scale of the `k`-th
dyadic block of markers is `x/4^k`, and the cell it has to fill is shorter by exactly `2^{-k}`.
-/

namespace RHTower.Sieve

open Finset Filter Topology ArithmeticFunction

/-- The Möbius fibre mean square at a shrunk window, at every exponent. -/
theorem averagedMeanSquare_moebius_scaled {c β : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    AveragedMeanSquare (fun n => ((moebius n : ℤ) : ℝ)) (scaledLength c β) :=
  averagedMeanSquare_moebius_scaledLength_all hc0 hc1 hβ0 hβ1

/-- The shrunk window is small against the outer scale. -/
theorem tendsto_scaledLength_div_sqrt {c β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun x : ℝ => scaledLength c β x / Real.sqrt x) atTop (𝓝 0) := by
  have h := tendsto_rpow_log_mul_scaledLength_div_sqrt (c := c) hβ0 hβ1 0
  simpa using h

/-- **Step 1 with a growing truncation level, at a shrunk window.** -/
theorem eventually_fibre_step_one_growing_scaled {c β : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      ((outerBlock x (scaledLength c β x)).card : ℝ)
        ≤ (((outerBlock x (scaledLength c β x)).filter (fun a =>
            (3 / 16) * squarefreeDensity * (fibreLen x (scaledLength c β x) a : ℝ)
                ≤ (((Finset.Ioc (fibreStartIdx x a)
                    (fibreStartIdx x a + fibreLen x (scaledLength c β x) a)).filter
                    (fun n => moebius n = 1)).card : ℝ)
              ∧ (3 / 16) * squarefreeDensity * (fibreLen x (scaledLength c β x) a : ℝ)
                ≤ (((Finset.Ioc (fibreStartIdx x a)
                    (fibreStartIdx x a + fibreLen x (scaledLength c β x) a)).filter
                    (fun n => moebius n = -1)).card : ℝ))).card : ℝ)
          + 1024 * ε * Real.sqrt x / squarefreeDensity ^ 2
          + Real.sqrt x / (Real.log x) ^ 2 := by
  have hβ0' : (0 : ℝ) < β := hβ0
  exact eventually_fibre_step_one_growing_gen
    (averagedMeanSquare_moebius_scaled hc0 hc1 hβ0 hβ1)
    (tendsto_scaledLength hc0 hβ0')
    (tendsto_scaledLength_div_sqrt hβ0' hβ1)
    (tendsto_rpow_log_div_scaledLength hc0 hβ0' 3) hε

/-- **A positive proportion of the fibres is good at a shrunk window.** -/
theorem eventually_fibre_step_one_positive_scaled {c β : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop,
      (3 / 4) * Real.sqrt x
        ≤ (((outerBlock x (scaledLength c β x)).filter (fun a =>
            (3 / 16) * squarefreeDensity * (fibreLen x (scaledLength c β x) a : ℝ)
                ≤ (((Finset.Ioc (fibreStartIdx x a)
                    (fibreStartIdx x a + fibreLen x (scaledLength c β x) a)).filter
                    (fun n => moebius n = 1)).card : ℝ)
              ∧ (3 / 16) * squarefreeDensity * (fibreLen x (scaledLength c β x) a : ℝ)
                ≤ (((Finset.Ioc (fibreStartIdx x a)
                    (fibreStartIdx x a + fibreLen x (scaledLength c β x) a)).filter
                    (fun n => moebius n = -1)).card : ℝ))).card : ℝ) := by
  have hβ0' : (0 : ℝ) < β := hβ0
  exact eventually_fibre_step_one_positive_gen
    (averagedMeanSquare_moebius_scaled hc0 hc1 hβ0 hβ1)
    (tendsto_scaledLength hc0 hβ0')
    (tendsto_scaledLength_div_sqrt hβ0' hβ1)
    (tendsto_rpow_log_div_scaledLength hc0 hβ0' 3)

end RHTower.Sieve
