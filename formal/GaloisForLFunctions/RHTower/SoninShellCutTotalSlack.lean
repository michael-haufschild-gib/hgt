import GaloisForLFunctions.RHTower.SoninShellCutSecondChoice

/-!
# The total slack under the schedule

The energy bound's hypothesis divides a sum of three roots by the floor, and division distributes,
so the total slack is the sum of the three quotients already computed.  Under the tied scale two of
them are functions of the prescribed product and the third of the cut.

The slack condition is therefore an inequality between one quantity chosen first, one chosen second,
and the threshold — with no remaining algebra between them.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open scoped FourierTransform

/-- Division distributes over the three roots. -/
theorem sum_div_three (A B C L : ℝ) : (A + B + C) / L = A / L + B / L + C / L := by
  field_simp

/-- **The total slack under the scale.**  Two terms in the prescribed product, one in the cut. -/
theorem totalSlack_scale_eq
    (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) (a q κ : ℝ) (ha : 0 < a) (haq : a < q)
    (hκ : 0 < κ) (hb : 0 < b) {K : ℝ} (hK : 0 ≤ K) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) :
    (Real.sqrt (soninShellCutHighBoundAt b c N K N₀ (soninShellCutScale b c N κ * b)) +
        Real.sqrt (soninShellCutSharpBandBoundAt b c N
          (soninShellCutScale b c N κ * q) (soninShellCutScale b c N κ * a)) +
        Real.sqrt (soninShellCutSharpBandBoundAt b c N
          (soninShellCutScale b c N κ * q) b)) / soninShellCutNormFloor b c N =
      Real.sqrt (4 * K / (((2 * N₀ : ℝ) - 1) * ∫ y : ℝ, soninUnitBumpSq y) *
          (κ * b) ^ (1 - (2 * N₀ : ℝ))) +
        2 * (2 * (1 + 2 * soninRefTailSup 0 / (∫ y : ℝ, soninUnitBumpData y))) *
          (Real.sqrt (a / ((q - a) * ∫ y : ℝ, soninUnitBumpSq y) * (κ * (q - a))) *
            soninRefTailSup (κ * (q - a))) +
        2 * (2 * (1 + 2 * soninRefTailSup 0 / (∫ y : ℝ, soninUnitBumpData y))) *
          (soninRefTailSup (soninShellCutWidth b c N *
              (soninShellCutScale b c N κ * q - b)) *
            Real.sqrt (soninShellCutWidth b c N * b / ∫ y : ℝ, soninUnitBumpSq y)) := by
  rw [sum_div_three, sqrt_soninShellCutHighBoundAt_div_floor_scale b c hbc hN hK hN₀ hκ hb,
    sqrt_soninShellCutSharpBandBoundAt_div_floor_middle_scale b c hbc hN a q κ ha haq hκ,
    sqrt_soninShellCutSharpBandBoundAt_div_floor_outer_scale b c hbc hN q κ hb.le]

end RHTower
