import GaloisForLFunctions.RHTower.SoninShellCutScale

/-!
# The slack under the scale that fixes the product

Substituting the scale tied to the cut turns the two schedule-driven slack terms into expressions in
the prescribed constant alone: the gap becomes that constant times the difference of carrier ratio
and inner radius, the high-side product becomes it times the outer radius, and neither mentions the
number of annuli.

Only the outer term still moves with the cut, and it moves the right way.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open scoped FourierTransform

/-- **The middle slack under the scale.**  A constant of the shell and the prescribed product. -/
theorem sqrt_soninShellCutSharpBandBoundAt_div_floor_middle_scale
    (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) (a q κ : ℝ) (ha : 0 < a) (haq : a < q)
    (hκ : 0 < κ) :
    Real.sqrt (soninShellCutSharpBandBoundAt b c N
          (soninShellCutScale b c N κ * q) (soninShellCutScale b c N κ * a)) /
        soninShellCutNormFloor b c N =
      2 * (2 * (1 + 2 * soninRefTailSup 0 / (∫ y : ℝ, soninUnitBumpData y))) *
        (Real.sqrt (a / ((q - a) * ∫ y : ℝ, soninUnitBumpSq y) * (κ * (q - a))) *
          soninRefTailSup (κ * (q - a))) := by
  have hr : 0 < soninShellCutScale b c N κ := soninShellCutScale_pos b c hbc hN hκ
  rw [sqrt_soninShellCutSharpBandBoundAt_div_floor_middle b c hbc hN a q
      (soninShellCutScale b c N κ) ha haq hr,
    soninShellCutWidth_mul_gap b c hbc hN κ a q]

/-- **The high-side slack under the scale.**  A single root in the prescribed product. -/
theorem sqrt_soninShellCutHighBoundAt_div_floor_scale
    (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) {K : ℝ} (hK : 0 ≤ K) {N₀ : ℕ} (hN₀ : 1 ≤ N₀)
    {κ : ℝ} (hκ : 0 < κ) (hb : 0 < b) :
    Real.sqrt (soninShellCutHighBoundAt b c N K N₀ (soninShellCutScale b c N κ * b)) /
        soninShellCutNormFloor b c N =
      Real.sqrt (4 * K / (((2 * N₀ : ℝ) - 1) * ∫ y : ℝ, soninUnitBumpSq y) *
        (κ * b) ^ (1 - (2 * N₀ : ℝ))) := by
  have hr : 0 < soninShellCutScale b c N κ := soninShellCutScale_pos b c hbc hN hκ
  have ht : 0 < soninShellCutScale b c N κ * b := by positivity
  rw [sqrt_soninShellCutHighBoundAt_div_floor_product b c hbc hN hK hN₀ ht,
    soninShellCutWidth_mul_outer b c hbc hN κ]

/-- **The outer slack under the scale.**  The majorant at a gap that stays bounded, times a root
that vanishes with the cut. -/
theorem sqrt_soninShellCutSharpBandBoundAt_div_floor_outer_scale
    (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) (q κ : ℝ) (hb : 0 ≤ b) :
    Real.sqrt (soninShellCutSharpBandBoundAt b c N (soninShellCutScale b c N κ * q) b) /
        soninShellCutNormFloor b c N =
      2 * (2 * (1 + 2 * soninRefTailSup 0 / (∫ y : ℝ, soninUnitBumpData y))) *
        (soninRefTailSup (soninShellCutWidth b c N * (soninShellCutScale b c N κ * q - b)) *
          Real.sqrt (soninShellCutWidth b c N * b / ∫ y : ℝ, soninUnitBumpSq y)) :=
  sqrt_soninShellCutSharpBandBoundAt_div_floor_outer b c hbc hN
    (soninShellCutScale b c N κ * q) hb

end RHTower
