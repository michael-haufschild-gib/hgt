import GaloisForLFunctions.RHTower.SoninShellCutSlackClosedForm

/-!
# The high-side slack in closed form

The high-side term of the budget divided by the floor is again a single root, and the half-width
cancels once against the floor: what remains under the root is the decay constant times the
half-width, against the half-width to the doubled order, the band radius to the negative order, and
the reference square's mass.

Together with the band slack this gives every term of the schedule's slack condition in closed form.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open scoped FourierTransform

theorem soninShellCutHighBoundAt_nonneg (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N)
    {K : ℝ} (hK : 0 ≤ K) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ soninShellCutHighBoundAt b c N K N₀ t := by
  have hδ := soninShellCutWidth_pos b c hbc hN
  have hord : (1 : ℝ) < (2 * N₀ : ℝ) := by
    have : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀
    linarith
  have hrp : (0 : ℝ) ≤ t ^ (1 - (2 * N₀ : ℝ)) := Real.rpow_nonneg ht _
  rw [soninShellCutHighBoundAt]
  have h1 : (0 : ℝ) ≤ K * soninShellCutWidth b c N ^ 2 /
      soninShellCutWidth b c N ^ (2 * N₀) := by positivity
  have h2 : (0 : ℝ) ≤ t ^ (1 - (2 * N₀ : ℝ)) / ((2 * N₀ : ℝ) - 1) := by
    apply div_nonneg hrp
    linarith
  positivity

/-- **The high-side slack.**  One root, with the half-width cancelled once against the floor. -/
theorem sqrt_soninShellCutHighBoundAt_div_floor
    (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) {K : ℝ} (hK : 0 ≤ K) {N₀ : ℕ} (hN₀ : 1 ≤ N₀)
    {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (soninShellCutHighBoundAt b c N K N₀ t) / soninShellCutNormFloor b c N =
      Real.sqrt (4 * K * soninShellCutWidth b c N * t ^ (1 - (2 * N₀ : ℝ)) /
        (soninShellCutWidth b c N ^ (2 * N₀) * ((2 * N₀ : ℝ) - 1) *
          ∫ y : ℝ, soninUnitBumpSq y)) := by
  have hδ := soninShellCutWidth_pos b c hbc hN
  have hI : (0 : ℝ) < ∫ y : ℝ, soninUnitBumpSq y := integral_soninUnitBumpSq_pos
  have hord : (1 : ℝ) < (2 * N₀ : ℝ) := by
    have : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀
    linarith
  have hhigh := soninShellCutHighBoundAt_nonneg b c hbc hN hK hN₀ ht
  rw [soninShellCutNormFloor, ← Real.sqrt_div hhigh]
  congr 1
  rw [soninShellCutHighBoundAt]
  have hδne : soninShellCutWidth b c N ≠ 0 := hδ.ne'
  have hδpow : soninShellCutWidth b c N ^ (2 * N₀) ≠ 0 := by positivity
  have hordne : ((2 * N₀ : ℝ) - 1) ≠ 0 := by linarith
  have hIne : (∫ y : ℝ, soninUnitBumpSq y) ≠ 0 := hI.ne'
  field_simp
  ring

end RHTower
