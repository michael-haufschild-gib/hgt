import GaloisForLFunctions.RHTower.SoninShellCutOuterSlack
import GaloisForLFunctions.RHTower.SoninShellCutHighSlackClosedForm

/-!
# The high-side slack depends only on one product

Under the root, the half-width and the band radius appear to the same negative order, so they
combine: the whole radicand is a constant of the decay order times the product of half-width and
radius, raised to one minus twice the order.

So the high-side term is governed by that single product — not by the half-width and the radius
separately, and in particular not by refinement, since refining the cut shrinks the half-width and
the product only if the radius stays fixed.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open scoped FourierTransform

/-- **The radicand is a power of one product.**  Half-width and radius enter only through `δ t`. -/
theorem soninShellCutHighSlack_radicand_eq (δ t K I : ℝ) (hδ : 0 < δ) (ht : 0 < t)
    {N₀ : ℕ} (hN₀ : 1 ≤ N₀) :
    4 * K * δ * t ^ (1 - (2 * N₀ : ℝ)) / (δ ^ (2 * N₀) * ((2 * N₀ : ℝ) - 1) * I) =
      4 * K / (((2 * N₀ : ℝ) - 1) * I) * (δ * t) ^ (1 - (2 * N₀ : ℝ)) := by
  have hord : (1 : ℝ) < (2 * N₀ : ℝ) := by
    have : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀
    linarith
  have hsplit : (δ * t) ^ (1 - (2 * N₀ : ℝ)) =
      δ ^ (1 - (2 * N₀ : ℝ)) * t ^ (1 - (2 * N₀ : ℝ)) :=
    Real.mul_rpow hδ.le ht.le
  have hδpow : δ ^ (1 - (2 * N₀ : ℝ)) = δ / δ ^ (2 * N₀) := by
    rw [Real.rpow_sub hδ, Real.rpow_one]
    congr 1
    rw [show ((2 : ℝ) * (N₀ : ℝ)) = ((2 * N₀ : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [hsplit, hδpow]
  have hδne : δ ^ (2 * N₀) ≠ 0 := by positivity
  field_simp

/-- **The high-side slack in product form.** -/
theorem sqrt_soninShellCutHighBoundAt_div_floor_product
    (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) {K : ℝ} (hK : 0 ≤ K) {N₀ : ℕ} (hN₀ : 1 ≤ N₀)
    {t : ℝ} (ht : 0 < t) :
    Real.sqrt (soninShellCutHighBoundAt b c N K N₀ t) / soninShellCutNormFloor b c N =
      Real.sqrt (4 * K / (((2 * N₀ : ℝ) - 1) * ∫ y : ℝ, soninUnitBumpSq y) *
        (soninShellCutWidth b c N * t) ^ (1 - (2 * N₀ : ℝ))) := by
  rw [sqrt_soninShellCutHighBoundAt_div_floor b c hbc hN hK hN₀ ht.le]
  congr 1
  exact soninShellCutHighSlack_radicand_eq (soninShellCutWidth b c N) t K _
    (soninShellCutWidth_pos b c hbc hN) ht hN₀

end RHTower
