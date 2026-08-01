import GaloisForLFunctions.RHTower.SoninShellCutHighSlackVanishing

/-!
# The scale that fixes the product

Tying the scale to the number of annuli so that half-width times scale is a prescribed constant
makes the two quantities that govern the schedule-driven slack terms exactly constant: the gap
becomes that constant times the difference of carrier ratio and inner radius, and the high-side
product becomes it times the outer radius.

The scale then grows linearly with the number of annuli, so every largeness condition the coupling
needs — scale above one, carrier past the outer radius, aperture reached — holds once the cut is
fine enough.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open Filter
open scoped Topology

/-- The scale pairing a cut of `N` annuli with the prescribed product `κ`. -/
def soninShellCutScale (b c : ℝ) (N : ℕ) (κ : ℝ) : ℝ := κ * (2 * N) / (c - b)

/-- **The product is exactly the prescribed constant.** -/
theorem soninShellCutWidth_mul_scale (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) (κ : ℝ) :
    soninShellCutWidth b c N * soninShellCutScale b c N κ = κ := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hne : c - b ≠ 0 := by linarith
  rw [soninShellCutWidth, soninShellCutScale]
  field_simp

theorem soninShellCutScale_pos (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) {κ : ℝ}
    (hκ : 0 < κ) : 0 < soninShellCutScale b c N κ := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [soninShellCutScale]
  apply div_pos (by positivity)
  linarith

/-- **The scale grows with the cut.**  Every largeness condition on the scale is met once the cut is
fine enough. -/
theorem tendsto_soninShellCutScale_atTop (b c : ℝ) (hbc : b < c) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun N : ℕ => soninShellCutScale b c N κ) atTop atTop := by
  have hcoef : (0 : ℝ) < κ * 2 / (c - b) := by
    have : (0 : ℝ) < c - b := by linarith
    positivity
  have hbase : Tendsto (fun N : ℕ => κ * 2 / (c - b) * (N : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hcoef tendsto_natCast_atTop_atTop
  refine hbase.congr fun N => ?_
  rw [soninShellCutScale]
  ring

/-- The gap at the inner aperture is the prescribed constant times the ratio difference. -/
theorem soninShellCutWidth_mul_gap (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) (κ a q : ℝ) :
    soninShellCutWidth b c N * (soninShellCutScale b c N κ * (q - a)) = κ * (q - a) := by
  have h := soninShellCutWidth_mul_scale b c hbc hN κ
  calc soninShellCutWidth b c N * (soninShellCutScale b c N κ * (q - a))
      = soninShellCutWidth b c N * soninShellCutScale b c N κ * (q - a) := by ring
    _ = κ * (q - a) := by rw [h]

/-- The high-side product is the prescribed constant times the outer radius. -/
theorem soninShellCutWidth_mul_outer (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) (κ : ℝ) :
    soninShellCutWidth b c N * (soninShellCutScale b c N κ * b) = κ * b := by
  have h := soninShellCutWidth_mul_scale b c hbc hN κ
  calc soninShellCutWidth b c N * (soninShellCutScale b c N κ * b)
      = soninShellCutWidth b c N * soninShellCutScale b c N κ * b := by ring
    _ = κ * b := by rw [h]

end RHTower
