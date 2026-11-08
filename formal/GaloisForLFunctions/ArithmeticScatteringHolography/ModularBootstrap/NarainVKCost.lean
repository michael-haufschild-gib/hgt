import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainVKParameters
import GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux.VinogradovKorobovCapsAndStageReceivers

/-!
# Logarithmic bounds for the arithmetic contour cost

The zero-free width eventually dominates a reciprocal logarithm. This bounds
the reciprocal-zeta cost by a fixed logarithmic power.
-/

open RHTower Filter Topology
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

private theorem tendsto_double_add_one_atTop :
    Tendsto (fun T : ℝ => 2 * T + 1) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b, eventually_ge_atTop (0 : ℝ)] with T hb hT
  linarith only [hb, hT]

/-- The existing logarithmic lower bound for the arithmetic width also bounds its reciprocal cost. -/
theorem eventually_narainVKCost_le_log_power :
    ∀ᶠ T : ℝ in atTop,
      narainVKCost T ≤ 3 ^ (7 : ℕ) * Real.log (2 * T + 1) ^ (14 : ℕ) := by
  have hlin := tendsto_double_add_one_atTop
  have hwidth := hlin.eventually
    GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux.eventually_inv_log_le_vkWidth
  have hheight := hlin.eventually_ge_atTop (Real.exp (Real.exp 1))
  filter_upwards [hwidth, hheight] with T hw hT
  change 1 / Real.log (2 * T + 1) ≤ vkHadamardWidth (2 * T + 1) at hw
  have hlog : Real.exp 1 ≤ Real.log (2 * T + 1) := by
    rw [← Real.log_exp (Real.exp 1)]
    exact Real.log_le_log (Real.exp_pos _) hT
  have he := Real.add_one_le_exp (1 : ℝ)
  have hlog1 : 1 ≤ Real.log (2 * T + 1) := by linarith only [he, hlog]
  have hlog0 : 0 < Real.log (2 * T + 1) := zero_lt_one.trans_le hlog1
  have hw0 := vkHadamardWidth_pos hT
  have hinv : (vkHadamardWidth (2 * T + 1))⁻¹ ≤ Real.log (2 * T + 1) := by
    have h := inv_anti₀ (one_div_pos.mpr hlog0) hw
    simpa only [one_div, inv_inv] using h
  have hfactor : 1 + 2 / vkHadamardWidth (2 * T + 1) ≤ 3 * Real.log (2 * T + 1) := by
    rw [div_eq_mul_inv]
    linarith only [hinv, hlog1]
  unfold narainVKCost
  calc
    _ ≤ Real.log (2 * T + 1) ^ 7 * (3 * Real.log (2 * T + 1)) ^ 7 := by gcongr
    _ = _ := by ring

/-- Every positive fixed fraction of the raw width still dominates a reciprocal logarithm. -/
theorem eventually_narainVKWidth_ge_inv_log {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop,
      min δ 1 / (8 * Real.log (2 * T + 1)) ≤ narainVKWidth δ T := by
  have hlin := tendsto_double_add_one_atTop
  have hwidth := hlin.eventually
    GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux.eventually_inv_log_le_vkWidth
  filter_upwards [hwidth, hlin.eventually_ge_atTop (Real.exp (Real.exp 1))] with T hw hT
  change 1 / Real.log (2 * T + 1) ≤ vkHadamardWidth (2 * T + 1) at hw
  have h := mul_le_mul_of_nonneg_left hw (show 0 ≤ min δ 1 / 8 by positivity)
  calc
    _ = min δ 1 / 8 * (1 / Real.log (2 * T + 1)) := by ring
    _ ≤ min δ 1 / 8 * vkHadamardWidth (2 * T + 1) := h
    _ ≤ _ := narainVKWidth_ge_fraction hδ hT

#print axioms eventually_narainVKCost_le_log_power
#print axioms eventually_narainVKWidth_ge_inv_log
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
