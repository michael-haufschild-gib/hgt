import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TypicalHeightHalfGaussReality
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TypicalHeightErrorDecay

/-!
# Uniform small-heat reality near typical heights

The dyadic source scale is comparable to the horizontal saddle slope.
Consequently the explicit error bounds are simultaneously small for
every heat time with `16η ≤ 2tα ≤ 2` and every nearby height.
-/

open Complex Filter Topology Set MeasureTheory
open _root_.RHTower _root_.RHTower.DeBruijn
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- The dyadic logarithmic scale is bounded by eight times the saddle slope. -/
theorem dyadic_log_le_horizontalSlope {T X : ℝ} (hT : 8 ≤ T) (hTX : T ≤ 2 * X)
    (hX : 0 < X) (hα : 8 ≤ (horizontalSlope X).re) :
    1 + Real.log (4 * T) ≤ 8 * (horizontalSlope X).re := by
  have ha : (horizontalSlope X).re = (Real.log X - Real.log (2 * Real.pi)) / 2 := by
    rw [horizontalSlope_re, Real.log_div hX.ne' (by positivity)]
  have hL := Real.log_le_log (show 0 < 4 * T by linarith only [hT])
    (show 4 * T ≤ 8 * X by linarith only [hTX])
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hX.ne'] at hL
  have h8 : Real.log 8 ≤ 7 := by
    simpa using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
  have hp0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith only [Real.pi_gt_three])
  have hp7 : Real.log (2 * Real.pi) ≤ 7 :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith only [Real.pi_lt_four])
  linarith only [hL, h8, hp0, hp7, ha, hα]

/-- At sufficiently large typical heights, the whole small-heat interval has no nonreal zeros. -/
theorem eventually_riemannHeat_ne_zero_of_zetaPolylogTypical {η : ℝ}
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∀ᶠ T : ℝ in atTop, ∀ t : ℝ, zetaTypicalHeight η (zetaPolylogLevel T) T t →
      ∀ X : ℝ, |X - t| ≤ η → ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 8 →
      16 * η ≤ 2 * τ * (horizontalSlope X).re → 2 * τ * (horizontalSlope X).re ≤ 2 →
      ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 / 2 → riemannHeat τ ((X : ℂ) + I * y) ≠ 0 := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp (eventually_typicalHalfGaussErrors_small hη hη8)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    (tendsto_horizontalSlope_re.eventually_ge_atTop (max A 8))
  filter_upwards [eventually_ge_atTop (max X₀ 200 + 2), eventually_ge_atTop (8 : ℝ)]
    with T hTbig hT
  intro t h X hXt τ hτ hτ8 hc hc2 y hy hy2
  have hXt' := (abs_le.mp hXt).1
  have hTX : T - 1 ≤ X := by linarith only [h.1.1, hXt', hη8]
  have hXm : max X₀ 200 ≤ X := by linarith only [hTbig, hTX]
  have hX : 200 ≤ X := (le_max_right _ _).trans hXm
  have hαm := hX₀ X ((le_max_left _ _).trans hXm)
  have hαA : A ≤ (horizontalSlope X).re := (le_max_left _ _).trans hαm
  have hα8 : 8 ≤ (horizontalSlope X).re := (le_max_right _ _).trans hαm
  have hscale := dyadic_log_le_horizontalSlope hT (by linarith only [hTX, hT])
    (by linarith only [hX]) hα8
  obtain ⟨hE, hS, hO⟩ := hA _ hαA T τ hT hscale hτ hτ8 hc hc2
  exact riemannHeat_ne_zero_of_typical_errors h hη hη8 hT hX hXt hτ hτ8
    (by linarith only [hα8]) hc hc2 hy hy2
    (window_fits hτ8 hτ (by linarith only [hX]) (by linarith only [hα8])) hE hS hO

#print axioms eventually_riemannHeat_ne_zero_of_zetaPolylogTypical

end

end GaloisForLFunctions.ZeroConfigurationGeometry
