import GaloisForLFunctions.HTGeometry.VerticalStripContourShift

/-!
# Shifting a vertical contour along a sequence of heights

The contour shift of `VerticalStripContourShift` asks the horizontal edges to vanish along the whole
filter `atTop`.  When only an `L¹` bound on the horizontal mass is available the edges are known to
vanish along *some* sequence of heights, which is already enough: Cauchy's theorem holds at every
height, so it suffices to pass to the limit along that sequence.

## Main results

* `integral_vertical_line_eq_of_horizontal_tendsto_seq`
-/

open Complex MeasureTheory Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

/-- **Contour shift between two vertical lines, along a sequence of heights.** -/
theorem integral_vertical_line_eq_of_horizontal_tendsto_seq {G : ℂ → ℂ} {c d : ℝ} (hcd : c ≤ d)
    (hdiff : DifferentiableOn ℂ G (verticalStrip c d))
    (hc : Integrable fun y : ℝ => G ((c : ℂ) + (y : ℝ) * I))
    (hd : Integrable fun y : ℝ => G ((d : ℂ) + (y : ℝ) * I))
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (hbot : Tendsto (fun n : ℕ => ∫ u in c..d, G ((u : ℂ) + ((-(T n) : ℝ) : ℂ) * I)) atTop (𝓝 0))
    (htop : Tendsto (fun n : ℕ => ∫ u in c..d, G ((u : ℂ) + ((T n : ℝ) : ℂ) * I)) atTop (𝓝 0)) :
    (∫ y : ℝ, G ((d : ℂ) + (y : ℝ) * I)) = ∫ y : ℝ, G ((c : ℂ) + (y : ℝ) * I) := by
  have hrect : ∀ S : ℝ,
      ((∫ x : ℝ in c..d, G ((x : ℂ) + ((-S : ℝ) : ℂ) * I))
          - (∫ x : ℝ in c..d, G ((x : ℂ) + ((S : ℝ) : ℂ) * I))
          + I • (∫ y : ℝ in (-S)..S, G ((d : ℂ) + (y : ℝ) * I)))
        - I • (∫ y : ℝ in (-S)..S, G ((c : ℂ) + (y : ℝ) * I)) = 0 := by
    intro S
    have hz : ((c : ℂ) + ((-S : ℝ) : ℂ) * I).re = c := by simp
    have hz' : ((c : ℂ) + ((-S : ℝ) : ℂ) * I).im = -S := by simp
    have hw : ((d : ℂ) + ((S : ℝ) : ℂ) * I).re = d := by simp
    have hw' : ((d : ℂ) + ((S : ℝ) : ℂ) * I).im = S := by simp
    have hsub : DifferentiableOn ℂ G
        (uIcc ((c : ℂ) + ((-S : ℝ) : ℂ) * I).re ((d : ℂ) + ((S : ℝ) : ℂ) * I).re ×ℂ
          uIcc ((c : ℂ) + ((-S : ℝ) : ℂ) * I).im ((d : ℂ) + ((S : ℝ) : ℂ) * I).im) := by
      rw [hz, hz', hw, hw']
      exact hdiff.mono (rect_subset_verticalStrip hcd S)
    have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
      ((c : ℂ) + ((-S : ℝ) : ℂ) * I) ((d : ℂ) + ((S : ℝ) : ℂ) * I) hsub
    rw [hz, hz', hw, hw'] at hcauchy
    exact hcauchy
  have hlimd : Tendsto (fun n : ℕ => ∫ y : ℝ in (-(T n))..(T n), G ((d : ℂ) + (y : ℝ) * I)) atTop
      (𝓝 (∫ y : ℝ, G ((d : ℂ) + (y : ℝ) * I))) :=
    intervalIntegral_tendsto_integral hd (tendsto_neg_atTop_atBot.comp hT) hT
  have hlimc : Tendsto (fun n : ℕ => ∫ y : ℝ in (-(T n))..(T n), G ((c : ℂ) + (y : ℝ) * I)) atTop
      (𝓝 (∫ y : ℝ, G ((c : ℂ) + (y : ℝ) * I))) :=
    intervalIntegral_tendsto_integral hc (tendsto_neg_atTop_atBot.comp hT) hT
  have hcomb := ((hbot.sub htop).add (hlimd.const_smul I)).sub (hlimc.const_smul I)
  have hzero : Tendsto (fun n : ℕ =>
      ((∫ x : ℝ in c..d, G ((x : ℂ) + ((-(T n) : ℝ) : ℂ) * I))
          - (∫ x : ℝ in c..d, G ((x : ℂ) + ((T n : ℝ) : ℂ) * I))
          + I • (∫ y : ℝ in (-(T n))..(T n), G ((d : ℂ) + (y : ℝ) * I)))
        - I • (∫ y : ℝ in (-(T n))..(T n), G ((c : ℂ) + (y : ℝ) * I))) atTop (𝓝 0) := by
    simp only [hrect]
    exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hcomb hzero
  have hI : I * ((∫ y : ℝ, G ((d : ℂ) + (y : ℝ) * I)) - ∫ y : ℝ, G ((c : ℂ) + (y : ℝ) * I))
      = I * 0 := by
    rw [mul_zero, mul_sub]
    simpa [smul_eq_mul] using heq
  have hcancel := mul_left_cancel₀ Complex.I_ne_zero hI
  linear_combination hcancel

end GaloisForLFunctions.HTGeometry
