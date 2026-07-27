import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Shifting a vertical contour

A function holomorphic on a closed vertical strip, integrable on both edges and with vanishing
horizontal edges, has the same integral on the two vertical lines.

The proof is Cauchy's theorem on the rectangle `[c,d] × [-T,T]` followed by `T → ∞`: the two
horizontal sides tend to zero by hypothesis, and the two vertical sides converge to the full-line
integrals because they are integrable.
-/

open Complex MeasureTheory Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

/-- The closed vertical strip between the lines `Re s = c` and `Re s = d`. -/
def verticalStrip (c d : ℝ) : Set ℂ := {z : ℂ | c ≤ z.re ∧ z.re ≤ d}

theorem mem_verticalStrip {c d : ℝ} {z : ℂ} : z ∈ verticalStrip c d ↔ c ≤ z.re ∧ z.re ≤ d :=
  Iff.rfl

/-- Every rectangle over `[c,d]` lies in the strip. -/
theorem rect_subset_verticalStrip {c d : ℝ} (hcd : c ≤ d) (T : ℝ) :
    (uIcc c d) ×ℂ (uIcc (-T) T) ⊆ verticalStrip c d := by
  intro z hz
  rw [Complex.mem_reProdIm] at hz
  rw [uIcc_of_le hcd] at hz
  exact ⟨hz.1.1, hz.1.2⟩

/-- **Contour shift between two vertical lines.**  If `G` is holomorphic on the closed strip
`c ≤ Re s ≤ d`, integrable on both edges, and its horizontal edge integrals tend to zero, then its
integrals along the two lines agree. -/
theorem integral_vertical_line_eq_of_horizontal_tendsto {G : ℂ → ℂ} {c d : ℝ} (hcd : c ≤ d)
    (hdiff : DifferentiableOn ℂ G (verticalStrip c d))
    (hc : Integrable fun y : ℝ => G ((c : ℂ) + (y : ℝ) * I))
    (hd : Integrable fun y : ℝ => G ((d : ℂ) + (y : ℝ) * I))
    (hbot : Tendsto (fun T : ℝ => ∫ u in c..d, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ u in c..d, G ((u : ℂ) + ((T : ℝ) : ℂ) * I)) atTop (𝓝 0)) :
    (∫ y : ℝ, G ((d : ℂ) + (y : ℝ) * I)) = ∫ y : ℝ, G ((c : ℂ) + (y : ℝ) * I) := by
  -- Cauchy's theorem on the rectangle of half-height `T`
  have hrect : ∀ T : ℝ,
      ((∫ x : ℝ in c..d, G ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
          - (∫ x : ℝ in c..d, G ((x : ℂ) + ((T : ℝ) : ℂ) * I))
          + I • (∫ y : ℝ in (-T)..T, G ((d : ℂ) + (y : ℝ) * I)))
        - I • (∫ y : ℝ in (-T)..T, G ((c : ℂ) + (y : ℝ) * I)) = 0 := by
    intro T
    have hz : ((c : ℂ) + ((-T : ℝ) : ℂ) * I).re = c := by simp
    have hz' : ((c : ℂ) + ((-T : ℝ) : ℂ) * I).im = -T := by simp
    have hw : ((d : ℂ) + ((T : ℝ) : ℂ) * I).re = d := by simp
    have hw' : ((d : ℂ) + ((T : ℝ) : ℂ) * I).im = T := by simp
    have hsub : DifferentiableOn ℂ G
        (uIcc ((c : ℂ) + ((-T : ℝ) : ℂ) * I).re ((d : ℂ) + ((T : ℝ) : ℂ) * I).re ×ℂ
          uIcc ((c : ℂ) + ((-T : ℝ) : ℂ) * I).im ((d : ℂ) + ((T : ℝ) : ℂ) * I).im) := by
      rw [hz, hz', hw, hw']
      exact hdiff.mono (rect_subset_verticalStrip hcd T)
    have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
      ((c : ℂ) + ((-T : ℝ) : ℂ) * I) ((d : ℂ) + ((T : ℝ) : ℂ) * I) hsub
    rw [hz, hz', hw, hw'] at hcauchy
    exact hcauchy
  -- the vertical edges converge to the full-line integrals
  have hlimd : Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, G ((d : ℂ) + (y : ℝ) * I)) atTop
      (𝓝 (∫ y : ℝ, G ((d : ℂ) + (y : ℝ) * I))) :=
    intervalIntegral_tendsto_integral hd tendsto_neg_atTop_atBot tendsto_id
  have hlimc : Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, G ((c : ℂ) + (y : ℝ) * I)) atTop
      (𝓝 (∫ y : ℝ, G ((c : ℂ) + (y : ℝ) * I))) :=
    intervalIntegral_tendsto_integral hc tendsto_neg_atTop_atBot tendsto_id
  have hcomb := ((hbot.sub htop).add (hlimd.const_smul I)).sub (hlimc.const_smul I)
  have hzero : Tendsto (fun T : ℝ =>
      ((∫ x : ℝ in c..d, G ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
          - (∫ x : ℝ in c..d, G ((x : ℂ) + ((T : ℝ) : ℂ) * I))
          + I • (∫ y : ℝ in (-T)..T, G ((d : ℂ) + (y : ℝ) * I)))
        - I • (∫ y : ℝ in (-T)..T, G ((c : ℂ) + (y : ℝ) * I))) atTop (𝓝 0) := by
    simp only [hrect]
    exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hcomb hzero
  have hI : I * ((∫ y : ℝ, G ((d : ℂ) + (y : ℝ) * I)) - ∫ y : ℝ, G ((c : ℂ) + (y : ℝ) * I))
      = I * 0 := by
    rw [mul_zero, mul_sub]
    simpa [smul_eq_mul] using heq
  have := mul_left_cancel₀ Complex.I_ne_zero hI
  linear_combination this


/-- A uniform bound on a horizontal segment that tends to zero forces the segment integral to
tend to zero. -/
theorem tendsto_intervalIntegral_of_tendsto_bound {G : ℂ → ℂ} {c d : ℝ} {M hgt : ℝ → ℝ}
    (hb : ∀ᶠ T : ℝ in atTop, ∀ u ∈ uIoc c d, ‖G ((u : ℂ) + ((hgt T : ℝ) : ℂ) * I)‖ ≤ M T)
    (hM : Tendsto M atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => ∫ u in c..d, G ((u : ℂ) + ((hgt T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (by simpa using hM.mul_const |d - c|)
  filter_upwards [hb] with T hT
  exact intervalIntegral.norm_integral_le_of_norm_le_const hT

end GaloisForLFunctions.HTGeometry
