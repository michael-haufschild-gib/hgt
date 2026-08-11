import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Ridge source-correlation localization

A small approximation residual forces large source/synthesis correlation.  If a coordinate split
has little high-side correlation, the low coordinates must carry the target correlation; a ridge
coefficient bound then forces a quantitative norm floor for their analysis vector.

These are Hilbert-space inequalities only.  Arithmetic applications separately provide the
reciprocal-square high-source tail and the zero count.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A unit source approximated within `1/4` has real correlation greater than `3/4` with the
approximant. -/
theorem unit_residual_lt_quarter_re_inner_gt
    (h p : H) (hunit : ‖h‖ = 1) (hres : ‖h - p‖ < 1 / 4) :
    3 / 4 < (inner ℂ h p).re := by
  have hpert : p = h - (h - p) := by abel
  have hcs : ‖inner ℂ h (h - p)‖ < 1 / 4 := by
    calc
      ‖inner ℂ h (h - p)‖ ≤ ‖h‖ * ‖h - p‖ := norm_inner_le_norm _ _
      _ = ‖h - p‖ := by rw [hunit, one_mul]
      _ < 1 / 4 := hres
  have hre : (inner ℂ h (h - p)).re < 1 / 4 := by
    have habs : |(inner ℂ h (h - p)).re| < 1 / 4 :=
      lt_of_le_of_lt (Complex.abs_re_le_norm _) hcs
    exact (abs_lt.mp habs).2
  rw [hpert, inner_sub_right, Complex.sub_re]
  have hself : (inner ℂ h h).re = 1 := by
    have hs := inner_self_eq_norm_sq (𝕜 := ℂ) h
    change (inner ℂ h h).re = ‖h‖ ^ 2 at hs
    rw [hs, hunit]
    norm_num
  rw [hself]
  linarith

/-- If a split analysis/synthesis pairing has high-side contribution at most `delta`, its low side
carries correlation greater than `3/4 - delta`. -/
theorem source_correlation_localizes
    (h p : H) (uLow uHigh cLow cHigh : E) (delta : ℝ)
    (hunit : ‖h‖ = 1) (hres : ‖h - p‖ < 1 / 4)
    (hpair : inner ℂ h p = inner ℂ uLow cLow + inner ℂ uHigh cHigh)
    (hhigh : ‖uHigh‖ * ‖cHigh‖ ≤ delta) :
    3 / 4 - delta < (inner ℂ uLow cLow).re := by
  have htotal := unit_residual_lt_quarter_re_inner_gt h p hunit hres
  rw [hpair, Complex.add_re] at htotal
  have hhre : (inner ℂ uHigh cHigh).re ≤ delta := by
    calc
      (inner ℂ uHigh cHigh).re ≤ ‖inner ℂ uHigh cHigh‖ := Complex.re_le_norm _
      _ ≤ ‖uHigh‖ * ‖cHigh‖ := norm_inner_le_norm _ _
      _ ≤ delta := hhigh
  linarith

/-- Correlation above `3/4 - delta` plus coefficient norm at most `1/(4 scale)` forces the
analysis norm above `(3 - 4 delta) scale`.  In ridge applications `scale = sqrt r`. -/
theorem core_analysis_norm_gt
    (u c : E) (delta scale : ℝ)
    (hscale : 0 < scale) (hc : ‖c‖ ≤ 1 / (4 * scale))
    (hcorr : 3 / 4 - delta < (inner ℂ u c).re) :
    (3 - 4 * delta) * scale < ‖u‖ := by
  have hre : (inner ℂ u c).re ≤ ‖u‖ * ‖c‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hbound : ‖u‖ * ‖c‖ ≤ ‖u‖ / (4 * scale) := by
    calc
      ‖u‖ * ‖c‖ ≤ ‖u‖ * (1 / (4 * scale)) :=
        mul_le_mul_of_nonneg_left hc (norm_nonneg u)
      _ = ‖u‖ / (4 * scale) := by ring
  have hden : 0 < 4 * scale := mul_pos (by norm_num) hscale
  have hmain : 3 / 4 - delta < ‖u‖ / (4 * scale) :=
    lt_of_lt_of_le hcorr (hre.trans hbound)
  have hscaled := (lt_div_iff₀ hden).mp hmain
  calc
    (3 - 4 * delta) * scale = (3 / 4 - delta) * (4 * scale) := by ring
    _ < ‖u‖ := hscaled

end GaloisForLFunctions.HTGeometry
