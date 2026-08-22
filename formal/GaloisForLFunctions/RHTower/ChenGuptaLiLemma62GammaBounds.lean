import GaloisForLFunctions.RHTower.SmoothAFEZetaStripBound

/-!
# Chen--Gupta--Li Lemma 6.2: Gamma-ratio bounds

This module extends the corpus's half-width vertical Gamma-ratio estimate to
the width-two range that arises after the two Gamma recurrences in CGL's
finite reflected contour.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

private theorem cglLemma62_div_telescope (a b c d e : ℝ)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) :
    a / e = (a / b) * (b / c) * (c / d) * (d / e) := by
  field_simp [hb, hc, hd, he]

/-- A vertical Gamma quotient over any nonnegative real-part interval of
width at most two has an absolute height-uniform bound.  This is obtained by
partitioning the interval into four widths at most one half and applying the
existing sharp half-width estimate to every part. -/
theorem cglLemma62_norm_Gamma_vertical_ratio_le_exp_eight
    {a b y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hwidth : b - a ≤ 2) (hy : 1 ≤ y) :
    ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
        ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ ≤
      Real.exp 8 := by
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hne : ∀ x : ℝ, Complex.Gamma ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro x
    apply Complex.Gamma_ne_zero
    intro n h
    have him := congrArg Complex.im h
    simp at him
    linarith
  let d : ℝ := (b - a) / 4
  have hd0 : 0 ≤ d := by
    dsimp only [d]
    positivity
  have hdhalf : d ≤ 1 / 2 := by
    dsimp only [d]
    linarith
  have h1 := norm_Gamma_vertical_ratio_le_exp_two ha (by linarith : a ≤ a + d)
    (by linarith) hy
  have ha1 : 0 ≤ a + d := by linarith
  have h2 := norm_Gamma_vertical_ratio_le_exp_two ha1 (by linarith : a + d ≤ a + 2 * d)
    (by dsimp only [d] at hdhalf ⊢; linarith) hy
  have ha2 : 0 ≤ a + 2 * d := by linarith
  have h3 := norm_Gamma_vertical_ratio_le_exp_two ha2
    (by linarith : a + 2 * d ≤ a + 3 * d)
    (by dsimp only [d] at hdhalf ⊢; linarith) hy
  have ha3 : 0 ≤ a + 3 * d := by linarith
  have hb : b = a + 4 * d := by
    dsimp only [d]
    ring
  have h4 := norm_Gamma_vertical_ratio_le_exp_two ha3
    (by rw [hb]; linarith : a + 3 * d ≤ b)
    (by rw [hb]; dsimp only [d] at hdhalf ⊢; linarith) hy
  have hmid1 : ‖Complex.Gamma (((a + d : ℝ) : ℂ) + (y : ℂ) * I)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (hne _)
  have hmid2 : ‖Complex.Gamma (((a + 2 * d : ℝ) : ℂ) + (y : ℂ) * I)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (hne _)
  have hmid3 : ‖Complex.Gamma (((a + 3 * d : ℝ) : ℂ) + (y : ℂ) * I)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (hne _)
  have hlast : ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (hne _)
  have hsplit :
      ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
          ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ =
        (‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
          ‖Complex.Gamma (((a + d : ℝ) : ℂ) + (y : ℂ) * I)‖) *
        (‖Complex.Gamma (((a + d : ℝ) : ℂ) + (y : ℂ) * I)‖ /
          ‖Complex.Gamma (((a + 2 * d : ℝ) : ℂ) + (y : ℂ) * I)‖) *
        (‖Complex.Gamma (((a + 2 * d : ℝ) : ℂ) + (y : ℂ) * I)‖ /
          ‖Complex.Gamma (((a + 3 * d : ℝ) : ℂ) + (y : ℂ) * I)‖) *
        (‖Complex.Gamma (((a + 3 * d : ℝ) : ℂ) + (y : ℂ) * I)‖ /
          ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖) := by
    exact cglLemma62_div_telescope _ _ _ _ _ hmid1 hmid2 hmid3 hlast
  rw [hsplit]
  calc
    _ ≤ Real.exp 2 * Real.exp 2 * Real.exp 2 * Real.exp 2 := by
      gcongr
    _ = Real.exp 8 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr
      norm_num

end

end RHTower
