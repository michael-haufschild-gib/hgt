import GaloisForLFunctions.RHTower.XiPoissonHalfPlaneDecay

/-!
# Splitting the Poisson trace on a vertical line

On a vertical line the trace splits into its bottom shell and everything above it.  Weighting by
`exp (g_1 v)` -- which is what the half-plane decay of `XiPoissonHalfPlaneDecay` leaves bounded --
holds the bottom-shell terms at constant modulus while the above-bottom part is suppressed by the
spectral gap:

`exp(g_1 v) ‖above-bottom part at (sigma+v) + i u‖ <= exp(|u|/2) exp(-(g_2 - g_1) v) * constant`.

The two exponentials pull in opposite directions, so for each `u` a choice of `v` growing linearly in
`|u|` makes the above-bottom part harmlessly small while the bottom-shell moduli do not move.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The above-bottom part of the trace on a vertical line. -/
def xiPoissonAboveBottomSum (s u : ℝ) : ℂ :=
  ∑' q : xiPoissonAboveBottom, xiPoissonTerm ((s : ℂ) + (u : ℂ) * I) (q : XiZeroCopy)

theorem re_vertical (s u : ℝ) : ((s : ℂ) + (u : ℂ) * I).re = s := by
  simp [Complex.mul_re]

theorem im_vertical (s u : ℝ) : ((s : ℂ) + (u : ℂ) * I).im = u := by
  simp [Complex.mul_im]

/-- The trace on a vertical line is its bottom shell plus everything above. -/
theorem xiPoissonTraceC_vertical_split {s : ℝ} (hs : 0 < s) (u : ℝ) :
    xiPoissonTraceC ((s : ℂ) + (u : ℂ) * I) =
      xiPoissonBottomShellSum s u + xiPoissonAboveBottomSum s u := by
  have hre : 0 < ((s : ℂ) + (u : ℂ) * I).re := by rw [re_vertical]; exact hs
  have hsum : Summable (fun q : XiZeroCopy => xiPoissonTerm ((s : ℂ) + (u : ℂ) * I) q) :=
    (summable_norm_xiPoissonTerm hre).of_norm
  exact (hsum.sum_add_tsum_compl).symm

/-- **The weighted tail bound.**  Above the bottom shell, the spectral gap beats the bottom-height
weight, at a cost of `exp (|u|/2)` from the vertical direction. -/
theorem exp_bottomHeight_mul_norm_aboveBottomSum_le {σ : ℝ} (hσ : 0 < σ)
    {g₂ : ℝ} (hg₂ : ∀ q ∈ xiPoissonAboveBottom, g₂ ≤ (xiPoissonPoint q).re)
    {v : ℝ} (hv : 0 ≤ v) (u : ℝ) :
    Real.exp (xiPoissonBottomHeight * v) * ‖xiPoissonAboveBottomSum (σ + v) u‖ ≤
      Real.exp (|u| / 2) * Real.exp (-((g₂ - xiPoissonBottomHeight) * v)) *
        ∑' q : xiPoissonAboveBottom, xiPoissonWeight σ (q : XiZeroCopy) := by
  have hsv : 0 < σ + v := by linarith
  have hre : 0 < (((σ + v : ℝ) : ℂ) + (u : ℂ) * I).re := by rw [re_vertical]; exact hsv
  have hsumnorm := summable_norm_xiPoissonTerm hre
  have hsumσ : Summable (fun q : xiPoissonAboveBottom => xiPoissonWeight σ (q : XiZeroCopy)) :=
    (summable_xiPoissonWeight hσ).subtype _
  have hterm : ∀ q : xiPoissonAboveBottom,
      Real.exp (xiPoissonBottomHeight * v) *
          ‖xiPoissonTerm (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (q : XiZeroCopy)‖ ≤
        Real.exp (|u| / 2) * Real.exp (-((g₂ - xiPoissonBottomHeight) * v)) *
          xiPoissonWeight σ (q : XiZeroCopy) := by
    intro q
    have hR : g₂ ≤ (xiPoissonPoint (q : XiZeroCopy)).re := hg₂ _ q.2
    have hJ : |(xiPoissonPoint (q : XiZeroCopy)).im| < 1 / 2 :=
      abs_xiPoissonPoint_im_lt_half _
    rw [norm_xiPoissonTerm, re_vertical, im_vertical, xiPoissonWeight,
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have huJ : u * (xiPoissonPoint (q : XiZeroCopy)).im ≤ |u| / 2 := by
      calc u * (xiPoissonPoint (q : XiZeroCopy)).im
          ≤ |u * (xiPoissonPoint (q : XiZeroCopy)).im| := le_abs_self _
        _ = |u| * |(xiPoissonPoint (q : XiZeroCopy)).im| := abs_mul _ _
        _ ≤ |u| * (1 / 2) := mul_le_mul_of_nonneg_left hJ.le (abs_nonneg _)
        _ = |u| / 2 := by ring
    nlinarith [hR, hv, huJ]
  calc Real.exp (xiPoissonBottomHeight * v) * ‖xiPoissonAboveBottomSum (σ + v) u‖
      ≤ Real.exp (xiPoissonBottomHeight * v) *
          ∑' q : xiPoissonAboveBottom,
            ‖xiPoissonTerm (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (q : XiZeroCopy)‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact norm_tsum_le_tsum_norm (hsumnorm.subtype _)
    _ = ∑' q : xiPoissonAboveBottom,
          Real.exp (xiPoissonBottomHeight * v) *
            ‖xiPoissonTerm (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (q : XiZeroCopy)‖ :=
        (tsum_mul_left).symm
    _ ≤ ∑' q : xiPoissonAboveBottom,
          Real.exp (|u| / 2) * Real.exp (-((g₂ - xiPoissonBottomHeight) * v)) *
            xiPoissonWeight σ (q : XiZeroCopy) :=
        Summable.tsum_le_tsum hterm (((hsumnorm.subtype _)).mul_left _) (hsumσ.mul_left _)
    _ = Real.exp (|u| / 2) * Real.exp (-((g₂ - xiPoissonBottomHeight) * v)) *
          ∑' q : xiPoissonAboveBottom, xiPoissonWeight σ (q : XiZeroCopy) := tsum_mul_left

end

end RHTower
