import GaloisForLFunctions.HTGeometry.YoungConvolutionL2

/-!
# The Gamma cutoff commutator has an exponentially localized kernel

The Gamma jump kernel `1/(e^{|s|} - 1)` is not integrable at the origin, but a cutoff commutator
never sees the origin: the difference of the cutoff values cancels the singularity.  For a cutoff
bounded by one with Lipschitz constant `Λ`,

`|χ(L) - χ(L')| / (e^{|L-L'|} - 1) ≤ (2Λ + 4) e^{-|L-L'|/2}`,

so the commutator is dominated by convolution with an integrable exponential envelope, and Young's
inequality bounds it on `L²` by `4(2Λ + 4)`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- The Gamma jump kernel of the physical seam. -/
def gammaJumpKernel (s : ℝ) : ℝ := 1 / (Real.exp |s| - 1)

/-- **The cutoff commutator kernel is exponentially localized.** -/
theorem abs_cutoff_diff_mul_gammaJumpKernel_le {χ : ℝ → ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hbound : ∀ x, |χ x| ≤ 1) (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|) (L L' : ℝ)
    (hne : L ≠ L') :
    |χ L - χ L'| * gammaJumpKernel (L - L')
      ≤ (2 * Λ + 4) * Real.exp (-(|L - L'| / 2)) := by
  set s : ℝ := |L - L'| with hs
  have hs0 : 0 < s := by
    rw [hs, abs_pos]
    exact sub_ne_zero.mpr hne
  have hexp : 1 < Real.exp s := by
    rw [show (1:ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr hs0
  have hden : 0 < Real.exp s - 1 := by linarith
  have hker : gammaJumpKernel (L - L') = 1 / (Real.exp s - 1) := by
    rw [gammaJumpKernel, hs]
  have hhalf : 0 < Real.exp (-(s / 2)) := Real.exp_pos _
  rcases le_or_gt s 1 with hle | hgt
  · have hlin : |χ L - χ L'| ≤ Λ * s := by
      rw [hs]
      exact hlip L L'
    have hexpge : s ≤ Real.exp s - 1 := by
      have := Real.add_one_le_exp s
      linarith
    have hratio : |χ L - χ L'| * gammaJumpKernel (L - L') ≤ Λ := by
      rw [hker, mul_one_div, div_le_iff₀ hden]
      calc |χ L - χ L'| ≤ Λ * s := hlin
        _ ≤ Λ * (Real.exp s - 1) := by
            apply mul_le_mul_of_nonneg_left hexpge hΛ
    have hexphalf : Real.exp (-(1 / 2 : ℝ)) ≤ Real.exp (-(s / 2)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hlow : (1:ℝ) / 2 ≤ Real.exp (-(1 / 2 : ℝ)) := by
      have h := Real.add_one_le_exp (-(1/2 : ℝ))
      linarith
    nlinarith [hratio, hexphalf, hlow, hΛ, hhalf]
  · have habs : |χ L - χ L'| ≤ 2 := by
      have h1 := hbound L
      have h2 := hbound L'
      have := abs_sub_abs_le_abs_sub (χ L) (χ L')
      have h3 : |χ L - χ L'| ≤ |χ L| + |χ L'| := abs_sub (χ L) (χ L')
      linarith
    have hexpsplit : Real.exp s - 1 ≥ Real.exp (s / 2) * (Real.exp (1 / 2) - 1) := by
      have hfac : Real.exp s = Real.exp (s / 2) * Real.exp (s / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hhalfge : Real.exp (1 / 2 : ℝ) ≤ Real.exp (s / 2) := by
        apply Real.exp_le_exp.mpr
        linarith
      have hpos : 0 < Real.exp (s / 2) := Real.exp_pos _
      nlinarith [hfac, hhalfge, hpos]
    have hconst : (1:ℝ) / 2 ≤ Real.exp (1 / 2 : ℝ) - 1 := by
      have h := Real.add_one_le_exp (1 / 2 : ℝ)
      have h2 : Real.exp (1/2 : ℝ) * Real.exp (1/2 : ℝ) = Real.exp 1 := by
        rw [← Real.exp_add]
        congr 1
        ring
      nlinarith [Real.exp_one_gt_d9, Real.exp_pos (1/2 : ℝ), h2]
    have hratio : |χ L - χ L'| * gammaJumpKernel (L - L') ≤ 4 * Real.exp (-(s / 2)) := by
      rw [hker, mul_one_div, div_le_iff₀ hden]
      have hinv : Real.exp (-(s / 2)) * Real.exp (s / 2) = 1 := by
        rw [← Real.exp_add]
        simp
      nlinarith [habs, hexpsplit, hconst, hhalf, Real.exp_pos (s / 2), hinv]
    nlinarith [hratio, hhalf, hΛ]

end

end RHTower
