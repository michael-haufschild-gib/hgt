import GaloisForLFunctions.RHTower.SmoothAFEZetaDualReflection
import GaloisForLFunctions.RHTower.HardyCarrier

/-!
# Splitting critical-line zeta into two Dirichlet edges

Unimodularity of the functional-equation factor on the critical line turns the exact two-series
Gaussian smooth approximate functional equation into a pointwise majorant of `|ζ(½+iτ)|` by the two
absolutely convergent Dirichlet series and the pole residue.  Squaring gives the pointwise form a
mollified second moment consumes: `|ζ M|² ≤ 3(|D₁M|² + |D₂M|² + |ρM|²)`, so the mean square of
`ζ M` is bounded by three Dirichlet-polynomial mean squares.
-/

open Complex

noncomputable section

namespace RHTower

/-- The direct Dirichlet edge of the Gaussian smooth AFE. -/
def smoothAFEDirectSeries (x τ : ℝ) : ℂ :=
  ∑' n : ℕ, ((n : ℂ) + 1) ^ (-linePt τ) * smoothAFECutoff (((n : ℝ) + 1) / x)

/-- The reflected Dirichlet edge of the Gaussian smooth AFE, with the unimodular factor removed. -/
def smoothAFEDualSeries (x τ : ℝ) : ℂ :=
  ∑' n : ℕ, ((n : ℂ) + 1) ^ (linePt τ - 1) * smoothAFEZetaDualWeight τ (((n : ℝ) + 1) * x)

theorem riemannZeta_line_eq_direct_add_chi_mul_dual {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    riemannZeta (linePt τ) =
      smoothAFEDirectSeries x τ + zetaChi (linePt τ) * smoothAFEDualSeries x τ
        - smoothAFEZetaShiftedPoleResidue (linePt τ) x := by
  rw [riemannZeta_line_eq_two_tsum_smoothAFE_dualWeight hx τ]
  congr 2
  rw [smoothAFEDualSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [mul_assoc]

/-- **The pointwise two-edge majorant on the critical line.** -/
theorem norm_riemannZeta_line_le {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    ‖riemannZeta (linePt τ)‖
      ≤ ‖smoothAFEDirectSeries x τ‖ + ‖smoothAFEDualSeries x τ‖
        + ‖smoothAFEZetaShiftedPoleResidue (linePt τ) x‖ := by
  rw [riemannZeta_line_eq_direct_add_chi_mul_dual hx τ]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖smoothAFEDirectSeries x τ + zetaChi (linePt τ) * smoothAFEDualSeries x τ‖
      ≤ ‖smoothAFEDirectSeries x τ‖ + ‖smoothAFEDualSeries x τ‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_zetaChi_line, one_mul]
  linarith

/-- **The pointwise mollified square majorant.**  Every mollified critical-line value is bounded by
three Dirichlet-edge squares, so the mollified second moment of zeta is bounded by three
Dirichlet-polynomial mean squares. -/
theorem norm_sq_riemannZeta_line_mul_le {x : ℝ} (hx : 0 < x) (τ : ℝ) (m : ℂ) :
    ‖riemannZeta (linePt τ) * m‖ ^ 2
      ≤ 3 * (‖smoothAFEDirectSeries x τ * m‖ ^ 2 + ‖smoothAFEDualSeries x τ * m‖ ^ 2
          + ‖smoothAFEZetaShiftedPoleResidue (linePt τ) x * m‖ ^ 2) := by
  have hbase := norm_riemannZeta_line_le hx τ
  have hm : (0 : ℝ) ≤ ‖m‖ := norm_nonneg _
  have hstep : ‖riemannZeta (linePt τ)‖ * ‖m‖
      ≤ (‖smoothAFEDirectSeries x τ‖ + ‖smoothAFEDualSeries x τ‖
          + ‖smoothAFEZetaShiftedPoleResidue (linePt τ) x‖) * ‖m‖ :=
    mul_le_mul_of_nonneg_right hbase hm
  have habc : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
      (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    intro a b c _ _ _
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
  have hsq : ‖riemannZeta (linePt τ) * m‖ ^ 2
      ≤ ((‖smoothAFEDirectSeries x τ‖ + ‖smoothAFEDualSeries x τ‖
          + ‖smoothAFEZetaShiftedPoleResidue (linePt τ) x‖) * ‖m‖) ^ 2 := by
    rw [norm_mul]
    have hnn : (0 : ℝ) ≤ ‖riemannZeta (linePt τ)‖ * ‖m‖ := by positivity
    nlinarith [hstep, hnn]
  refine le_trans hsq ?_
  rw [mul_pow]
  have hexp := habc ‖smoothAFEDirectSeries x τ‖ ‖smoothAFEDualSeries x τ‖
    ‖smoothAFEZetaShiftedPoleResidue (linePt τ) x‖ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  have hm2 : (0 : ℝ) ≤ ‖m‖ ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hexp hm2
  refine le_trans hmul (le_of_eq ?_)
  rw [norm_mul, norm_mul, norm_mul]
  ring

end RHTower

end
