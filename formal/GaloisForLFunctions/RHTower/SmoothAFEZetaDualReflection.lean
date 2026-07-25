import GaloisForLFunctions.RHTower.SmoothAFEZetaDualExpansion

/-!
# Reflection of the exact dual Gaussian cutoff

The reflected zeta edge is initially parameterized on `Re w = -1`.  Replacing
`w` by `-u` moves it to `Re u = 1`, changes the odd Gaussian kernel by a
minus sign, and replaces the reciprocal scale by the direct scale.  This is
the exact positive-line dual weight used in the conductor-length AFE.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory

theorem smoothAFEGaussianKernel_neg {w : ℂ} (hw : w ≠ 0) :
    smoothAFEGaussianKernel (-w) = -smoothAFEGaussianKernel w := by
  unfold smoothAFEGaussianKernel
  rw [show (-w) ^ 2 = w ^ 2 by ring]
  field_simp

theorem smoothAFEMellinIntegrand_neg_eq_neg_inv
    {y : ℝ} (hy : 0 < y) (w : ℂ) (hw : w ≠ 0) :
    smoothAFEMellinIntegrand y (-w) =
      -smoothAFEMellinIntegrand y⁻¹ w := by
  have hpow :
      ((y⁻¹ : ℝ) : ℂ) ^ (-w) = (y : ℂ) ^ w := by
    simpa [one_div] using
      cpow_div_pos_neg (a := 1) (b := y) zero_lt_one hy w
  unfold smoothAFEMellinIntegrand
  rw [neg_neg, hpow, smoothAFEGaussianKernel_neg hw]
  ring

/-- Positive-line exact dual weight after `w ↦ -w`. -/
def smoothAFEZetaDualWeight (τ Y : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ,
    smoothAFEZetaChiShiftRatio (linePt τ)
        (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y
        (((1 : ℝ) : ℂ) + (v : ℂ) * I)

theorem smoothAFEZetaDualCutoff_eq_neg_dualWeight
    {y : ℝ} (hy : 0 < y) (τ : ℝ) :
    smoothAFEZetaDualCutoff τ y =
      -smoothAFEZetaDualWeight τ y⁻¹ := by
  unfold smoothAFEZetaDualCutoff smoothAFEZetaDualWeight
  let f : ℝ → ℂ := fun v =>
    smoothAFEDualRatioIntegrand (linePt τ) y
      (((-1 : ℝ) : ℂ) + (v : ℂ) * I)
  rw [← MeasureTheory.integral_neg_eq_self f volume]
  rw [Complex.real_smul, Complex.real_smul]
  have hpoint : ∀ v : ℝ,
      f (-v) =
        -(smoothAFEZetaChiShiftRatio (linePt τ)
            (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
          smoothAFEMellinIntegrand y⁻¹
            (((1 : ℝ) : ℂ) + (v : ℂ) * I)) := by
    intro v
    let w : ℂ := ((1 : ℝ) : ℂ) + (v : ℂ) * I
    have hw : w ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      dsimp only [w] at hre
      norm_num at hre
    have harg :
        (((-1 : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I) = -w := by
      dsimp only [w]
      push_cast
      ring
    rw [show f (-v) =
        smoothAFEDualRatioIntegrand (linePt τ) y (-w) by
          unfold f
          rw [harg]]
    unfold smoothAFEDualRatioIntegrand
    rw [smoothAFEMellinIntegrand_neg_eq_neg_inv hy w hw]
    ring
  rw [show (fun v : ℝ => f (-v)) =
      (fun v : ℝ => -(smoothAFEZetaChiShiftRatio (linePt τ)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand y⁻¹
          (((1 : ℝ) : ℂ) + (v : ℂ) * I))) by
        funext v
        exact hpoint v]
  rw [integral_neg]
  ring

/-- The reflected Mellin edge is the negative of the positive-line exact
dual Dirichlet series. -/
theorem smoothAFEZetaDualMellinAt_eq_neg_tsum_dualWeight
    {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    smoothAFEZetaDualMellinAt τ x =
      -(∑' n : ℕ,
        (zetaChi (linePt τ) *
          (n + 1 : ℂ) ^ (linePt τ - 1)) *
          smoothAFEZetaDualWeight τ ((n + 1 : ℝ) * x)) := by
  rw [smoothAFEZetaDualMellinAt_eq_tsum hx τ]
  calc
    (∑' n : ℕ,
        (zetaChi (linePt τ) *
          (n + 1 : ℂ) ^ (linePt τ - 1)) *
          smoothAFEZetaDualCutoff τ
            (1 / ((n + 1 : ℝ) * x))) =
      ∑' n : ℕ,
        -((zetaChi (linePt τ) *
          (n + 1 : ℂ) ^ (linePt τ - 1)) *
          smoothAFEZetaDualWeight τ ((n + 1 : ℝ) * x)) := by
        apply tsum_congr
        intro n
        have hn : (0 : ℝ) < n + 1 := by
          exact_mod_cast Nat.succ_pos n
        have hnx : 0 < (n + 1 : ℝ) * x := mul_pos hn hx
        rw [smoothAFEZetaDualCutoff_eq_neg_dualWeight
          (one_div_pos.mpr hnx)]
        rw [show (1 / ((n + 1 : ℝ) * x))⁻¹ =
            (n + 1 : ℝ) * x by
          rw [one_div, inv_inv]]
        ring
    _ = -(∑' n : ℕ,
        (zetaChi (linePt τ) *
          (n + 1 : ℂ) ^ (linePt τ - 1)) *
          smoothAFEZetaDualWeight τ ((n + 1 : ℝ) * x)) := by
      rw [tsum_neg]

/-- Exact unconditional conductor-oriented two-series Gaussian smooth AFE. -/
theorem riemannZeta_line_eq_two_tsum_smoothAFE_dualWeight
    {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    riemannZeta (linePt τ) =
      (∑' n : ℕ, (n + 1 : ℂ) ^ (-linePt τ) *
        smoothAFECutoff ((n + 1 : ℝ) / x)) +
      (∑' n : ℕ,
        (zetaChi (linePt τ) *
          (n + 1 : ℂ) ^ (linePt τ - 1)) *
          smoothAFEZetaDualWeight τ ((n + 1 : ℝ) * x)) -
      smoothAFEZetaShiftedPoleResidue (linePt τ) x := by
  rw [riemannZeta_line_eq_tsum_smoothAFECutoff_sub_dual_sub_residue hx τ,
    smoothAFEZetaDualMellinAt_eq_neg_tsum_dualWeight hx τ]
  ring

end RHTower
