import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDualReflection
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftRightPowerBound

/-!
# Right-strip smooth AFE with a reflected primal terminal block

Reflect the exact AFE at `1/2-d-iτ` before expanding `ζ(1/2+d+iτ)`.  The resulting
terminal block uses the height-independent primal cutoff `smoothAFECutoff`; the complementary
block retains the displaced dual weight on the reflected left line.
-/

noncomputable section

namespace RHTower

open Complex

/-- Coefficient of the terminal reflected-primal block on the right line. -/
def smoothAFEZetaRightReflectedPrimalCoefficient
    (d τ x : ℝ) (n : ℕ) : ℂ :=
  (zetaChi (rightDisplacedLinePt d τ) *
      (n + 1 : ℂ) ^ (rightDisplacedLinePt d τ - 1)) *
    smoothAFECutoff ((n + 1 : ℝ) / x)

/-- Coefficient of the complementary reflected-left dual block. -/
def smoothAFEZetaRightComplementCoefficient
    (d τ x : ℝ) (n : ℕ) : ℂ :=
  (n + 1 : ℂ) ^ (-rightDisplacedLinePt d τ) *
    smoothAFEZetaDisplacedDualWeight d (-τ) ((n + 1 : ℝ) * x)

/-- Exact right-strip AFE obtained by reflecting the left-line AFE first.

The first series has the growing power `n^{-1/2+d}` multiplied by the ordinary primal cutoff;
it is therefore the terminal carrier when `x` is proportional to the height. -/
theorem riemannZeta_rightDisplaced_eq_reflectedPrimal_add_complement
    {x : ℝ} (hx : 0 < x) {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (τ : ℝ) :
    riemannZeta (rightDisplacedLinePt d τ) =
      (∑' n : ℕ, smoothAFEZetaRightReflectedPrimalCoefficient d τ x n) +
      (∑' n : ℕ, smoothAFEZetaRightComplementCoefficient d τ x n) -
      zetaChi (rightDisplacedLinePt d τ) *
        smoothAFEZetaShiftedPoleResidue (displacedLinePt d (-τ)) x := by
  let sR : ℂ := rightDisplacedLinePt d τ
  let sL : ℂ := displacedLinePt d (-τ)
  have hsR0 : sR ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [sR] at hre
    rw [rightDisplacedLinePt_re] at hre
    norm_num at hre
    linarith
  have hsR1 : sR ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [sR] at hre
    rw [rightDisplacedLinePt_re] at hre
    norm_num at hre
    linarith
  have hGamma : Gammaℝ (1 - sR) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    dsimp only [sR]
    rw [← displacedLinePt_neg_eq_one_sub_rightDisplacedLinePt]
    rw [displacedLinePt_re]
    linarith
  have hFE : riemannZeta sR = zetaChi sR * riemannZeta sL := by
    have h := zeta_eq_zetaChi_mul hsR0 hsR1 hGamma
    dsimp only [sR, sL] at h ⊢
    rwa [← displacedLinePt_neg_eq_one_sub_rightDisplacedLinePt] at h
  have hleft := riemannZeta_displaced_eq_two_tsum_smoothAFE_dualWeight
    hx hd hdhalf (-τ)
  have hchi : zetaChi sR * zetaChi sL = 1 := by
    dsimp only [sR, sL]
    exact zetaChi_right_mul_reflected_left hd hdhalf τ
  rw [hFE, hleft]
  rw [mul_sub, mul_add, ← tsum_mul_left, ← tsum_mul_left]
  have hprimal :
      (∑' n : ℕ, zetaChi sR *
        ((n + 1 : ℂ) ^ (-displacedLinePt d (-τ)) *
          smoothAFECutoff ((n + 1 : ℝ) / x))) =
        ∑' n : ℕ, smoothAFEZetaRightReflectedPrimalCoefficient d τ x n := by
    apply tsum_congr
    intro n
    unfold smoothAFEZetaRightReflectedPrimalCoefficient
    dsimp only [sR, sL]
    rw [rightDisplacedLinePt_sub_one_eq_neg_displacedLinePt_neg]
    ring
  have hcomplement :
      (∑' n : ℕ, zetaChi sR *
        ((zetaChi (displacedLinePt d (-τ)) *
          (n + 1 : ℂ) ^ (displacedLinePt d (-τ) - 1)) *
          smoothAFEZetaDisplacedDualWeight d (-τ) ((n + 1 : ℝ) * x))) =
        ∑' n : ℕ, smoothAFEZetaRightComplementCoefficient d τ x n := by
    apply tsum_congr
    intro n
    unfold smoothAFEZetaRightComplementCoefficient
    dsimp only [sR, sL] at hchi ⊢
    rw [displacedLinePt_neg_sub_one_eq_neg_rightDisplacedLinePt]
    calc
      zetaChi (rightDisplacedLinePt d τ) *
            (zetaChi (displacedLinePt d (-τ)) *
              (n + 1 : ℂ) ^ (-rightDisplacedLinePt d τ) *
              smoothAFEZetaDisplacedDualWeight d (-τ) ((n + 1 : ℝ) * x)) =
          (zetaChi (rightDisplacedLinePt d τ) *
              zetaChi (displacedLinePt d (-τ))) *
            ((n + 1 : ℂ) ^ (-rightDisplacedLinePt d τ) *
              smoothAFEZetaDisplacedDualWeight d (-τ) ((n + 1 : ℝ) * x)) := by
                ring
      _ = (n + 1 : ℂ) ^ (-rightDisplacedLinePt d τ) *
            smoothAFEZetaDisplacedDualWeight d (-τ) ((n + 1 : ℝ) * x) := by
              rw [hchi, one_mul]
  rw [hprimal, hcomplement]

end RHTower
