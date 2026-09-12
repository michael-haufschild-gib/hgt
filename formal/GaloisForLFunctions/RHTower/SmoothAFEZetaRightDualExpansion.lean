import GaloisForLFunctions.RHTower.SmoothAFEZetaRightDualContourLimit
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDualReflection

/-!
# Exact direct smooth AFE on a displaced right line

This connects the conductor-localized right dual weight to the actual
general-point AFE coefficients, rather than to an abstract model.
-/

noncomputable section

namespace RHTower

open Complex

theorem smoothAFEZetaDualCoefficientGeneral_right_eq_neg_weight
    {x : ℝ} (hx : 0 < x) (d τ : ℝ) (n : ℕ) :
    smoothAFEZetaDualCoefficientGeneral (rightDisplacedLinePt d τ) x n =
      -((zetaChi (rightDisplacedLinePt d τ) *
          (n + 1 : ℂ) ^ (rightDisplacedLinePt d τ - 1)) *
        smoothAFEZetaRightDualWeight d τ ((n + 1 : ℝ) * x)) := by
  have h := smoothAFEZetaDualCoefficientGeneral_displaced_eq_neg_weight
    hx (-d) τ n
  unfold smoothAFEZetaRightDualWeight smoothAFEZetaRightDualWeightAt
  unfold smoothAFEZetaDisplacedDualWeight at h
  rw [displacedLinePt_neg_displacement_eq_right] at h
  exact h

/-- Actual right-line dual coefficients differ from their classical main
term by the direct conductor-localization error. -/
theorem exists_norm_smoothAFEZetaDualCoefficientGeneral_right_add_main_le
    {d η : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hdηhalf : d + η < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) {x : ℝ}, 0 < x → ∀ n : ℕ,
      ‖smoothAFEZetaDualCoefficientGeneral
            (rightDisplacedLinePt d τ) x n +
          (zetaChi (rightDisplacedLinePt d τ) *
            (n + 1 : ℂ) ^ (rightDisplacedLinePt d τ - 1))‖ ≤
        ‖zetaChi (rightDisplacedLinePt d τ) *
            (n + 1 : ℂ) ^ (rightDisplacedLinePt d τ - 1)‖ *
          (C * (((n + 1 : ℝ) * x) ^ η) /
            (max 1 |τ|) ^ η) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_norm_smoothAFEZetaRightDualWeight_sub_one_le_conductor
      hd hdhalf hη hdηhalf
  refine ⟨C, hC, fun τ {x} hx n => ?_⟩
  let A : ℂ := zetaChi (rightDisplacedLinePt d τ) *
    (n + 1 : ℂ) ^ (rightDisplacedLinePt d τ - 1)
  let Y : ℝ := (n + 1 : ℝ) * x
  have hn : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
  have hY : 0 < Y := mul_pos hn hx
  have heq := smoothAFEZetaDualCoefficientGeneral_right_eq_neg_weight
    hx d τ n
  have hW := hweight τ hY
  have hdecomp :
      smoothAFEZetaDualCoefficientGeneral
          (rightDisplacedLinePt d τ) x n + A =
        -A * (smoothAFEZetaRightDualWeight d τ Y - 1) := by
    dsimp only [A, Y]
    rw [heq]
    ring
  dsimp only [A, Y] at hW ⊢
  rw [hdecomp, norm_mul, norm_neg]
  exact mul_le_mul_of_nonneg_left hW (norm_nonneg _)

/-- Exact conductor-oriented two-series Gaussian AFE directly on
`1/2+d+iτ`. -/
theorem riemannZeta_rightDisplaced_eq_two_tsum_smoothAFE_dualWeight
    {x : ℝ} (hx : 0 < x) {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (τ : ℝ) :
    riemannZeta (rightDisplacedLinePt d τ) =
      (∑' n : ℕ, (n + 1 : ℂ) ^ (-rightDisplacedLinePt d τ) *
        smoothAFECutoff ((n + 1 : ℝ) / x)) +
      (∑' n : ℕ,
        (zetaChi (rightDisplacedLinePt d τ) *
          (n + 1 : ℂ) ^ (rightDisplacedLinePt d τ - 1)) *
          smoothAFEZetaRightDualWeight d τ ((n + 1 : ℝ) * x)) -
      smoothAFEZetaShiftedPoleResidue (rightDisplacedLinePt d τ) x := by
  have hs : rightDisplacedLinePt d τ ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    rw [rightDisplacedLinePt_re] at hre
    norm_num at hre
    linarith
  have hstrip := rightDisplacedLinePt_mem_openStrip hd hdhalf τ
  have hbase := riemannZeta_eq_two_tsum_smoothAFE_general
    hx hs hstrip.1 hstrip.2
  have hdual :
      (∑' n : ℕ,
        smoothAFEZetaDualCoefficientGeneral
          (rightDisplacedLinePt d τ) x n) =
        -(∑' n : ℕ,
          (zetaChi (rightDisplacedLinePt d τ) *
            (n + 1 : ℂ) ^ (rightDisplacedLinePt d τ - 1)) *
            smoothAFEZetaRightDualWeight d τ ((n + 1 : ℝ) * x)) := by
    calc
      (∑' n : ℕ,
          smoothAFEZetaDualCoefficientGeneral
            (rightDisplacedLinePt d τ) x n) =
          ∑' n : ℕ,
            -((zetaChi (rightDisplacedLinePt d τ) *
              (n + 1 : ℂ) ^ (rightDisplacedLinePt d τ - 1)) *
              smoothAFEZetaRightDualWeight d τ ((n + 1 : ℝ) * x)) := by
        apply tsum_congr
        intro n
        exact smoothAFEZetaDualCoefficientGeneral_right_eq_neg_weight
          hx d τ n
      _ = -(∑' n : ℕ,
          (zetaChi (rightDisplacedLinePt d τ) *
            (n + 1 : ℂ) ^ (rightDisplacedLinePt d τ - 1)) *
            smoothAFEZetaRightDualWeight d τ ((n + 1 : ℝ) * x)) := by
        rw [tsum_neg]
  change riemannZeta (rightDisplacedLinePt d τ) =
      (∑' n : ℕ, (n + 1 : ℂ) ^ (-rightDisplacedLinePt d τ) *
        smoothAFECutoff ((n + 1 : ℝ) / x)) -
      (∑' n : ℕ,
        smoothAFEZetaDualCoefficientGeneral
          (rightDisplacedLinePt d τ) x n) -
      smoothAFEZetaShiftedPoleResidue (rightDisplacedLinePt d τ) x at hbase
  rw [hdual] at hbase
  simpa only [sub_neg_eq_add] using hbase

end RHTower
