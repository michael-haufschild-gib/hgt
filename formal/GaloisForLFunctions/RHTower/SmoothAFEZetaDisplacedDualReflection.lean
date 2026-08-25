import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftDisplacedDerivative
import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneralDualTruncation

/-!
# Reflection of the general dual cutoff at a displaced abscissa

The fixed left contour defining the general reflected coefficient is exactly
the negative of the positive-line displaced weight after inversion of scale.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory

theorem smoothAFEZetaDualCutoffGeneral_displaced_eq_neg_weight
    {y : ℝ} (hy : 0 < y) (d τ : ℝ) :
    smoothAFEZetaDualCutoffGeneral (displacedLinePt d τ) y =
      -smoothAFEZetaDisplacedDualWeight d τ y⁻¹ := by
  unfold smoothAFEZetaDualCutoffGeneral smoothAFEZetaDisplacedDualWeight
    smoothAFEZetaDisplacedDualWeightAt
  let f : ℝ → ℂ := fun v =>
    smoothAFEDualRatioIntegrand (displacedLinePt d τ) y
      (((-1 : ℝ) : ℂ) + (v : ℂ) * I)
  rw [← MeasureTheory.integral_neg_eq_self f volume]
  rw [Complex.real_smul, Complex.real_smul]
  have hpoint : ∀ v : ℝ,
      f (-v) =
        -(smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
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
        smoothAFEDualRatioIntegrand (displacedLinePt d τ) y (-w) by
          unfold f
          rw [harg]]
    unfold smoothAFEDualRatioIntegrand
    rw [smoothAFEMellinIntegrand_neg_eq_neg_inv hy w hw]
    ring
  rw [show (fun v : ℝ => f (-v)) =
      (fun v : ℝ => -(smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand y⁻¹
          (((1 : ℝ) : ℂ) + (v : ℂ) * I))) by
        funext v
        exact hpoint v]
  rw [integral_neg]
  ring

theorem smoothAFEZetaDualCoefficientGeneral_displaced_eq_neg_weight
    {x : ℝ} (hx : 0 < x) (d τ : ℝ) (n : ℕ) :
    smoothAFEZetaDualCoefficientGeneral (displacedLinePt d τ) x n =
      -((zetaChi (displacedLinePt d τ) *
          (n + 1 : ℂ) ^ (displacedLinePt d τ - 1)) *
        smoothAFEZetaDisplacedDualWeight d τ ((n + 1 : ℝ) * x)) := by
  have hn : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
  have hnx : 0 < (n + 1 : ℝ) * x := mul_pos hn hx
  unfold smoothAFEZetaDualCoefficientGeneral
  rw [smoothAFEZetaDualCutoffGeneral_displaced_eq_neg_weight
      (one_div_pos.mpr hnx)]
  rw [show (1 / ((n + 1 : ℝ) * x))⁻¹ = (n + 1 : ℝ) * x by
    rw [one_div, inv_inv]]
  ring

/-- Uniform conductor-small correction to the classical reflected
Dirichlet coefficient on every moving Levinson line. -/
theorem exists_norm_smoothAFEZetaDualCoefficientGeneral_displaced_add_main_le
    {d₀ η : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ (τ : ℝ) {x : ℝ}, 0 < x → ∀ n : ℕ,
        ‖smoothAFEZetaDualCoefficientGeneral (displacedLinePt d τ) x n +
            (zetaChi (displacedLinePt d τ) *
              (n + 1 : ℂ) ^ (displacedLinePt d τ - 1))‖ ≤
          ‖zetaChi (displacedLinePt d τ) *
              (n + 1 : ℂ) ^ (displacedLinePt d τ - 1)‖ *
            (C * (((n + 1 : ℝ) * x) ^ (d + η)) /
              (max 1 |τ|) ^ (d + η)) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_norm_smoothAFEZetaDisplacedDualWeight_sub_one_le_uniform_conductor
      hd₀0 hd₀half hη hηhalf
  refine ⟨C, hC, fun d hd hdd₀ τ {x} hx n => ?_⟩
  let A : ℂ := zetaChi (displacedLinePt d τ) *
    (n + 1 : ℂ) ^ (displacedLinePt d τ - 1)
  let Y : ℝ := (n + 1 : ℝ) * x
  have hn : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
  have hY : 0 < Y := mul_pos hn hx
  have heq := smoothAFEZetaDualCoefficientGeneral_displaced_eq_neg_weight
    hx d τ n
  have hW := hweight d hd hdd₀ τ hY
  have hdecomp :
      smoothAFEZetaDualCoefficientGeneral (displacedLinePt d τ) x n + A =
        -A * (smoothAFEZetaDisplacedDualWeight d τ Y - 1) := by
    dsimp only [A, Y]
    rw [heq]
    ring
  dsimp only [A, Y] at hW ⊢
  rw [hdecomp, norm_mul, norm_neg]
  exact mul_le_mul_of_nonneg_left hW (norm_nonneg _)

/-- Exact conductor-oriented two-series Gaussian AFE on a displaced
Levinson line. -/
theorem riemannZeta_displaced_eq_two_tsum_smoothAFE_dualWeight
    {x : ℝ} (hx : 0 < x) {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (τ : ℝ) :
    riemannZeta (displacedLinePt d τ) =
      (∑' n : ℕ, (n + 1 : ℂ) ^ (-displacedLinePt d τ) *
        smoothAFECutoff ((n + 1 : ℝ) / x)) +
      (∑' n : ℕ,
        (zetaChi (displacedLinePt d τ) *
          (n + 1 : ℂ) ^ (displacedLinePt d τ - 1)) *
          smoothAFEZetaDisplacedDualWeight d τ ((n + 1 : ℝ) * x)) -
      smoothAFEZetaShiftedPoleResidue (displacedLinePt d τ) x := by
  have hs : displacedLinePt d τ ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    rw [displacedLinePt_re] at hre
    norm_num at hre
    linarith
  have hbase := riemannZeta_eq_two_tsum_smoothAFE_general
    hx hs
    (displacedLinePt_mem_openStrip hd hdhalf τ).1
    (displacedLinePt_mem_openStrip hd hdhalf τ).2
  have hdual :
      (∑' n : ℕ,
        smoothAFEZetaDualCoefficientGeneral (displacedLinePt d τ) x n) =
        -(∑' n : ℕ,
          (zetaChi (displacedLinePt d τ) *
            (n + 1 : ℂ) ^ (displacedLinePt d τ - 1)) *
            smoothAFEZetaDisplacedDualWeight d τ ((n + 1 : ℝ) * x)) := by
    calc
      (∑' n : ℕ,
          smoothAFEZetaDualCoefficientGeneral (displacedLinePt d τ) x n) =
          ∑' n : ℕ,
            -((zetaChi (displacedLinePt d τ) *
              (n + 1 : ℂ) ^ (displacedLinePt d τ - 1)) *
              smoothAFEZetaDisplacedDualWeight d τ ((n + 1 : ℝ) * x)) := by
        apply tsum_congr
        intro n
        exact smoothAFEZetaDualCoefficientGeneral_displaced_eq_neg_weight
          hx d τ n
      _ = -(∑' n : ℕ,
          (zetaChi (displacedLinePt d τ) *
            (n + 1 : ℂ) ^ (displacedLinePt d τ - 1)) *
            smoothAFEZetaDisplacedDualWeight d τ ((n + 1 : ℝ) * x)) := by
        rw [tsum_neg]
  change riemannZeta (displacedLinePt d τ) =
      (∑' n : ℕ, (n + 1 : ℂ) ^ (-displacedLinePt d τ) *
        smoothAFECutoff ((n + 1 : ℝ) / x)) -
      (∑' n : ℕ,
        smoothAFEZetaDualCoefficientGeneral (displacedLinePt d τ) x n) -
      smoothAFEZetaShiftedPoleResidue (displacedLinePt d τ) x at hbase
  rw [hdual] at hbase
  simpa only [sub_neg_eq_add] using hbase

end RHTower
