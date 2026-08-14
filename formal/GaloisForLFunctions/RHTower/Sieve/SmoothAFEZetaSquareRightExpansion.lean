import GaloisForLFunctions.RHTower.Sieve.SmoothAFEZetaSquareInfiniteContour
import GaloisForLFunctions.RHTower.SmoothAFEZetaDirichletExpansion
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualSeriesFreezing

noncomputable section

open Complex MeasureTheory

namespace RHTower.Sieve

def smoothAFEZetaSquareRightMellinTerm
    (tau x : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  LSeries.term (fun m : ℕ => (m.divisors.card : ℂ))
      (linePt tau + w) (n + 1) *
    (x : ℂ) ^ w * smoothAFEGaussianKernel w

theorem smoothAFEZetaSquareMellinIntegrand_right_eq_tsum
    (tau x t : ℝ) :
    smoothAFEZetaSquareMellinIntegrand (linePt tau) x
        ((1 : ℂ) + (t : ℂ) * I) =
      ∑' n : ℕ, smoothAFEZetaSquareRightMellinTerm tau x n
        ((1 : ℂ) + (t : ℂ) * I) := by
  let w : ℂ := (1 : ℂ) + (t : ℂ) * I
  have hre : (linePt tau + w).re = 3 / 2 := by
    dsimp only [w]
    simp [linePt]
    ring
  have hhalf : 1 < (linePt tau + w).re := by rw [hre]; norm_num
  have hsum := LSeriesSummable_card_divisors hhalf
  rw [smoothAFEZetaSquareMellinIntegrand,
    ← LSeries_card_divisors_eq_riemannZeta_sq hhalf]
  unfold LSeries
  rw [hsum.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  rw [← tsum_mul_right, ← tsum_mul_right]
  apply tsum_congr
  intro n
  rfl

theorem smoothAFEZetaSquareRightMellinTerm_eq_divisor_mul_cutoffIntegrand
    {x : ℝ} (hx : 0 < x) (tau : ℝ) (n : ℕ) (w : ℂ) :
    smoothAFEZetaSquareRightMellinTerm tau x n w =
      ((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (-linePt tau) *
        smoothAFEMellinIntegrand ((n + 1 : ℝ) / x) w := by
  have hn : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
  have hnC : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [smoothAFEZetaSquareRightMellinTerm, LSeries.term_of_ne_zero hn,
    smoothAFEMellinIntegrand]
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  rw [show -(linePt tau + w) = -linePt tau + -w by ring]
  push_cast
  rw [Complex.cpow_add _ _ hnC]
  have hdiv := cpow_div_pos_neg
    (a := (n + 1 : ℝ)) (b := x)
    (by exact_mod_cast Nat.succ_pos n) hx w
  push_cast at hdiv
  rw [hdiv]
  ring

theorem smoothAFEZetaSquareRightMellinTerm_verticalIntegrable
    {x : ℝ} (hx : 0 < x) (tau : ℝ) (n : ℕ) :
    Integrable (fun t : ℝ =>
      smoothAFEZetaSquareRightMellinTerm tau x n
        ((1 : ℂ) + (t : ℂ) * I)) := by
  rw [show (fun t : ℝ => smoothAFEZetaSquareRightMellinTerm tau x n
      ((1 : ℂ) + (t : ℂ) * I)) =
      fun t : ℝ => (((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (-linePt tau)) *
        smoothAFEMellinIntegrand ((n + 1 : ℝ) / x)
          ((1 : ℂ) + (t : ℂ) * I) by
    funext t
    rw [smoothAFEZetaSquareRightMellinTerm_eq_divisor_mul_cutoffIntegrand hx]]
  exact (smoothAFEMellinIntegrand_verticalIntegrable
    (div_pos (by exact_mod_cast Nat.succ_pos n) hx) (by norm_num)).const_mul _

theorem norm_smoothAFEZetaSquareRightMellinTerm_vertical_le
    {x : ℝ} (hx : 0 < x) (tau : ℝ) (n : ℕ) (t : ℝ) :
    ‖smoothAFEZetaSquareRightMellinTerm tau x n
        ((1 : ℂ) + (t : ℂ) * I)‖ ≤
      ((((n + 1).divisors.card : ℝ) /
          (n + 1 : ℝ) ^ (3 / 2 : ℝ)) * x * Real.exp 1) *
        Real.exp (-(t ^ 2)) := by
  have hk := norm_smoothAFEGaussianKernel_vertical_le
    (σ := (1 : ℝ)) (by norm_num) t
  rw [smoothAFEZetaSquareRightMellinTerm, norm_mul, norm_mul,
    LSeries.norm_term_eq,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (linePt tau + ((1 : ℂ) + (t : ℂ) * I)).re = 3 / 2 := by
    simp [linePt]
    ring
  have hwre : (((1 : ℂ) + (t : ℂ) * I)).re = 1 := by simp
  rw [hre, hwre, Real.rpow_one]
  simp only [Nat.succ_ne_zero, if_false, Complex.norm_natCast]
  push_cast
  calc
    ((n + 1).divisors.card : ℝ) /
          (n + 1 : ℝ) ^ (3 / 2 : ℝ) * x *
          ‖smoothAFEGaussianKernel (1 + ↑t * I)‖
        ≤ ((n + 1).divisors.card : ℝ) /
            (n + 1 : ℝ) ^ (3 / 2 : ℝ) * x *
            (Real.exp 1 * Real.exp (-(t ^ 2))) := by
          gcongr
          simpa using hk
    _ = ((((n + 1).divisors.card : ℝ) /
          (n + 1 : ℝ) ^ (3 / 2 : ℝ)) * x * Real.exp 1) *
        Real.exp (-(t ^ 2)) := by ring

theorem summable_integral_norm_smoothAFEZetaSquareRightMellinTerm
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Summable (fun n : ℕ => ∫ t : ℝ,
      ‖smoothAFEZetaSquareRightMellinTerm tau x n
        ((1 : ℂ) + (t : ℂ) * I)‖) := by
  let D : ℝ := x * Real.exp 1 *
    ∫ t : ℝ, Real.exp (-(t ^ 2))
  have hbase := RHTower.summable_card_divisors_div_natSucc_rpow_three_halves
  have hmajor : Summable (fun n : ℕ =>
      (((n + 1).divisors.card : ℝ) /
        (n + 1 : ℝ) ^ (3 / 2 : ℝ)) * D) := hbase.mul_right D
  refine Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_) hmajor
  have hterm := smoothAFEZetaSquareRightMellinTerm_verticalIntegrable hx tau n
  have hgauss := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  have hdom : Integrable (fun t : ℝ =>
      ((((n + 1).divisors.card : ℝ) /
          (n + 1 : ℝ) ^ (3 / 2 : ℝ)) * x * Real.exp 1) *
        Real.exp (-(t ^ 2))) := by
    simpa only [neg_one_mul] using hgauss.const_mul
      ((((n + 1).divisors.card : ℝ) /
        (n + 1 : ℝ) ^ (3 / 2 : ℝ)) * x * Real.exp 1)
  calc
    ∫ t : ℝ, ‖smoothAFEZetaSquareRightMellinTerm tau x n
        ((1 : ℂ) + (t : ℂ) * I)‖
      ≤ ∫ t : ℝ,
          ((((n + 1).divisors.card : ℝ) /
              (n + 1 : ℝ) ^ (3 / 2 : ℝ)) * x * Real.exp 1) *
            Real.exp (-(t ^ 2)) := by
        apply integral_mono_ae hterm.norm hdom
        exact Filter.Eventually.of_forall fun t =>
          norm_smoothAFEZetaSquareRightMellinTerm_vertical_le hx tau n t
    _ = (((n + 1).divisors.card : ℝ) /
          (n + 1 : ℝ) ^ (3 / 2 : ℝ)) * D := by
      rw [MeasureTheory.integral_const_mul]
      dsimp only [D]
      ring

theorem integral_smoothAFEZetaSquareMellinIntegrand_right_eq_tsum
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    (∫ t : ℝ, smoothAFEZetaSquareMellinIntegrand (linePt tau) x
        ((1 : ℂ) + (t : ℂ) * I)) =
      ∑' n : ℕ, ∫ t : ℝ,
        smoothAFEZetaSquareRightMellinTerm tau x n
          ((1 : ℂ) + (t : ℂ) * I) := by
  calc
    (∫ t : ℝ, smoothAFEZetaSquareMellinIntegrand (linePt tau) x
        ((1 : ℂ) + (t : ℂ) * I)) =
        ∫ t : ℝ, ∑' n : ℕ,
          smoothAFEZetaSquareRightMellinTerm tau x n
            ((1 : ℂ) + (t : ℂ) * I) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t =>
        smoothAFEZetaSquareMellinIntegrand_right_eq_tsum tau x t
    _ = ∑' n : ℕ, ∫ t : ℝ,
        smoothAFEZetaSquareRightMellinTerm tau x n
          ((1 : ℂ) + (t : ℂ) * I) := by
      symm
      apply MeasureTheory.integral_tsum_of_summable_integral_norm
      · exact fun n =>
          smoothAFEZetaSquareRightMellinTerm_verticalIntegrable hx tau n
      · exact summable_integral_norm_smoothAFEZetaSquareRightMellinTerm hx tau

theorem integral_smoothAFEZetaSquareRightMellinTerm_eq_divisor_mul_cutoffIntegral
    {x : ℝ} (hx : 0 < x) (tau : ℝ) (n : ℕ) :
    (∫ t : ℝ, smoothAFEZetaSquareRightMellinTerm tau x n
        ((1 : ℂ) + (t : ℂ) * I)) =
      (((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (-linePt tau)) *
        ∫ t : ℝ, smoothAFEMellinIntegrand ((n + 1 : ℝ) / x)
          ((1 : ℂ) + (t : ℂ) * I) := by
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    change smoothAFEZetaSquareRightMellinTerm tau x n
      ((1 : ℂ) + (t : ℂ) * I) = _
    rw [smoothAFEZetaSquareRightMellinTerm_eq_divisor_mul_cutoffIntegrand hx]

/-- Right Gaussian square contour, normalized by `1/(2π)`. -/
def smoothAFEZetaSquareRightMellinAt (tau x : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ t : ℝ,
    smoothAFEZetaSquareMellinIntegrand (linePt tau) x
      ((1 : ℂ) + (t : ℂ) * I)

theorem smoothAFEZetaSquareRightMellinAt_eq_tsum_smoothAFECutoff
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    smoothAFEZetaSquareRightMellinAt tau x =
      ∑' n : ℕ, ((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (-linePt tau) *
        smoothAFECutoff ((n + 1 : ℝ) / x) := by
  unfold smoothAFEZetaSquareRightMellinAt
  rw [integral_smoothAFEZetaSquareMellinIntegrand_right_eq_tsum hx tau]
  rw [Complex.real_smul, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [integral_smoothAFEZetaSquareRightMellinTerm_eq_divisor_mul_cutoffIntegral
    hx]
  rw [show smoothAFECutoff ((n + 1 : ℝ) / x) =
      (1 / (2 * Real.pi)) • ∫ t : ℝ,
        smoothAFEMellinIntegrand ((n + 1 : ℝ) / x)
          ((1 : ℂ) + (t : ℂ) * I) by
    rw [← smoothAFECutoffAt_eq_smoothAFECutoff
      (σ := (1 : ℝ))
      (div_pos (by exact_mod_cast Nat.succ_pos n) hx) (by norm_num)]
    rfl]
  rw [Complex.real_smul]
  ring

end RHTower.Sieve
