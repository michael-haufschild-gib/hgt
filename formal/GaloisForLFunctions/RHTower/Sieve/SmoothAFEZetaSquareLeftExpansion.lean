import GaloisForLFunctions.RHTower.Sieve.SmoothAFEZetaSquareRightExpansion
import GaloisForLFunctions.RHTower.SmoothAFEZetaDualReflection

noncomputable section

open Complex MeasureTheory

namespace RHTower.Sieve

def smoothAFEZetaSquareLeftReflectedIntegrand
    (tau x : ℝ) (w : ℂ) : ℂ :=
  zetaChi (linePt tau + w) ^ 2 *
    LSeries (fun m : ℕ => (m.divisors.card : ℂ))
      (1 - linePt tau - w) *
    (x : ℂ) ^ w * smoothAFEGaussianKernel w

def smoothAFEZetaSquareLeftReflectedTerm
    (tau x : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  zetaChi (linePt tau + w) ^ 2 *
    LSeries.term (fun m : ℕ => (m.divisors.card : ℂ))
      (1 - linePt tau - w) (n + 1) *
    (x : ℂ) ^ w * smoothAFEGaussianKernel w

theorem smoothAFEZetaSquareMellinIntegrand_left_eq_reflected
    (tau x t : ℝ) :
    smoothAFEZetaSquareMellinIntegrand (linePt tau) x
        ((-1 : ℂ) + (t : ℂ) * I) =
      smoothAFEZetaSquareLeftReflectedIntegrand tau x
        ((-1 : ℂ) + (t : ℂ) * I) := by
  let w : ℂ := (-1 : ℂ) + (t : ℂ) * I
  have hz0 : linePt tau + w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [w] at hre
    simp [linePt] at hre
    norm_num at hre
  have hz1 : linePt tau + w ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [w] at hre
    simp [linePt] at hre
    norm_num at hre
  have hreflect : 1 < (1 - linePt tau - w).re := by
    dsimp only [w]
    simp [linePt]
    norm_num
  have hGamma : Gammaℝ (1 - (linePt tau + w)) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    have : (1 - (linePt tau + w)).re = (1 - linePt tau - w).re := by
      congr 1
      ring
    rw [this]
    linarith
  have hFE : riemannZeta (linePt tau + w) =
      zetaChi (linePt tau + w) * riemannZeta (1 - (linePt tau + w)) :=
    zeta_eq_zetaChi_mul hz0 hz1 hGamma
  have harg : (1 : ℂ) - (linePt tau + w) = 1 - linePt tau - w := by ring
  have hDS := LSeries_card_divisors_eq_riemannZeta_sq hreflect
  unfold smoothAFEZetaSquareMellinIntegrand
  unfold smoothAFEZetaSquareLeftReflectedIntegrand
  rw [hFE, harg, hDS]
  ring

theorem smoothAFEZetaSquareLeftReflectedIntegrand_eq_tsum
    (tau x t : ℝ) :
    smoothAFEZetaSquareLeftReflectedIntegrand tau x
        ((-1 : ℂ) + (t : ℂ) * I) =
      ∑' n : ℕ, smoothAFEZetaSquareLeftReflectedTerm tau x n
        ((-1 : ℂ) + (t : ℂ) * I) := by
  let w : ℂ := (-1 : ℂ) + (t : ℂ) * I
  have hre : (1 - linePt tau - w).re = 3 / 2 := by
    dsimp only [w]
    simp [linePt]
    ring
  have hreflect : 1 < (1 - linePt tau - w).re := by rw [hre]; norm_num
  have hsum := LSeriesSummable_card_divisors hreflect
  unfold smoothAFEZetaSquareLeftReflectedIntegrand
  unfold LSeries
  rw [hsum.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  rw [← tsum_mul_left, ← tsum_mul_right, ← tsum_mul_right]
  apply tsum_congr
  intro n
  rfl

theorem smoothAFEZetaSquareMellinIntegrand_left_eq_tsum
    (tau x t : ℝ) :
    smoothAFEZetaSquareMellinIntegrand (linePt tau) x
        ((-1 : ℂ) + (t : ℂ) * I) =
      ∑' n : ℕ, smoothAFEZetaSquareLeftReflectedTerm tau x n
        ((-1 : ℂ) + (t : ℂ) * I) := by
  rw [smoothAFEZetaSquareMellinIntegrand_left_eq_reflected,
    smoothAFEZetaSquareLeftReflectedIntegrand_eq_tsum]

theorem smoothAFEZetaSquareLeftReflectedTerm_factor
    (tau x : ℝ) (n : ℕ) (w : ℂ) :
    smoothAFEZetaSquareLeftReflectedTerm tau x n w =
      zetaChi (linePt tau) ^ 2 *
        ((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (linePt tau - 1) *
        (smoothAFEZetaChiShiftRatio (linePt tau) w) ^ 2 *
        (n + 1 : ℂ) ^ w * (x : ℂ) ^ w *
        smoothAFEGaussianKernel w := by
  have hn : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
  have hnC : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast hn
  have hχ : zetaChi (linePt tau) ≠ 0 := zetaChi_line_ne_zero tau
  rw [smoothAFEZetaSquareLeftReflectedTerm, LSeries.term_of_ne_zero hn]
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  have hexp : -(1 - linePt tau - w) = (linePt tau - 1) + w := by ring
  rw [hexp]
  push_cast
  rw [Complex.cpow_add _ _ hnC]
  unfold smoothAFEZetaChiShiftRatio
  field_simp [hχ]

theorem smoothAFEZetaSquareLeftReflectedTerm_neg_eq_dualIntegrand
    {x : ℝ} (hx : 0 < x) (tau : ℝ) (n : ℕ) (v : ℝ) :
    smoothAFEZetaSquareLeftReflectedTerm tau x n
        ((-1 : ℂ) + ((-v : ℝ) : ℂ) * I) =
      -(zetaChi (linePt tau) ^ 2 *
        ((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (linePt tau - 1) *
        (smoothAFEZetaChiShiftRatioSq tau v *
          smoothAFEMellinIntegrand ((n + 1 : ℝ) * x)
            ((1 : ℂ) + (v : ℂ) * I))) := by
  let u : ℂ := (1 : ℂ) + (v : ℂ) * I
  have hu0 : u ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [u] at hre
    norm_num at hre
  have harg : ((-1 : ℂ) + ((-v : ℝ) : ℂ) * I) = -u := by
    dsimp only [u]
    push_cast
    ring
  have hnpos : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
  have hmul : ((((n + 1 : ℝ) * x : ℝ) : ℂ) ^ (-u)) =
      (n + 1 : ℂ) ^ (-u) * (x : ℂ) ^ (-u) := by
    convert Complex.mul_cpow_ofReal_nonneg hnpos.le hx.le (-u) using 1 <;>
      norm_num
  rw [harg, smoothAFEZetaSquareLeftReflectedTerm_factor]
  unfold smoothAFEZetaChiShiftRatioSq smoothAFEMellinIntegrand
  rw [smoothAFEGaussianKernel_neg hu0]
  push_cast at hmul
  push_cast
  rw [hmul]
  dsimp only [u]
  ring

def smoothAFEZetaSquareDualSeriesIntegrand
    (tau x : ℝ) (n : ℕ) (v : ℝ) : ℂ :=
  zetaChi (linePt tau) ^ 2 *
    ((n + 1).divisors.card : ℂ) *
    (n + 1 : ℂ) ^ (linePt tau - 1) *
    (smoothAFEZetaChiShiftRatioSq tau v *
      smoothAFEMellinIntegrand ((n + 1 : ℝ) * x)
        ((1 : ℂ) + (v : ℂ) * I))

theorem smoothAFEZetaSquareDualSeriesIntegrand_integrable
    {x : ℝ} (hx : 0 < x) (tau : ℝ) (n : ℕ) :
    Integrable (smoothAFEZetaSquareDualSeriesIntegrand tau x n) := by
  have hY : 0 < (n + 1 : ℝ) * x :=
    mul_pos (by exact_mod_cast Nat.succ_pos n) hx
  have hbase := smoothAFEZetaSquareDualWeightAt_one_integrable hY tau
  let C : ℂ := zetaChi (linePt tau) ^ 2 *
    ((n + 1).divisors.card : ℂ) *
    (n + 1 : ℂ) ^ (linePt tau - 1)
  have hmul := hbase.const_mul C
  unfold smoothAFEZetaSquareDualSeriesIntegrand
  simpa only [C, Complex.ofReal_one] using hmul

theorem norm_smoothAFEZetaSquareDualSeriesIntegrand_le
    {x : ℝ} (hx : 0 < x) (tau : ℝ) (n : ℕ) (v : ℝ) :
    ‖smoothAFEZetaSquareDualSeriesIntegrand tau x n v‖ ≤
      ((‖zetaChi (linePt tau) ^ 2‖ * (1 + |tau|) ^ 2 *
          Real.exp 1 / x) *
        (((n + 1).divisors.card : ℝ) /
          (n + 1 : ℝ) ^ (3 / 2 : ℝ))) *
        ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by
  have hnpos : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
  have hY : 0 < (n + 1 : ℝ) * x := mul_pos hnpos hx
  have hratio0 := norm_smoothAFEZetaChiShiftRatio_neg_right_one_le tau v
  have hratio0' :
      ‖smoothAFEZetaChiShiftRatio (linePt tau)
        (-((1 : ℂ) + (v : ℂ) * I))‖ ≤
        (1 + |tau|) * (1 + |v|) := by
    simpa only [Complex.ofReal_one] using hratio0
  have hratio : ‖smoothAFEZetaChiShiftRatioSq tau v‖ ≤
      (1 + |tau|) ^ 2 * (1 + |v|) ^ 2 := by
    unfold smoothAFEZetaChiShiftRatioSq
    rw [norm_pow]
    calc
      ‖smoothAFEZetaChiShiftRatio (linePt tau)
          (-((1 : ℂ) + ↑v * I))‖ ^ 2
        ≤ ((1 + |tau|) * (1 + |v|)) ^ 2 := by gcongr
      _ = (1 + |tau|) ^ 2 * (1 + |v|) ^ 2 := by ring
  have hm0 := norm_smoothAFEMellinIntegrand_vertical_le hY
    (show (0 : ℝ) < 1 by norm_num) v
  have hm :
      ‖smoothAFEMellinIntegrand ((n + 1 : ℝ) * x)
          ((1 : ℂ) + (v : ℂ) * I)‖ ≤
        ((((n + 1 : ℝ) * x)⁻¹ * Real.exp 1) *
          Real.exp (-(v ^ 2))) := by
    simpa [Real.rpow_neg_one] using hm0
  have hpow : ‖(n + 1 : ℂ) ^ (linePt tau - 1)‖ =
      (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hcast : (n + 1 : ℂ) = (((n + 1 : ℝ) : ℝ) : ℂ) := by
      norm_num
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    congr 1
    simp [linePt]
    ring
  rw [smoothAFEZetaSquareDualSeriesIntegrand,
    norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_natCast, hpow]
  calc
    ‖zetaChi (linePt tau) ^ 2‖ *
          ((n + 1).divisors.card : ℝ) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
          (‖smoothAFEZetaChiShiftRatioSq tau v‖ *
            ‖smoothAFEMellinIntegrand ((n + 1 : ℝ) * x)
              (1 + ↑v * I)‖)
      ≤ ‖zetaChi (linePt tau) ^ 2‖ *
          ((n + 1).divisors.card : ℝ) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
          (((1 + |tau|) ^ 2 * (1 + |v|) ^ 2) *
            ((((n + 1 : ℝ) * x)⁻¹ * Real.exp 1) *
              Real.exp (-(v ^ 2)))) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul hratio hm (norm_nonneg _) (by positivity)
        · positivity
    _ = ((‖zetaChi (linePt tau) ^ 2‖ * (1 + |tau|) ^ 2 *
            Real.exp 1 / x) *
          (((n + 1).divisors.card : ℝ) /
            (n + 1 : ℝ) ^ (3 / 2 : ℝ))) *
          ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by
      have hp : (n + 1 : ℝ) ^ (3 / 2 : ℝ) =
          (n + 1 : ℝ) ^ (1 / 2 : ℝ) * (n + 1 : ℝ) := by
        rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by ring,
          Real.rpow_add hnpos, Real.rpow_one]
      rw [Real.rpow_neg hnpos.le, hp]
      field_simp [hnpos.ne', hx.ne']

theorem summable_integral_norm_smoothAFEZetaSquareDualSeriesIntegrand
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Summable (fun n : ℕ => ∫ v : ℝ,
      ‖smoothAFEZetaSquareDualSeriesIntegrand tau x n v‖) := by
  let q : ℝ → ℝ := fun v =>
    (1 + |v|) ^ 2 * Real.exp (-(v ^ 2))
  let C : ℝ := ‖zetaChi (linePt tau) ^ 2‖ *
    (1 + |tau|) ^ 2 * Real.exp 1 / x
  let M : ℝ := ∫ v : ℝ, q v
  have hq : Integrable q := integrable_one_add_abs_sq_mul_exp_neg_sq
  have hbase := RHTower.summable_card_divisors_div_natSucc_rpow_three_halves
  have hmajor : Summable (fun n : ℕ =>
      (C * (((n + 1).divisors.card : ℝ) /
        (n + 1 : ℝ) ^ (3 / 2 : ℝ))) * M) :=
    (hbase.mul_left C).mul_right M
  refine Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_) hmajor
  have hterm := smoothAFEZetaSquareDualSeriesIntegrand_integrable hx tau n
  have hdom : Integrable (fun v : ℝ =>
      (C * (((n + 1).divisors.card : ℝ) /
        (n + 1 : ℝ) ^ (3 / 2 : ℝ))) * q v) :=
    hq.const_mul _
  calc
    ∫ v : ℝ, ‖smoothAFEZetaSquareDualSeriesIntegrand tau x n v‖
      ≤ ∫ v : ℝ, (C * (((n + 1).divisors.card : ℝ) /
          (n + 1 : ℝ) ^ (3 / 2 : ℝ))) * q v := by
        apply integral_mono_ae hterm.norm hdom
        exact Filter.Eventually.of_forall fun v => by
          simpa only [C, q] using
            norm_smoothAFEZetaSquareDualSeriesIntegrand_le hx tau n v
    _ = (C * (((n + 1).divisors.card : ℝ) /
          (n + 1 : ℝ) ^ (3 / 2 : ℝ))) * M := by
      rw [MeasureTheory.integral_const_mul]

theorem integral_smoothAFEZetaSquareMellinIntegrand_left_eq_neg_tsum
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    (∫ t : ℝ, smoothAFEZetaSquareMellinIntegrand (linePt tau) x
        ((-1 : ℂ) + (t : ℂ) * I)) =
      -(∑' n : ℕ, ∫ v : ℝ,
        smoothAFEZetaSquareDualSeriesIntegrand tau x n v) := by
  let f : ℝ → ℂ := fun t =>
    smoothAFEZetaSquareMellinIntegrand (linePt tau) x
      ((-1 : ℂ) + (t : ℂ) * I)
  rw [show (∫ t : ℝ, smoothAFEZetaSquareMellinIntegrand (linePt tau) x
      ((-1 : ℂ) + (t : ℂ) * I)) = ∫ t : ℝ, f t by rfl]
  rw [← MeasureTheory.integral_neg_eq_self f volume]
  calc
    (∫ v : ℝ, f (-v)) =
        ∫ v : ℝ, ∑' n : ℕ,
          -smoothAFEZetaSquareDualSeriesIntegrand tau x n v := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by
        change f (-v) = _
        rw [show f (-v) =
            ∑' n : ℕ, smoothAFEZetaSquareLeftReflectedTerm tau x n
              ((-1 : ℂ) + ((-v : ℝ) : ℂ) * I) by
          dsimp only [f]
          rw [smoothAFEZetaSquareMellinIntegrand_left_eq_tsum]]
        apply tsum_congr
        intro n
        exact smoothAFEZetaSquareLeftReflectedTerm_neg_eq_dualIntegrand
          hx tau n v
    _ = ∑' n : ℕ, ∫ v : ℝ,
        -smoothAFEZetaSquareDualSeriesIntegrand tau x n v := by
      symm
      apply MeasureTheory.integral_tsum_of_summable_integral_norm
      · exact fun n =>
          (smoothAFEZetaSquareDualSeriesIntegrand_integrable hx tau n).neg
      · simpa only [norm_neg] using
          summable_integral_norm_smoothAFEZetaSquareDualSeriesIntegrand hx tau
    _ = -(∑' n : ℕ, ∫ v : ℝ,
        smoothAFEZetaSquareDualSeriesIntegrand tau x n v) := by
      rw [← tsum_neg]
      apply tsum_congr
      intro n
      rw [integral_neg]

theorem integral_smoothAFEZetaSquareDualSeriesIntegrand_eq_weightIntegral
    {x : ℝ} (_hx : 0 < x) (tau : ℝ) (n : ℕ) :
    (∫ v : ℝ, smoothAFEZetaSquareDualSeriesIntegrand tau x n v) =
      (zetaChi (linePt tau) ^ 2 *
        ((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (linePt tau - 1)) *
        ∫ v : ℝ, smoothAFEZetaChiShiftRatioSq tau v *
          smoothAFEMellinIntegrand ((n + 1 : ℝ) * x)
            ((1 : ℂ) + (v : ℂ) * I) := by
  rw [← MeasureTheory.integral_const_mul]
  rfl

/-- Left Gaussian square contour, normalized by `1/(2π)`. -/
def smoothAFEZetaSquareLeftMellinAt (tau x : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ t : ℝ,
    smoothAFEZetaSquareMellinIntegrand (linePt tau) x
      ((-1 : ℂ) + (t : ℂ) * I)

theorem smoothAFEZetaSquareLeftMellinAt_eq_neg_tsum_dualWeight
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    smoothAFEZetaSquareLeftMellinAt tau x =
      -(∑' n : ℕ, zetaChi (linePt tau) ^ 2 *
        ((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (linePt tau - 1) *
        smoothAFEZetaSquareDualWeight tau ((n + 1 : ℝ) * x)) := by
  unfold smoothAFEZetaSquareLeftMellinAt
  rw [integral_smoothAFEZetaSquareMellinIntegrand_left_eq_neg_tsum hx tau]
  rw [Complex.real_smul, mul_neg, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  rw [integral_smoothAFEZetaSquareDualSeriesIntegrand_eq_weightIntegral hx]
  unfold smoothAFEZetaSquareDualWeight
  rw [Complex.real_smul]
  let J : ℂ := ∫ v : ℝ, smoothAFEZetaChiShiftRatioSq tau v *
    smoothAFEMellinIntegrand ((n + 1 : ℝ) * x)
      (((1 : ℝ) : ℂ) + (v : ℂ) * I)
  change (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ((zetaChi (linePt tau) ^ 2 *
        ((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (linePt tau - 1)) * J)) =
    zetaChi (linePt tau) ^ 2 *
      ((n + 1).divisors.card : ℂ) *
      (n + 1 : ℂ) ^ (linePt tau - 1) *
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * J)
  ring

end RHTower.Sieve
