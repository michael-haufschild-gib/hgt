import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSignedConvolution
import GaloisForLFunctions.RHTower.ZetaDerivZeroSumMainTerm

/-!
# Gaussian extraction error for the actual signed source

Absolute Dirichlet summability at `9/8` controls the aggregate kernel
error by `O(T^(5/6))`. The proof splits the pointwise weighted kernel at
`T^(4/3)` and then sums one integrable majorant. No Ramanujan estimate or
local absolute-mass hypothesis is added to the full-positive source.
-/

open Complex MeasureTheory Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

open GaussZeroSum

theorem exists_weighted_gaussian_kernel_error_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ (9 / 8 : ℝ) * |leftKernel T n - 2 * gaussW T n| ≤ C * T ^ (5 / 6 : ℝ) := by
  obtain ⟨A, hA0, hA⟩ := exists_abs_leftKernel_sub_le
  obtain ⟨B, hB0, hB⟩ := exists_abs_leftKernel_le_sq
  refine ⟨2 * A + B + 2, by positivity, fun T hT n hn => ?_⟩
  have hT0 : 0 < T := by linarith
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn9 : 0 ≤ (n : ℝ) ^ (9 / 8 : ℝ) := Real.rpow_nonneg hn0.le _
  let Y : ℝ := T ^ (4 / 3 : ℝ)
  have hY : 0 < Y := Real.rpow_pos_of_pos hT0 _
  rcases le_or_gt (n : ℝ) Y with hnY | hnY
  · have hcos : Real.cos (2 * Real.pi * n) = 1 := by
      rw [mul_comm (2 * Real.pi)]
      exact Real.cos_nat_mul_two_pi n
    have hnear := hA T hT n hn0.le
    rw [hcos, mul_one] at hnear
    change |leftKernel T n - 2 * gaussW T n| ≤ A * ((n : ℝ) / T ^ 2 + 1 / T) at hnear
    have he₁ : (n : ℝ) ^ (9 / 8 : ℝ) * n = (n : ℝ) ^ (17 / 8 : ℝ) := by
      rw [show (17 / 8 : ℝ) = 9 / 8 + 1 by norm_num, Real.rpow_add_one hn0.ne']
    have he₂ : Y ^ (17 / 8 : ℝ) / T ^ 2 = T ^ (5 / 6 : ℝ) := by
      dsimp only [Y]
      rw [← Real.rpow_mul hT0.le, ← Real.rpow_natCast T 2, ← Real.rpow_sub hT0]
      norm_num
    have he₃ : Y ^ (9 / 8 : ℝ) / T = T ^ (1 / 2 : ℝ) := by
      dsimp only [Y]
      rw [← Real.rpow_mul hT0.le, ← Real.rpow_sub_one hT0.ne']
      norm_num
    have hpow : T ^ (1 / 2 : ℝ) ≤ T ^ (5 / 6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
    calc _ ≤ (n : ℝ) ^ (9 / 8 : ℝ) * (A * ((n : ℝ) / T ^ 2 + 1 / T)) :=
          mul_le_mul_of_nonneg_left hnear hn9
      _ = A * ((n : ℝ) ^ (17 / 8 : ℝ) / T ^ 2 + (n : ℝ) ^ (9 / 8 : ℝ) / T) := by
          rw [← he₁]; ring
      _ ≤ A * (Y ^ (17 / 8 : ℝ) / T ^ 2 + Y ^ (9 / 8 : ℝ) / T) := by
          gcongr
      _ = A * (T ^ (5 / 6 : ℝ) + T ^ (1 / 2 : ℝ)) := by rw [he₂, he₃]
      _ ≤ (2 * A + B + 2) * T ^ (5 / 6 : ℝ) := by
          nlinarith [mul_le_mul_of_nonneg_left hpow hA0,
            mul_nonneg hB0 (Real.rpow_nonneg hT0.le (5 / 6 : ℝ)),
            Real.rpow_pos_of_pos hT0 (5 / 6 : ℝ)]
  · have hfar : |leftKernel T n - 2 * gaussW T n| ≤ (B + 2) * T ^ 2 / (n : ℝ) ^ 2 := by
      have hg := gaussW_le_sq_div hT0 hn0
      have hj := hB T hT n hn0
      have hp := gaussW_pos T n
      have hab := abs_sub (leftKernel T n) (2 * gaussW T n)
      rw [abs_of_pos (by positivity : 0 < 2 * gaussW T n)] at hab
      exact hab.trans ((add_le_add hj (mul_le_mul_of_nonneg_left hg (by norm_num))).trans_eq
        (by ring))
    have he₁ : (n : ℝ) ^ (9 / 8 : ℝ) / (n : ℝ) ^ 2 = (n : ℝ) ^ (-7 / 8 : ℝ) := by
      rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_sub hn0]
      norm_num
    have hdec : (n : ℝ) ^ (-7 / 8 : ℝ) ≤ Y ^ (-7 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hY hnY.le (by norm_num)
    have he₂ : T ^ 2 * Y ^ (-7 / 8 : ℝ) = T ^ (5 / 6 : ℝ) := by
      dsimp only [Y]
      rw [← Real.rpow_mul hT0.le, ← Real.rpow_natCast T 2, ← Real.rpow_add hT0]
      norm_num
    calc _ ≤ (n : ℝ) ^ (9 / 8 : ℝ) * ((B + 2) * T ^ 2 / (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hfar hn9
      _ = (B + 2) * T ^ 2 * (n : ℝ) ^ (-7 / 8 : ℝ) := by rw [← he₁]; ring
      _ ≤ (B + 2) * T ^ 2 * Y ^ (-7 / 8 : ℝ) :=
          mul_le_mul_of_nonneg_left hdec (by positivity)
      _ = (B + 2) * T ^ (5 / 6 : ℝ) := by rw [mul_assoc, he₂]
      _ ≤ (2 * A + B + 2) * T ^ (5 / 6 : ℝ) := by gcongr; linarith

/-- The actual source error series is absolutely summable and sublinear. -/
theorem exists_norm_source_gaussian_error_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      Summable (fun n : ℕ => sourceSquareCoeff lam n *
        ((leftKernel T n - 2 * gaussW T n : ℝ) : ℂ)) ∧
      ‖∑' n : ℕ, sourceSquareCoeff lam n * ((leftKernel T n - 2 * gaussW T n : ℝ) : ℂ)‖ ≤
        C * T ^ (5 / 6 : ℝ) := by
  obtain ⟨K, hK, hb⟩ := exists_weighted_gaussian_kernel_error_le
  let w : ℕ → ℝ := fun n => ‖LSeries.term (sourceSquareCoeff lam) ((9 / 8 : ℝ) : ℂ) n‖
  have hw : Summable w := (sourceSquareCoeff_summable hW (s := ((9 / 8 : ℝ) : ℂ)) (by norm_num)).norm
  have hw0 (n : ℕ) : 0 ≤ w n := norm_nonneg _
  refine ⟨K * ∑' n, w n, by positivity, fun T hT => ?_⟩
  let e : ℕ → ℂ := fun n => sourceSquareCoeff lam n * ((leftKernel T n - 2 * gaussW T n : ℝ) : ℂ)
  have hT0 : 0 < T := by linarith
  have hmajor (n : ℕ) : ‖e n‖ ≤ w n * (K * T ^ (5 / 6 : ℝ)) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [e, w, sourceSquareCoeff_zero]
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    have hnp : 0 < (n : ℝ) ^ (9 / 8 : ℝ) := Real.rpow_pos_of_pos hn0 _
    have he : w n = ‖sourceSquareCoeff lam n‖ / (n : ℝ) ^ (9 / 8 : ℝ) := by
      simp only [w, LSeries.norm_term_eq, if_neg hn.ne', Complex.ofReal_re]
    dsimp only [e]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, he]
    calc _ = (‖sourceSquareCoeff lam n‖ / (n : ℝ) ^ (9 / 8 : ℝ)) *
        ((n : ℝ) ^ (9 / 8 : ℝ) * |leftKernel T n - 2 * gaussW T n|) := by field_simp [hnp.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb T hT n hn) (by positivity)
  have hs : Summable (fun n => ‖e n‖) := Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    hmajor (hw.mul_right (K * T ^ (5 / 6 : ℝ)))
  refine ⟨hs.of_norm, (norm_tsum_le_tsum_norm hs).trans ?_⟩
  calc ∑' n, ‖e n‖ ≤ ∑' n, w n * (K * T ^ (5 / 6 : ℝ)) :=
        hs.tsum_le_tsum hmajor (hw.mul_right _)
    _ = (K * ∑' n, w n) * T ^ (5 / 6 : ℝ) := by rw [tsum_mul_right]; ring

end RHTower.WeilSingularArithmetic
