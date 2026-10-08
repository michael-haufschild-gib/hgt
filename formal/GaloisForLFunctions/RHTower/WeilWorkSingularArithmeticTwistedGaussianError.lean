import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticGaussianError

/-!
# The arithmetic phase in scaled source extraction

The all-real-frequency estimate retains the cosine. Integer frequencies
were exceptional: rational scales expose additive twists of the source.
-/

open Complex MeasureTheory Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

open GaussZeroSum

theorem exists_weighted_twisted_gaussian_kernel_error_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → ∀ y : ℝ, 0 < y →
      y ^ (9 / 8 : ℝ) * |leftKernel T y - 2 * gaussW T y * Real.cos (2 * Real.pi * y)| ≤ C * T ^ (5 / 6 : ℝ) := by
  obtain ⟨A, hA0, hA⟩ := exists_abs_leftKernel_sub_le
  obtain ⟨B, hB0, hB⟩ := exists_abs_leftKernel_le_sq
  refine ⟨2 * A + B + 2, by positivity, fun T hT y hy => ?_⟩
  have hT0 : 0 < T := by linarith
  have hn0 : 0 < y := hy
  have hn9 : 0 ≤ y ^ (9 / 8 : ℝ) := Real.rpow_nonneg hn0.le _
  let Y : ℝ := T ^ (4 / 3 : ℝ)
  have hY : 0 < Y := Real.rpow_pos_of_pos hT0 _
  rcases le_or_gt y Y with hnY | hnY
  · have hnear := hA T hT y hn0.le
    have hnear' : |leftKernel T y - 2 * gaussW T y * Real.cos (2 * Real.pi * y)| ≤
        A * (y / T ^ 2 + 1 / T) := by
      simpa only [gaussW, mul_assoc, mul_left_comm, mul_comm] using hnear
    have he₁ : y ^ (9 / 8 : ℝ) * y = y ^ (17 / 8 : ℝ) := by
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
    calc _ ≤ y ^ (9 / 8 : ℝ) * (A * (y / T ^ 2 + 1 / T)) :=
          mul_le_mul_of_nonneg_left hnear' hn9
      _ = A * (y ^ (17 / 8 : ℝ) / T ^ 2 + y ^ (9 / 8 : ℝ) / T) := by
          rw [← he₁]; ring
      _ ≤ A * (Y ^ (17 / 8 : ℝ) / T ^ 2 + Y ^ (9 / 8 : ℝ) / T) := by
          gcongr
      _ = A * (T ^ (5 / 6 : ℝ) + T ^ (1 / 2 : ℝ)) := by rw [he₂, he₃]
      _ ≤ (2 * A + B + 2) * T ^ (5 / 6 : ℝ) := by
          nlinarith [mul_le_mul_of_nonneg_left hpow hA0,
            mul_nonneg hB0 (Real.rpow_nonneg hT0.le (5 / 6 : ℝ)),
            Real.rpow_pos_of_pos hT0 (5 / 6 : ℝ)]
  · have hfar : |leftKernel T y - 2 * gaussW T y * Real.cos (2 * Real.pi * y)| ≤ (B + 2) * T ^ 2 / y ^ 2 := by
      have hg := gaussW_le_sq_div hT0 hn0
      have hj := hB T hT y hn0
      have hp := gaussW_pos T y
      have hab := abs_sub (leftKernel T y) (2 * gaussW T y * Real.cos (2 * Real.pi * y))
      have hc : |2 * gaussW T y * Real.cos (2 * Real.pi * y)| ≤ 2 * gaussW T y := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * gaussW T y)]
        exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
      exact hab.trans ((add_le_add hj (hc.trans
        (mul_le_mul_of_nonneg_left hg (by norm_num)))).trans_eq (by ring))
    have he₁ : y ^ (9 / 8 : ℝ) / y ^ 2 = y ^ (-7 / 8 : ℝ) := by
      rw [← Real.rpow_natCast y 2, ← Real.rpow_sub hn0]
      norm_num
    have hdec : y ^ (-7 / 8 : ℝ) ≤ Y ^ (-7 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hY hnY.le (by norm_num)
    have he₂ : T ^ 2 * Y ^ (-7 / 8 : ℝ) = T ^ (5 / 6 : ℝ) := by
      dsimp only [Y]
      rw [← Real.rpow_mul hT0.le, ← Real.rpow_natCast T 2, ← Real.rpow_add hT0]
      norm_num
    calc _ ≤ y ^ (9 / 8 : ℝ) * ((B + 2) * T ^ 2 / y ^ 2) :=
          mul_le_mul_of_nonneg_left hfar hn9
      _ = (B + 2) * T ^ 2 * y ^ (-7 / 8 : ℝ) := by rw [← he₁]; ring
      _ ≤ (B + 2) * T ^ 2 * Y ^ (-7 / 8 : ℝ) :=
          mul_le_mul_of_nonneg_left hdec (by positivity)
      _ = (B + 2) * T ^ (5 / 6 : ℝ) := by rw [mul_assoc, he₂]
      _ ≤ (2 * A + B + 2) * T ^ (5 / 6 : ℝ) := by gcongr; linarith

/-- The literal source at every positive scale has a sublinear extraction error. -/
theorem exists_norm_source_twisted_gaussian_error_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ T : ℝ, 1 ≤ T →
      Summable (fun n : ℕ => sourceSquareCoeff lam n *
        ((leftKernel T (n * r) - 2 * gaussW T (n * r) *
          Real.cos (2 * Real.pi * (n * r)) : ℝ) : ℂ)) ∧
      ‖∑' n : ℕ, sourceSquareCoeff lam n *
        ((leftKernel T (n * r) - 2 * gaussW T (n * r) *
          Real.cos (2 * Real.pi * (n * r)) : ℝ) : ℂ)‖ ≤
        C / r ^ (9 / 8 : ℝ) * T ^ (5 / 6 : ℝ) := by
  obtain ⟨A, hA0, hA⟩ := exists_weighted_twisted_gaussian_kernel_error_le
  let w : ℕ → ℝ := fun n => ‖LSeries.term (sourceSquareCoeff lam) (9 / 8 : ℂ) n‖
  have hw : Summable w := (sourceSquareCoeff_summable hW
    (s := 9 / 8) (by norm_num)).norm
  have hw0 (n : ℕ) : 0 ≤ w n := norm_nonneg _
  refine ⟨(∑' n, w n) * A, by positivity, fun r hr T hT => ?_⟩
  have hrp : 0 < r ^ (9 / 8 : ℝ) := Real.rpow_pos_of_pos hr _
  let f : ℕ → ℂ := fun n => sourceSquareCoeff lam n *
    ((leftKernel T (n * r) - 2 * gaussW T (n * r) *
      Real.cos (2 * Real.pi * (n * r)) : ℝ) : ℂ)
  have hb (n : ℕ) : ‖f n‖ ≤ w n * (A / r ^ (9 / 8 : ℝ) * T ^ (5 / 6 : ℝ)) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [f, w]
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    have hnp : (n : ℝ) ^ (9 / 8 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
    have he : w n = ‖sourceSquareCoeff lam n‖ / (n : ℝ) ^ (9 / 8 : ℝ) := by
      simp only [w, LSeries.norm_term_eq, if_neg hn.ne', Complex.div_re,
        Complex.re_ofNat, Complex.im_ofNat]
      norm_num
    have ha := hA T hT (n * r) (mul_pos hn0 hr)
    rw [Real.mul_rpow hn0.le hr.le] at ha
    have hd : (n : ℝ) ^ (9 / 8 : ℝ) *
        |leftKernel T (n * r) - 2 * gaussW T (n * r) *
          Real.cos (2 * Real.pi * (n * r))| ≤ A / r ^ (9 / 8 : ℝ) * T ^ (5 / 6 : ℝ) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hrp).mpr
      simpa only [mul_assoc, mul_left_comm, mul_comm] using ha
    dsimp only [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, he]
    calc
      _ = (‖sourceSquareCoeff lam n‖ / (n : ℝ) ^ (9 / 8 : ℝ)) *
          ((n : ℝ) ^ (9 / 8 : ℝ) *
            |leftKernel T (n * r) - 2 * gaussW T (n * r) *
              Real.cos (2 * Real.pi * (n * r))|) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)
  have hf : Summable (fun n => ‖f n‖) := Summable.of_nonneg_of_le
    (fun n => norm_nonneg _) hb (hw.mul_right _)
  refine ⟨hf.of_norm, (norm_tsum_le_tsum_norm hf).trans ?_⟩
  calc
    ∑' n, ‖f n‖ ≤ ∑' n, w n * (A / r ^ (9 / 8 : ℝ) * T ^ (5 / 6 : ℝ)) :=
      hf.tsum_le_tsum hb (hw.mul_right _)
    _ = _ := by rw [tsum_mul_right]; ring

end RHTower.WeilSingularArithmetic
