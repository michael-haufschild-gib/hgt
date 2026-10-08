import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticGaussianError

/-!
# A signed Gaussian upper bound for the actual arithmetic source

Both extracted series converge absolutely before they are subtracted.
The exact source contour and the sublinear extraction error then bound
the real Gaussian sum by `O(T^(5/6))`, using full positivity alone.
-/

open Complex MeasureTheory Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

open GaussZeroSum

theorem exists_norm_source_gaussW_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      Summable (fun n : ℕ => sourceSquareCoeff lam n * (gaussW T n : ℂ)) ∧
      ‖∑' n : ℕ, sourceSquareCoeff lam n * (gaussW T n : ℂ)‖ ≤ C * T ^ 2 := by
  let w : ℕ → ℝ := fun n => ‖LSeries.term (sourceSquareCoeff lam) (2 : ℂ) n‖
  have hw : Summable w := (sourceSquareCoeff_summable hW (s := 2) (by norm_num)).norm
  have hw0 (n : ℕ) : 0 ≤ w n := norm_nonneg _
  refine ⟨∑' n, w n, tsum_nonneg hw0, fun T hT => ?_⟩
  let f : ℕ → ℂ := fun n => sourceSquareCoeff lam n * (gaussW T n : ℂ)
  have hb (n : ℕ) : ‖f n‖ ≤ w n * T ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [f, w]
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    have he : w n = ‖sourceSquareCoeff lam n‖ / (n : ℝ) ^ 2 := by
      simp only [w, LSeries.norm_term_eq, if_neg hn.ne', Complex.re_ofNat,
        Real.rpow_two]
    dsimp only [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussW_pos T n), he]
    calc
      _ ≤ ‖sourceSquareCoeff lam n‖ * (T ^ 2 / (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (gaussW_le_sq_div hT hn0) (norm_nonneg _)
      _ = _ := by ring
  have hf : Summable (fun n => ‖f n‖) := Summable.of_nonneg_of_le
    (fun n => norm_nonneg _) hb (hw.mul_right (T ^ 2))
  refine ⟨hf.of_norm, (norm_tsum_le_tsum_norm hf).trans ?_⟩
  calc
    ∑' n, ‖f n‖ ≤ ∑' n, w n * T ^ 2 := hf.tsum_le_tsum hb (hw.mul_right _)
    _ = _ := tsum_mul_right

theorem summable_source_leftKernel {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) :
    Summable (fun n : ℕ => sourceSquareCoeff lam n * (leftKernel T n : ℂ)) := by
  obtain ⟨C, _, hC⟩ := exists_norm_source_gaussian_error_le hW
  obtain ⟨D, _, hD⟩ := exists_norm_source_gaussW_le hW
  have hs := (hC T hT).1.add ((hD T (by linarith)).1.mul_left (2 : ℂ))
  refine hs.congr fun n => ?_
  push_cast
  ring

theorem source_gaussian_error_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) :
    (∑' n : ℕ, sourceSquareCoeff lam n * ((leftKernel T n - 2 * gaussW T n : ℝ) : ℂ)) =
      (∑' n : ℕ, sourceSquareCoeff lam n * (leftKernel T n : ℂ)) -
        2 * ∑' n : ℕ, sourceSquareCoeff lam n * (gaussW T n : ℂ) := by
  obtain ⟨D, _, hD⟩ := exists_norm_source_gaussW_le hW
  have hj := summable_source_leftKernel hW hT
  have hw := (hD T (by linarith)).1.mul_left (2 : ℂ)
  calc
    _ = ∑' n : ℕ, (sourceSquareCoeff lam n * (leftKernel T n : ℂ) -
        2 * (sourceSquareCoeff lam n * (gaussW T n : ℂ))) := by
      apply tsum_congr
      intro n
      push_cast
      ring
    _ = _ := by rw [hj.tsum_sub hw, tsum_mul_left]

/-- The source Gaussian sum has a sublinear upper bound, without a sign premise. -/
theorem exists_re_source_gaussW_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      (∑' n : ℕ, sourceSquareCoeff lam n * (gaussW T n : ℂ)).re ≤
        C * T ^ (5 / 6 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_source_gaussian_error_le hW
  let B : ℝ := |(sourcePoleNumerator hW 1).re| * Real.exp (1 / 4)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B + C, by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hpow : 1 ≤ T ^ (5 / 6 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hT (show (0 : ℝ) ≤ 5 / 6 by norm_num)
  have hexp : Real.exp (1 / (4 * T ^ 2)) ≤ Real.exp (1 / 4) := by
    apply Real.exp_le_exp.mpr
    have hsq : 1 ≤ T ^ 2 := by nlinarith
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * T ^ 2) (by norm_num : (0 : ℝ) < 4)).mpr
    nlinarith
  have hPB : -(sourcePoleNumerator hW 1).re * Real.exp (1 / (4 * T ^ 2)) ≤ B :=
    mul_le_mul (neg_le_abs _) hexp (Real.exp_pos _).le (abs_nonneg _)
  have hI := re_integral_sourceZetaPairing_gaussian_right_le hW hT
  rw [integral_sourceZetaPairing_eq_kernelSum hW hT] at hI
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, zero_add, sub_zero] at hI
  have hj : (∑' n : ℕ, sourceSquareCoeff lam n * (leftKernel T n : ℂ)).re ≤ B := by
    have hb := mul_le_mul_of_nonneg_left hPB Real.pi_pos.le
    have h2 : 2 * (∑' n : ℕ, sourceSquareCoeff lam n * (leftKernel T n : ℂ)).re ≤ B := by
      apply (mul_le_mul_iff_right₀ Real.pi_pos).mp
      nlinarith only [hI, hb]
    linarith only [h2, hB]
  let e : ℂ := ∑' n : ℕ, sourceSquareCoeff lam n * ((leftKernel T n - 2 * gaussW T n : ℝ) : ℂ)
  have he : -e.re ≤ C * T ^ (5 / 6 : ℝ) :=
    (neg_le_abs e.re).trans ((Complex.abs_re_le_norm e).trans (hC T hT).2)
  have hid := congrArg Complex.re (source_gaussian_error_eq hW hT)
  change e.re = _ at hid
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero] at hid
  have hBpow := mul_le_mul_of_nonneg_left hpow hB
  have hCpow : 0 ≤ C * T ^ (5 / 6 : ℝ) := by positivity
  nlinarith

end RHTower.WeilSingularArithmetic
