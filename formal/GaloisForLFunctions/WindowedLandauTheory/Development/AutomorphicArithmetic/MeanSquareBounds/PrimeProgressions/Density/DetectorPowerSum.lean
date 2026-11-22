import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroRepulsion.ShiftedPowerSum

/-! A shifted power sum detects a zero within twice the real offset. -/

open Complex Finset

namespace QH.PrimeProgressions

private theorem turan_factor_le {n K : ℕ} (hn : 1 ≤ n) (hnK : n ≤ K) :
    (1 / (3200 * Real.exp 1) : ℝ) ^ K ≤
      ((n : ℝ) / (1600 * ((K : ℝ) + n))) ^ n := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn
  have hK₀ : (0 : ℝ) < K := by exact_mod_cast hn.trans hnK
  have hnK' : (n : ℝ) ≤ K := by exact_mod_cast hnK
  let b : ℝ := 1 / (3200 * Real.exp 1)
  let v : ℝ := (n : ℝ) / (3200 * K)
  have hb : 0 < b := by dsimp only [b]; positivity
  have hv : 0 < v := by dsimp only [v]; positivity
  have hm := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hK₀ hn₀)) hn₀.le
  have he : (n : ℝ) * ((K : ℝ) / n - 1) = (K : ℝ) - n := by
    field_simp [hn₀.ne'] <;> ring
  rw [he] at hm
  have hbLog : Real.log b = -(Real.log 3200 + 1) := by
    dsimp only [b]
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
      Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp, zero_sub]
  have hvLog : Real.log v = -Real.log 3200 - Real.log ((K : ℝ) / n) := by
    dsimp only [v]
    rw [Real.log_div hn₀.ne' (by positivity), Real.log_mul (by norm_num) hK₀.ne',
      Real.log_div hK₀.ne' hn₀.ne']
    ring
  calc
    b ^ K = Real.exp ((K : ℝ) * Real.log b) := by rw [Real.exp_nat_mul, Real.exp_log hb]
    _ ≤ Real.exp ((n : ℝ) * Real.log v) := by
      apply Real.exp_le_exp.mpr
      rw [hbLog, hvLog]
      linarith only [hm, hn₀, mul_le_mul_of_nonneg_right hnK' (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3200))]
    _ = v ^ n := by rw [Real.exp_nat_mul, Real.exp_log hv]
    _ ≤ _ := pow_le_pow_left₀ hv.le
      (div_le_div_of_nonneg_left hn₀.le (by positivity) (by linarith only [hnK'])) n

/-- If the retained divisor has at most `K` copies, one of the orders from `K+1`
through `2K` detects its large reciprocal. -/
theorem detector_power_sum (n K : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K)
    (w : Fin n → ℂ) {r : ℝ} (hr : 0 < r) (hnear : ∃ i, 1 / (2 * r) ≤ ‖w i‖) :
    ∃ j : ℕ, K + 1 ≤ j ∧ j ≤ 2 * K ∧
      (1 / ((6400 * Real.exp 1) * r)) ^ j ≤ ‖∑ i, w i ^ j‖ := by
  obtain ⟨i₀, hi₀⟩ := hnear
  obtain ⟨i, -, himax⟩ := exists_max_image (univ : Finset (Fin n)) (fun i => ‖w i‖)
    ⟨i₀, mem_univ _⟩
  let R := ‖w i‖
  have hR : 1 / (2 * r) ≤ R := hi₀.trans (himax i₀ (mem_univ _))
  have hR₀ : 0 < R := (by positivity : 0 < 1 / (2 * r)).trans_le hR
  let z (i : Fin n) : ℂ := w i / (R : ℂ)
  have hz (i' : Fin n) : ‖z i'‖ ≤ 1 := by
    dsimp only [z]
    rw [norm_div, norm_real, Real.norm_of_nonneg hR₀.le]
    exact (div_le_one hR₀).mpr (himax i' (mem_univ _))
  have hzi : ‖z i‖ = 1 := by
    dsimp only [z]
    rw [norm_div, norm_real, Real.norm_of_nonneg hR₀.le]
    exact div_self hR₀.ne'
  obtain ⟨j, hj, hj', hsum⟩ := T2.turan2Main n K z hn hz ⟨i, hzi⟩
  refine ⟨j, hj, by omega, ?_⟩
  have hnorm : ‖∑ i, w i ^ j‖ = R ^ j * ‖∑ i, z i ^ j‖ := by
    have hR' : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR₀.ne'
    have he : (∑ i, w i ^ j) = (R : ℂ) ^ j * ∑ i, z i ^ j := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [← mul_pow]
      dsimp only [z]
      rw [show (R : ℂ) * (w i / (R : ℂ)) = w i by field_simp [hR']]
    rw [he, norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hR₀.le]
  let b : ℝ := 1 / (3200 * Real.exp 1)
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hb₁ : b ≤ 1 := by
    dsimp only [b]
    refine (div_le_one (by positivity)).mpr ?_
    linarith only [Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)]
  have hsmall : b ^ j ≤ ‖∑ i, z i ^ j‖ :=
    (pow_le_pow_of_le_one hb hb₁ (by omega : K ≤ j)).trans
      ((turan_factor_le hn hnK).trans hsum)
  calc
    _ = (1 / (2 * r)) ^ j * b ^ j := by
      rw [← mul_pow]
      congr 1
      dsimp only [b]
      field_simp [hr.ne']
      <;> ring
    _ ≤ R ^ j * ‖∑ i, z i ^ j‖ :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hR j) hsmall (pow_nonneg hb _) (pow_nonneg hR₀.le _)
    _ = _ := hnorm.symm

end QH.PrimeProgressions
