import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheCalibratedExponentialBlockApproximatesAConstant
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A positive calibrated block at dense imaginary grids

The two factorials in the interpolation error offset the exponential
weight loss. Explicit inequalities `A≤8k` and `512x≤k` make the error
at most `1/4`, uniformly throughout the prescribed window.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

private theorem exp_nat_le_three_pow (n : ℕ) : Real.exp (n : ℝ) ≤ (3 : ℝ) ^ n := by
  calc
    _ = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le n

/-- An elementary factorial estimate with the rational upper bound `e<3`. -/
theorem pow_div_factorial_le_three_scaled_pow {a : ℝ} (ha : 0 ≤ a) {n : ℕ} (hn : 0 < n) :
    a ^ n / (n.factorial : ℝ) ≤ (3 * a / n) ^ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hf := (Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n).trans
    (exp_nat_le_three_pow n)
  calc
    _ = (a / n) ^ n * ((n : ℝ) ^ n / (n.factorial : ℝ)) := by
      rw [div_pow]
      field_simp [hn0.ne']
    _ ≤ (a / n) ^ n * 3 ^ n := mul_le_mul_of_nonneg_left hf (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1 <;> ring

/-- Explicit simultaneous control of the weight mass and Taylor tail. -/
theorem interpolation_factorial_error_le_quarter {k : ℕ} (hk : 0 < k)
    {A x : ℝ} (hA : 0 ≤ A) (hx : 0 ≤ x) (hAk : A ≤ 8 * k) (hxk : 512 * x ≤ k) :
    (A ^ k / (k.factorial : ℝ)) *
      ((x ^ (k + 1) / ((k + 1).factorial : ℝ)) * Real.exp x) ≤ 1 / 4 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hw : A ^ k / (k.factorial : ℝ) ≤ (24 : ℝ) ^ k := by
    refine (pow_div_factorial_le_three_scaled_pow hA hk).trans ?_
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_iff₀ hk0).mpr
    linarith only [hAk]
  have ht : x ^ (k + 1) / ((k + 1).factorial : ℝ) ≤ (3 / 512 : ℝ) ^ (k + 1) := by
    refine (pow_div_factorial_le_three_scaled_pow hx (Nat.succ_pos k)).trans ?_
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_iff₀ hk1).mpr
    push_cast
    linarith only [hxk]
  have he : Real.exp x ≤ (3 : ℝ) ^ k := by
    refine (Real.exp_le_exp.mpr ?_).trans (exp_nat_le_three_pow k)
    linarith only [hxk, hx]
  calc
    _ ≤ (24 : ℝ) ^ k * ((3 / 512 : ℝ) ^ (k + 1) * 3 ^ k) := by gcongr
    _ = (3 / 512 : ℝ) * (27 / 64 : ℝ) ^ k := by
      calc
        _ = (3 / 512 : ℝ) * ((24 : ℝ) * (3 / 512) * 3) ^ k := by
          rw [mul_pow, mul_pow, pow_succ]
          ring
        _ = _ := by norm_num
    _ ≤ (3 / 512 : ℝ) * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 27 / 64) (by norm_num)) (by norm_num)
    _ ≤ _ := by norm_num

/-- A calibrated sufficiently dense block has positive real part throughout its full window. -/
theorem calibrated_exponential_block_re_ge_three_quarters {k : ℕ} (hk : 0 < k)
    {z : Fin (k + 1) → ℂ} (hz : Function.Injective z) {T δ B R : ℝ}
    (hδ : 0 < δ) (hB : 0 ≤ B) (hR : 0 ≤ R) (hb : ∀ i, ‖z i‖ ≤ B)
    (hsep : ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ ≤ ‖z i - z j‖)
    (hcal : ∀ i, Complex.exp ((T : ℂ) * z i) = zeroInterpolationWeight z i)
    (hweight : 2 * B / δ ≤ 8 * k) (hwindow : 512 * (R * B) ≤ k)
    {v : ℝ} (hv : |v| ≤ R) :
    (3 / 4 : ℝ) ≤ (∑ i, Complex.exp (((T + v : ℝ) : ℂ) * z i)).re := by
  have herr := (norm_calibrated_exponential_block_sub_one_le hz hδ hB hR hb hsep hcal hv).trans
    (interpolation_factorial_error_le_quarter hk (by positivity) (mul_nonneg hR hB) hweight hwindow)
  have hre := Complex.abs_re_le_norm ((∑ i, Complex.exp (((T + v : ℝ) : ℂ) * z i)) - 1)
  simp only [Complex.sub_re, Complex.one_re] at hre
  have hh := (abs_le.mp (hre.trans herr)).1
  linarith only [hh]

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
