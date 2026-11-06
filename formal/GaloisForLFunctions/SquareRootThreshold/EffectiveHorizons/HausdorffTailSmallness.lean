import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HausdorffSaddle
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Uniform smallness of the three Hausdorff tails

Elementary exponential inequalities make the Gaussian complement and the
two far tails smaller than a fixed fraction of the saddle core.
-/

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle

theorem mul_exp_neg_le_four_div {t : ℝ} (ht : 0 < t) :
    t * Real.exp (-t) ≤ 4 / t := by
  have h : t / 2 ≤ Real.exp (t / 2) := by linarith only [Real.add_one_le_exp (t / 2)]
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ t / 2) h 2
  have heq : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq] at hsq
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos t) ht]
  nlinarith only [hsq]

/-- A polynomial factor does not obstruct the two exponentially decaying tails. -/
theorem order_tail_le_inverse (p : ℕ) (hp : 0 < p) :
    4096 * Real.exp 1 * (p : ℝ) * (4 : ℝ)⁻¹ ^ p +
      2 * (p : ℝ) * Real.exp (-4 * (p : ℝ)) ≤ (16384 * Real.exp 1 + 8) / (p : ℝ) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hbase : (4 : ℝ)⁻¹ ≤ Real.exp (-1) := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (by norm_num) (Real.exp_pos 1)).mpr
      (by linarith only [Real.exp_one_lt_d9])
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹) hbase p
  rw [← Real.exp_nat_mul] at hpow
  have heq : (p : ℝ) * (-1) = -(p : ℝ) := by ring
  rw [heq] at hpow
  have hlow := Real.exp_le_exp.mpr (show -4 * (p : ℝ) ≤ -(p : ℝ) by linarith only [hpR])
  have h₁ := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4096 * Real.exp 1 * (p : ℝ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 2 * (p : ℝ) by positivity)
  have hsmall := mul_exp_neg_le_four_div hpR
  have h₃ := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 4096 * Real.exp 1 + 2 by positivity)
  have heq' : (4096 * Real.exp 1 + 2) * (4 / (p : ℝ)) =
      (16384 * Real.exp 1 + 8) / (p : ℝ) := by ring
  rw [heq'] at h₃
  nlinarith only [h₁, h₂, h₃]

/-- Lower bounds on both order and squared width make the Gaussian loss uniformly small. -/
theorem gaussian_factor_le {C p w : ℝ} (_hC : 0 < C)
    (hp : 131072 * (8000 * C) ≤ p) (hw : 131072 * (8000 * C) ≤ w ^ 2) :
    C * Real.exp (-min p (w ^ 2) / 131072) ≤ 1 / 8000 := by
  have hm : 131072 * (8000 * C) ≤ min p (w ^ 2) := le_min hp hw
  have he := Real.add_one_le_exp (min p (w ^ 2) / 131072)
  have hE : 8000 * C ≤ Real.exp (min p (w ^ 2) / 131072) := by linarith only [hm, he]
  rw [show -min p (w ^ 2) / 131072 = -(min p (w ^ 2) / 131072) by ring,
    Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith only [hE]

end GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle
