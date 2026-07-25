import GaloisForLFunctions.RHTower.XiPoissonVerticalType

/-!
# Moment-weighted summability of the Poisson weight

The derivatives of the Poisson trace carry a factor `alpha^^n`, so the real-variable route to the
converse needs the weight to stay summable against any polynomial factor.  It does, for the same
reason the weight itself is summable: a height `R` satisfies `‖alpha^‖ <= R + 1/2` because the
displacement is bounded by `1/2`, and `y^(n+2) exp(-sigma y) <= (n+2)! / sigma^(n+2)`, so the
polynomially weighted term is dominated by a constant times `1 / ‖alpha‖^2`.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

theorem norm_xiPoissonPoint (q : XiZeroCopy) :
    ‖xiPoissonPoint q‖ = ‖xiSpectralPoint q‖ := by
  unfold xiPoissonPoint
  split_ifs with h
  · rfl
  · exact norm_neg _

theorem norm_xiPoissonPoint_le (q : XiZeroCopy) :
    ‖xiPoissonPoint q‖ ≤ (xiPoissonPoint q).re + 1 / 2 := by
  have h := Complex.norm_le_abs_re_add_abs_im (xiPoissonPoint q)
  have hre : |(xiPoissonPoint q).re| = (xiPoissonPoint q).re :=
    abs_of_nonneg (xiPoissonPoint_re_nonneg q)
  have him : |(xiPoissonPoint q).im| < 1 / 2 := abs_xiPoissonPoint_im_lt_half q
  rw [hre] at h
  linarith

/-- **Polynomially weighted summability.**  The Poisson weight survives any power of the spectral
modulus. -/
theorem summable_pow_mul_xiPoissonWeight {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    Summable (fun q : XiZeroCopy => ‖xiPoissonPoint q‖ ^ n * xiPoissonWeight σ q) := by
  have hC : (0 : ℝ) < Real.exp (σ / 2) * ((n + 2).factorial : ℝ) / σ ^ (n + 2) := by
    have hfac : (0 : ℝ) < ((n + 2).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos (n + 2)
    positivity
  have hbase : Summable (fun q : XiZeroCopy =>
      Real.exp (σ / 2) * ((n + 2).factorial : ℝ) / σ ^ (n + 2) *
        (1 / ‖xiSpectralPoint q‖ ^ 2)) :=
    xiSpectralPoint_inv_sq_summable.mul_left _
  refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hbase
  · exact mul_nonneg (pow_nonneg (norm_nonneg _) n) (xiPoissonWeight_pos σ q).le
  · set y : ℝ := (xiPoissonPoint q).re + 1 / 2 with hy
    have hnormle : ‖xiPoissonPoint q‖ ≤ y := norm_xiPoissonPoint_le q
    have hN : (4 : ℝ) < ‖xiSpectralPoint q‖ := four_lt_norm_xiSpectralPoint q
    have hNpos : (0 : ℝ) < ‖xiSpectralPoint q‖ := by linarith
    have hNy : ‖xiSpectralPoint q‖ ≤ y := by
      rw [← norm_xiPoissonPoint q]; exact hnormle
    have hypos : (0 : ℝ) < y := by linarith
    have hexpw : xiPoissonWeight σ q = Real.exp (σ / 2) * Real.exp (-(σ * y)) := by
      rw [xiPoissonWeight, ← Real.exp_add, hy]
      congr 1
      ring
    have hfac : (0 : ℝ) < ((n + 2).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos (n + 2)
    have hσp : (0 : ℝ) < σ ^ (n + 2) := pow_pos hσ _
    have hkey : y ^ (n + 2) * Real.exp (-(σ * y)) ≤ ((n + 2).factorial : ℝ) / σ ^ (n + 2) := by
      have hx : 0 ≤ σ * y := (mul_pos hσ hypos).le
      have hq := Real.pow_div_factorial_le_exp (σ * y) hx (n + 2)
      rw [div_le_iff₀ hfac, mul_pow] at hq
      rw [Real.exp_neg, ← div_eq_mul_inv,
        div_le_div_iff₀ (Real.exp_pos _) hσp]
      nlinarith [hq]
    rw [mul_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < ‖xiSpectralPoint q‖ ^ 2)]
    have h1 : ‖xiPoissonPoint q‖ ^ n ≤ y ^ n := pow_le_pow_left₀ (norm_nonneg _) hnormle n
    have h2 : ‖xiSpectralPoint q‖ ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hNy 2
    have h3 : (0 : ℝ) ≤ Real.exp (σ / 2) * Real.exp (-(σ * y)) := by positivity
    calc ‖xiPoissonPoint q‖ ^ n * xiPoissonWeight σ q * ‖xiSpectralPoint q‖ ^ 2
        ≤ y ^ n * (Real.exp (σ / 2) * Real.exp (-(σ * y))) * y ^ 2 := by
          rw [hexpw]
          exact mul_le_mul (mul_le_mul_of_nonneg_right h1 h3) h2 (by positivity) (by positivity)
      _ = Real.exp (σ / 2) * (y ^ (n + 2) * Real.exp (-(σ * y))) := by ring
      _ ≤ Real.exp (σ / 2) * (((n + 2).factorial : ℝ) / σ ^ (n + 2)) :=
          mul_le_mul_of_nonneg_left hkey (Real.exp_pos _).le
      _ = Real.exp (σ / 2) * ((n + 2).factorial : ℝ) / σ ^ (n + 2) := by ring

end

end RHTower
