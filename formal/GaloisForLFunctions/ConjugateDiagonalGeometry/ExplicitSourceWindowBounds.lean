import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceWindowError

/-!
# Vanishing bounds for prescribed source regulators

The moving C² window has a quadratic transform envelope. A sixth-degree
local logarithmic error bound is absorbed by the quartic exponential
regulator, yielding one vanishing majorant for the whole window.
-/

open Complex Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry

/-- Linear ordinate motion and logarithmic Hecke motion have a quadratic envelope. -/
lemma moving_source_square_exponent_le (j n : ℕ) (L τ : ℝ)
    (hτ : |τ| ≤ (n : ℝ)) (hL : (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1)) :
    2 * (((n : ℝ) + 3 + |τ|) ^ 2 + (j : ℝ) * |L| * ((n : ℝ) + 7 / 2)) ≤
      50 * (n : ℝ) ^ 2 + 56 := by
  have hsq : ((n : ℝ) + 3 + |τ|) ^ 2 ≤ (2 * (n : ℝ) + 3) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hτ]) 2
  have hlog : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ) + 1)
    linarith only [h]
  have hj : (j : ℝ) * |L| ≤ 2 * (n : ℝ) := by linarith only [hL, hlog]
  have hp := mul_le_mul_of_nonneg_right hj (by positivity : 0 ≤ (n : ℝ) + 7 / 2)
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 + 1 := by
    nlinarith only [sq_nonneg ((n : ℝ) - 1 / 2)]
  nlinarith only [hsq, hp, hn]

/-- The disc area and logarithmic-square mass share one sixth-degree bound. -/
lemma source_log_polynomial_le (C : ℝ) (n : ℕ) :
    Real.pi * ((n : ℝ) + 2) ^ 2 / 2 + 8 * C * ((n : ℝ) + 1) ^ 6 ≤
      (2 * Real.pi + 8 * C) * ((n : ℝ) + 1) ^ 6 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ht1 : 1 ≤ (n : ℝ) + 1 := by linarith only [hn]
  have ht4 : 1 ≤ ((n : ℝ) + 1) ^ 4 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one ht1 4
  have ht26 : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 6 := by
    calc
      ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 4 :=
        le_mul_of_one_le_right (sq_nonneg ((n : ℝ) + 1)) ht4
      _ = _ := by ring
  have hr := pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ) + 2)
    (show (n : ℝ) + 2 ≤ 2 * ((n : ℝ) + 1) by linarith only [hn]) 2
  have hp := mul_le_mul_of_nonneg_left hr Real.pi_pos.le
  have hpoly := mul_le_mul_of_nonneg_left ht26 Real.pi_pos.le
  nlinarith only [hp, hpoly]

/-- Quartic regulator decay absorbs both the local mass and the moving transform. -/
lemma source_poly_exp_window_le {C : ℝ} (hC : 0 ≤ C) (j n : ℕ) (L τ : ℝ)
    (hτ : |τ| ≤ (n : ℝ)) (hL : (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1)) :
    (Real.pi * ((n : ℝ) + 2) ^ 2 / 2 + 8 * C * ((n : ℝ) + 1) ^ 6) *
      Real.exp (-(((n : ℝ) + 1) ^ 4) +
        2 * (((n : ℝ) + 3 + |τ|) ^ 2 + (j : ℝ) * |L| * ((n : ℝ) + 7 / 2))) ≤
    (2 * Real.pi + 8 * C) * Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ht : (n : ℝ) + 1 ≤ Real.exp (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (Real.exp_pos (n : ℝ))
    rw [Real.log_exp] at h
    linarith only [h]
  have hpoly : ((n : ℝ) + 1) ^ 6 ≤ Real.exp (6 * (n : ℝ)) := by
    have h := pow_le_pow_left₀ (by positivity) ht 6
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat] using h
  have hfour : (n : ℝ) ^ 4 ≤ ((n : ℝ) + 1) ^ 4 :=
    pow_le_pow_left₀ hn (by linarith only [hn]) 4
  have hlinear : (n : ℝ) ≤ (n : ℝ) ^ 2 + 1 := by
    nlinarith only [sq_nonneg ((n : ℝ) - 1 / 2)]
  have hE := moving_source_square_exponent_le j n L τ hτ hL
  have hcoef : 0 ≤ 2 * Real.pi + 8 * C := by positivity
  calc
    (Real.pi * ((n : ℝ) + 2) ^ 2 / 2 + 8 * C * ((n : ℝ) + 1) ^ 6) *
        Real.exp (-(((n : ℝ) + 1) ^ 4) +
          2 * (((n : ℝ) + 3 + |τ|) ^ 2 + (j : ℝ) * |L| * ((n : ℝ) + 7 / 2))) ≤
      ((2 * Real.pi + 8 * C) * Real.exp (6 * (n : ℝ))) *
        Real.exp (-(((n : ℝ) + 1) ^ 4) +
          2 * (((n : ℝ) + 3 + |τ|) ^ 2 + (j : ℝ) * |L| * ((n : ℝ) + 7 / 2))) :=
      mul_le_mul_of_nonneg_right ((source_log_polynomial_le C n).trans
        (mul_le_mul_of_nonneg_left hpoly hcoef)) (Real.exp_pos _).le
    _ = (2 * Real.pi + 8 * C) *
        Real.exp (6 * (n : ℝ) - ((n : ℝ) + 1) ^ 4 +
          2 * (((n : ℝ) + 3 + |τ|) ^ 2 + (j : ℝ) * |L| * ((n : ℝ) + 7 / 2))) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith only [hfour, hlinear, hE])) hcoef

/-- The joint error envelope vanishes by quadratic exponential decay in `n²`. -/
lemma tendsto_explicitWindowError (B : ℝ) :
    Tendsto (fun n : ℕ => B * Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have h := (RiemannGaussian.tendsto_exp_neg_quadratic_add_linear_atTop
    (ε := 1) zero_lt_one 0 56 62).comp ht
  have he : Tendsto (fun n : ℕ =>
      Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62)) atTop (𝓝 0) := by
    apply h.congr'
    filter_upwards with n
    change Real.exp (-1 * ((n : ℝ) ^ 2 - 0) ^ 2 + 56 * (n : ℝ) ^ 2 + 62) =
      Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62)
    congr 1
    ring
  simpa only [mul_zero] using he.const_mul B

end GaloisForLFunctions.ConjugateDiagonalGeometry
