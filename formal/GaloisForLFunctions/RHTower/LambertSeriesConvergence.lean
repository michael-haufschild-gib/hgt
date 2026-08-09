import GaloisForLFunctions.RHTower.LambertQuadraticFactor
import GaloisForLFunctions.RHTower.ZetaRealBound

/-!
# Normal convergence of a Lambert series

The Lambert form of a moment-Borel transform is `∑_n (1/n) w_n/(1 + 2 w_n cos α + w_n²)` with
`w_n → 0` at a power rate.  Once `‖w_n‖ ≤ 1/2` the quadratic factor is bounded below by `1/4`, so
the `n`-th term is `O(n^{-1-b})` and the series converges absolutely.

Only the tail matters, so the finitely many terms where `‖w_n‖` may approach one — the terms whose
denominators carry the poles — are irrelevant to convergence.

* `GaloisForLFunctions.RHTower.norm_lambertTerm_le`;
* `GaloisForLFunctions.RHTower.summable_lambertTerm`;
* `GaloisForLFunctions.RHTower.rpow_scale_identity`.
-/

open Complex

namespace GaloisForLFunctions.RHTower

/-- The termwise bound: a power-decaying `w` with `‖w‖ ≤ 1/2` gives a term of order `n^{-1-b}`. -/
theorem norm_lambertTerm_le {α : ℝ} {C b : ℝ} {w : ℕ → ℂ} (n : ℕ)
    (hw : ‖w n‖ ≤ C / ((n : ℝ) + 1) ^ b) (hsmall : ‖w n‖ ≤ 1 / 2) :
    ‖(1 / ((n : ℂ) + 1)) * (w n / (1 + 2 * w n * (Real.cos α : ℂ) + (w n) ^ 2))‖
      ≤ 4 * C / ((n : ℝ) + 1) ^ (1 + b) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  have hnormn : ‖(1 : ℂ) / ((n : ℂ) + 1)‖ = 1 / ((n : ℝ) + 1) := by
    rw [norm_div, norm_one, hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  -- the quadratic factor is bounded below
  have hle1 : ‖w n‖ ≤ 1 := le_trans hsmall (by norm_num)
  have hquad := norm_lambertQuadratic_ge α hle1
  have hquarter : (1 : ℝ) / 4 ≤ (1 - ‖w n‖) ^ 2 := by nlinarith [norm_nonneg (w n)]
  have hqpos : (0 : ℝ) < ‖1 + 2 * w n * (Real.cos α : ℂ) + (w n) ^ 2‖ := by
    have : (0 : ℝ) < 1 / 4 := by norm_num
    linarith [le_trans hquarter hquad]
  have hqge : (1 : ℝ) / 4 ≤ ‖1 + 2 * w n * (Real.cos α : ℂ) + (w n) ^ 2‖ :=
    le_trans hquarter hquad
  -- assemble
  have hCnn : (0 : ℝ) ≤ C := by
    have hbp : (0 : ℝ) < ((n : ℝ) + 1) ^ b := Real.rpow_pos_of_pos hpos b
    have h := le_trans (norm_nonneg (w n)) hw
    have hmul := (le_div_iff₀ hbp).mp h
    simpa using hmul
  have hfrac : ‖w n / (1 + 2 * w n * (Real.cos α : ℂ) + (w n) ^ 2)‖
      ≤ 4 * (C / ((n : ℝ) + 1) ^ b) := by
    rw [norm_div]
    rw [div_le_iff₀ hqpos]
    have hmul : 4 * (C / ((n : ℝ) + 1) ^ b) * (1 / 4)
        ≤ 4 * (C / ((n : ℝ) + 1) ^ b) * ‖1 + 2 * w n * (Real.cos α : ℂ) + (w n) ^ 2‖ := by
      have hnn : (0 : ℝ) ≤ 4 * (C / ((n : ℝ) + 1) ^ b) := by
        have hb : (0 : ℝ) < ((n : ℝ) + 1) ^ b := Real.rpow_pos_of_pos hpos b
        positivity
      exact mul_le_mul_of_nonneg_left hqge hnn
    nlinarith [hw]
  calc ‖(1 / ((n : ℂ) + 1)) * (w n / (1 + 2 * w n * (Real.cos α : ℂ) + (w n) ^ 2))‖
      = ‖(1 : ℂ) / ((n : ℂ) + 1)‖ * ‖w n / (1 + 2 * w n * (Real.cos α : ℂ) + (w n) ^ 2)‖ := by
        rw [norm_mul]
    _ ≤ (1 / ((n : ℝ) + 1)) * (4 * (C / ((n : ℝ) + 1) ^ b)) := by
        rw [hnormn]
        exact mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = 4 * C / ((n : ℝ) + 1) ^ (1 + b) := by
        rw [Real.rpow_add hpos, Real.rpow_one]
        field_simp

/-- **The Lambert series converges absolutely.** -/
theorem summable_lambertTerm {α : ℝ} {C b : ℝ} (hb : 0 < b) {w : ℕ → ℂ}
    (hw : ∀ n, ‖w n‖ ≤ C / ((n : ℝ) + 1) ^ b) (hsmall : ∀ n, ‖w n‖ ≤ 1 / 2) :
    Summable fun n : ℕ =>
      (1 / ((n : ℂ) + 1)) * (w n / (1 + 2 * w n * (Real.cos α : ℂ) + (w n) ^ 2)) := by
  have hCnn : (0 : ℝ) ≤ C := by
    have hb0 : (0 : ℝ) < ((0 : ℕ) : ℝ) + 1 := by norm_num
    have hbp : (0 : ℝ) < (((0 : ℕ) : ℝ) + 1) ^ b := Real.rpow_pos_of_pos hb0 b
    have h := le_trans (norm_nonneg (w 0)) (hw 0)
    have hmul := (le_div_iff₀ hbp).mp h
    simpa using hmul
  have hmaj : Summable fun n : ℕ => 4 * C / ((n : ℝ) + 1) ^ (1 + b) := by
    have hbase : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ (1 + b) :=
      summable_one_div_nat_add_one_rpow (by linarith)
    have := hbase.mul_left (4 * C)
    refine this.congr fun n => ?_
    rw [mul_one_div]
  refine Summable.of_norm_bounded hmaj fun n => ?_
  exact norm_lambertTerm_le n (hw n) (hsmall n)

/-- **The scale identity behind the Lambert regrouping.**  Splitting the Dirichlet denominator
`(n+1)^{1+sk}` against the power `(2π)^{sk}` produces one factor `n+1` and the `k`-th power of the
single scale `(2π(n+1))^s` — which is what turns a double sum into a Lambert series in the
variables `ξ/(2π(n+1))^s`. -/
theorem rpow_scale_identity {P : ℝ} (hP : 0 < P) (s : ℝ) (n k : ℕ) :
    P ^ (s * (k + 1)) * (((n : ℝ) + 1) ^ (1 + s * (k + 1)))
      = ((n : ℝ) + 1) * ((P * ((n : ℝ) + 1)) ^ s) ^ (k + 1) := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hstep : ((P * ((n : ℝ) + 1)) ^ s) ^ (k + 1)
      = P ^ (s * (k + 1)) * ((n : ℝ) + 1) ^ (s * (k + 1)) := by
    rw [← Real.rpow_natCast ((P * ((n : ℝ) + 1)) ^ s) (k + 1), ← Real.rpow_mul (by positivity),
      Real.mul_rpow hP.le hN.le]
    push_cast
    ring_nf
  rw [hstep, Real.rpow_add hN, Real.rpow_one]
  ring

end GaloisForLFunctions.RHTower
