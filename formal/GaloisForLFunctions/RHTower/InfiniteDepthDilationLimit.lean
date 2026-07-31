import Mathlib
import GaloisForLFunctions.RHTower.BoundedExponentDilationOperator
import GaloisForLFunctions.RHTower.MeyerPoissonTest

/-!
# Infinite exponent depth totalizes the positive dilation sum

Every positive integer has a finite maximal prime exponent, so the `m`-free coefficient
indicator converges pointwise to the indicator of the positive integers.  Under a summable
dominating bound the bounded-exponent dilation sums therefore converge to the complete
dilation sum.  For the explicit Gaussian source test the bound is a polynomial multiple of a
geometric series, so the convergence holds at every point of the ray.
-/

open Complex Filter Topology MeasureTheory Set
open scoped Classical

namespace RHTower

/-- The complete positive dilation sum. -/
noncomputable def fullDilationSum (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, if n = 0 then 0 else g ((n : ℝ) * x)

/-- A positive integer below `2 ^ m` is `m`-free. -/
theorem mFree_of_lt_two_pow {m n : ℕ} (hn : n ≠ 0) (h : n < 2 ^ m) : MFree m n := by
  intro p hp hdvd
  have h1 : p ^ m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have h2 : 2 ^ m ≤ p ^ m := Nat.pow_le_pow_left hp.two_le m
  omega

/-- Bounded exponent depth exhausts every positive integer. -/
theorem eventually_mFree {n : ℕ} (hn : n ≠ 0) : ∀ᶠ m in atTop, MFree m n := by
  filter_upwards [eventually_ge_atTop n] with m hm
  exact mFree_of_lt_two_pow hn
    (lt_of_lt_of_le n.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hm))

/-- **Infinite-depth totalization.**  The bounded-exponent dilation sums converge pointwise to
the complete dilation sum. -/
theorem tendsto_mFreeDilationSum_atTop {g : ℝ → ℂ} {x : ℝ}
    (hsum : Summable fun n : ℕ => ‖g ((n : ℝ) * x)‖) :
    Tendsto (fun m : ℕ => mFreeDilationSum m g x) atTop (𝓝 (fullDilationSum g x)) := by
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun n : ℕ => ‖g ((n : ℝ) * x)‖) hsum (fun n => ?_) ?_
  · rcases eq_or_ne n 0 with rfl | hn
    · have hzero : (fun m : ℕ => if MFree m 0 then g ((0 : ℕ) * x) else 0) = fun _ : ℕ => (0 : ℂ) :=
        funext fun m => if_neg (not_mFree_zero m)
      rw [hzero, if_pos rfl]
      exact tendsto_const_nhds
    · rw [if_neg hn]
      refine Tendsto.congr' ?_ (tendsto_const_nhds (x := g ((n : ℝ) * x)))
      filter_upwards [eventually_mFree hn] with m hm
      rw [if_pos hm]
  · filter_upwards with m k
    split_ifs
    · exact le_refl _
    · simp

/-! ## The explicit Gaussian source test -/

theorem norm_meyerPoissonTest_le (y : ℝ) :
    ‖((meyerPoissonTest y : ℝ) : ℂ)‖
      ≤ (y ^ 4 + 3 / (2 * Real.pi) * y ^ 2) * Real.exp (-Real.pi * y ^ 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Complex.norm_real, Real.norm_eq_abs, meyerPoissonTest, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  rw [abs_mul, abs_of_nonneg (sq_nonneg y)]
  have habs : |y ^ 2 - 3 / (2 * Real.pi)| ≤ y ^ 2 + 3 / (2 * Real.pi) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg y, div_nonneg (by norm_num : (0:ℝ) ≤ 3) (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  nlinarith [sq_nonneg y, habs]

theorem summable_norm_meyerPoissonTest_dilate {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => ‖((meyerPoissonTest ((n : ℝ) * x) : ℝ) : ℂ)‖ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set r : ℝ := Real.exp (-Real.pi * x) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0, hr, Real.exp_lt_one_iff]
    nlinarith
  set C : ℝ := x ^ 4 + 3 / (2 * Real.pi) * x ^ 2 with hC
  have hCpos : 0 ≤ C := by positivity
  have hgeo : Summable fun n : ℕ => C * ((n : ℝ) ^ 4 * r ^ n) :=
    (summable_pow_mul_geometric_of_norm_lt_one 4 hr1).mul_left C
  refine Summable.of_norm_bounded_eventually_nat hgeo ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / x)
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hn1 : (1 : ℕ) ≤ n := le_trans (le_max_right N 1) hn
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hy1 : (1 : ℝ) ≤ (n : ℝ) * x := by
    have : (1 / x : ℝ) ≤ (n : ℝ) := le_trans hN (by exact_mod_cast hnN)
    rw [div_le_iff₀ hx] at this
    linarith
  have hy0 : (0 : ℝ) < (n : ℝ) * x := lt_of_lt_of_le one_pos hy1
  have hexp : Real.exp (-Real.pi * ((n : ℝ) * x) ^ 2) ≤ r ^ n := by
    have hsq : (n : ℝ) * x ≤ ((n : ℝ) * x) ^ 2 := by nlinarith
    have h1 : Real.exp (-Real.pi * ((n : ℝ) * x) ^ 2) ≤ Real.exp (-Real.pi * ((n : ℝ) * x)) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have h2 : Real.exp (-Real.pi * ((n : ℝ) * x)) = r ^ n := by
      rw [hr, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [← h2]
    exact h1
  have hpoly : ((n : ℝ) * x) ^ 4 + 3 / (2 * Real.pi) * ((n : ℝ) * x) ^ 2
      ≤ C * (n : ℝ) ^ 4 := by
    have hc : (0 : ℝ) ≤ 3 / (2 * Real.pi) := by positivity
    have hx2 : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
    have h2 : ((n : ℝ)) ^ 2 ≤ ((n : ℝ)) ^ 4 := pow_le_pow_right₀ hn1' (by norm_num)
    have key : 3 / (2 * Real.pi) * ((n : ℝ) ^ 2 * x ^ 2)
        ≤ 3 / (2 * Real.pi) * ((n : ℝ) ^ 4 * x ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hx2) hc
    rw [hC]
    calc ((n : ℝ) * x) ^ 4 + 3 / (2 * Real.pi) * ((n : ℝ) * x) ^ 2
        = x ^ 4 * (n : ℝ) ^ 4 + 3 / (2 * Real.pi) * ((n : ℝ) ^ 2 * x ^ 2) := by ring
      _ ≤ x ^ 4 * (n : ℝ) ^ 4 + 3 / (2 * Real.pi) * ((n : ℝ) ^ 4 * x ^ 2) := by linarith
      _ = (x ^ 4 + 3 / (2 * Real.pi) * x ^ 2) * (n : ℝ) ^ 4 := by ring
  have hbase := norm_meyerPoissonTest_le ((n : ℝ) * x)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  calc ‖((meyerPoissonTest ((n : ℝ) * x) : ℝ) : ℂ)‖
      ≤ (((n : ℝ) * x) ^ 4 + 3 / (2 * Real.pi) * ((n : ℝ) * x) ^ 2) *
          Real.exp (-Real.pi * ((n : ℝ) * x) ^ 2) := hbase
    _ ≤ (C * (n : ℝ) ^ 4) * r ^ n :=
        mul_le_mul hpoly hexp (Real.exp_pos _).le (by positivity)
    _ = C * ((n : ℝ) ^ 4 * r ^ n) := by ring

/-- The bounded-exponent dilations of the explicit source test converge pointwise on the ray to
the complete dilation sum. -/
theorem tendsto_meyerPoissonTest_dilation {x : ℝ} (hx : 0 < x) :
    Tendsto (fun m : ℕ => mFreeDilationSum m (fun t : ℝ => ((meyerPoissonTest t : ℝ) : ℂ)) x)
      atTop (𝓝 (fullDilationSum (fun t : ℝ => ((meyerPoissonTest t : ℝ) : ℂ)) x)) :=
  tendsto_mFreeDilationSum_atTop (summable_norm_meyerPoissonTest_dilate hx)

end RHTower
