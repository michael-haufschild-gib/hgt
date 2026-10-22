import GaloisForLFunctions.BezoutValuationIncidence.CrossScaleLawOfEveryOrder
import GaloisForLFunctions.BezoutValuationIncidence.SmoothLargeScaleRowsOfEveryOrder
import GaloisForLFunctions.BezoutValuationIncidence.DualNormOfTheCrossScaleFunctional

/-!
# Higher-Order Kernel Statistic and All-Order Dual-Norm Law

In `DualNormOfTheCrossScaleFunctional`, the cross-scale functional
`rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' + rowBeta N c * finiteHarmonicSum N c'`
was expanded only to order `L = 2`, leaving a fourth-order remainder
`6 * (∑ p ∈ S, p^3) * (∑ n, |c' n| / n^4)` that blows up in the balanced regime `P ≍ Q`.

This file generalizes the dual-norm theory to arbitrary order `L`:
1. Defines `higherOrderKernelStatistic N L c' d := ∑ n ∈ Icc 1 N, c' n * potentialTerms d n L`
   and proves its step recursion `higherOrderKernelStatistic_succ`.
2. Proves the order-`L` cross-scale dual-norm approximation (`abs_rowBilinear_sub_higherOrderKernelStatistic_le`),
   adversarial attainment (`exists_rowBilinear_ge_higherOrderDualNorm`), and upper bound
   (`abs_rowBilinear_le_higherOrderDualNorm`), reducing the remainder to order `L + 2`.
3. Couples the order-`L` dual norm with `SmoothLargeScaleRowsOfEveryOrder` to bound
   `∑ p ∈ S, |higherOrderKernelStatistic N L c' p| / p` directly by the `L`-th backward-difference
   smoothness norm `smoothnessNorm N L c'` (`sum_abs_higherOrderKernelStatistic_le_smoothnessNorm`).
-/

noncomputable section

open Finset BigOperators Real RHTower GaloisForLFunctions.BiScaleUncertainty

namespace GaloisForLFunctions.SmoothBernoulliPoleCalibration

open GaloisForLFunctions.BezoutValuationIncidence

/-- The order-`L` cross-scale kernel statistic at modulus `d` against the large-scale row `c'`. -/
def higherOrderKernelStatistic (N L : ℕ) (c' : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, c' n * potentialTerms d n L

@[simp]
theorem higherOrderKernelStatistic_zero (N : ℕ) (c' : ℕ → ℝ) (d : ℕ) :
    higherOrderKernelStatistic N 0 c' d = 0 := by
  simp [higherOrderKernelStatistic, potentialTerms]

/-- Step recursion adding the order-`L` chain potential layer `Y_{d,L}(jn) u_L(jn)` to
`higherOrderKernelStatistic`. -/
theorem higherOrderKernelStatistic_succ (N L : ℕ) (c' : ℕ → ℝ) (d : ℕ) :
    higherOrderKernelStatistic N (L + 1) c' d =
      higherOrderKernelStatistic N L c' d +
        ∑ n ∈ Icc 1 N, c' n *
          ∑' j : ℕ, chainPotential d L ((j + 1) * n) * pronicWeight L ((j + 1) * n) := by
  unfold higherOrderKernelStatistic potentialTerms
  rw [← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [Finset.sum_range_succ, mul_add]

/-- Fubini swap expressing the bilinear potential sum in terms of `higherOrderKernelStatistic`. -/
theorem sum_mul_potentialTerms_eq_sum_higherOrderKernelStatistic (N L : ℕ) (c c' : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / (d : ℝ)) * potentialTerms d n L =
      ∑ d ∈ Icc 1 N, c d / (d : ℝ) * higherOrderKernelStatistic N L c' d := by
  unfold higherOrderKernelStatistic
  rw [sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun n _ => by ring

/-- Order-`L` approximation of the shifted cross-scale functional by `higherOrderKernelStatistic`,
with remainder of order `O((∑ d, |c d| d^{L+1}) (∑ n, |c' n| / n^{L+2}))`. -/
theorem abs_rowBilinear_sub_higherOrderKernelStatistic_le (N L : ℕ) (c c' : ℕ → ℝ) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
      rowBeta N c * finiteHarmonicSum N c' -
      ∑ d ∈ Icc 1 N, c d / (d : ℝ) * higherOrderKernelStatistic N L c' d| ≤
      (2 : ℝ) ^ L * (L + 1).factorial *
        (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ (L + 1)) *
        (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (L + 2)) := by
  rw [← sum_mul_potentialTerms_eq_sum_higherOrderKernelStatistic]
  exact abs_rowBilinear_add_mean_add_beta_sub_potentialTerms_le N L c c'

/-- Adversarial sign choice attaining the order-`L` dual norm `∑ d ∈ S, |Λ_{d,L}(c')| / d`
up to the order-`(L + 2)` remainder. -/
theorem exists_rowBilinear_ge_higherOrderDualNorm (N L : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (c' : ℕ → ℝ) :
    ∃ c : ℕ → ℝ,
      (∀ d, d ∉ S → c d = 0) ∧
      (∀ d ∈ S, |c d| = 1) ∧
      ∑ d ∈ S, |higherOrderKernelStatistic N L c' d| / (d : ℝ) -
        (2 : ℝ) ^ L * (L + 1).factorial *
          (∑ d ∈ S, (d : ℝ) ^ (L + 1)) * (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (L + 2)) ≤
        rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
          rowBeta N c * finiteHarmonicSum N c' := by
  classical
  let c : ℕ → ℝ := fun d =>
    if d ∈ S then (if 0 ≤ higherOrderKernelStatistic N L c' d then 1 else -1) else 0
  refine ⟨c, ?_, ?_, ?_⟩
  · intro d hd
    simp [c, hd]
  · intro d hd
    simp only [c, hd, ↓reduceIte]
    split_ifs <;> simp
  · have h_approx := abs_rowBilinear_sub_higherOrderKernelStatistic_le N L c c'
    have h_sum_c : ∑ d ∈ Icc 1 N, c d / (d : ℝ) * higherOrderKernelStatistic N L c' d =
        ∑ d ∈ S, |higherOrderKernelStatistic N L c' d| / (d : ℝ) := by
      rw [← sum_subset hS]
      · refine sum_congr rfl fun d hd => ?_
        simp only [c, hd, ↓reduceIte]
        split_ifs with hpos
        · rw [abs_of_nonneg hpos]; ring
        · rw [abs_of_neg (not_le.mp hpos)]; ring
      · intro d _ hdS
        simp [c, hdS]
    have h_sum_d : ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ (L + 1) =
        ∑ d ∈ S, (d : ℝ) ^ (L + 1) := by
      rw [← sum_subset hS]
      · refine sum_congr rfl fun d hd => ?_
        have hc1 : |c d| = 1 := by
          simp only [c, hd, ↓reduceIte]
          split_ifs <;> simp
        rw [hc1, one_mul]
      · intro d _ hdS
        simp [c, hdS]
    rw [h_sum_c, h_sum_d] at h_approx
    linarith [abs_le.mp h_approx]

/-- Order-`L` dual-norm upper bound on the shifted cross-scale functional for any modulus weight `c`
supported on `S ⊆ Icc 1 N` with `|c d| ≤ 1`. -/
theorem abs_rowBilinear_le_higherOrderDualNorm (N L : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (c c' : ℕ → ℝ) (hc_supp : ∀ d, d ∉ S → c d = 0) (hc_le : ∀ d ∈ S, |c d| ≤ 1) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
      rowBeta N c * finiteHarmonicSum N c'| ≤
      ∑ d ∈ S, |higherOrderKernelStatistic N L c' d| / (d : ℝ) +
        (2 : ℝ) ^ L * (L + 1).factorial *
          (∑ d ∈ S, (d : ℝ) ^ (L + 1)) * (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (L + 2)) := by
  have h_approx := abs_rowBilinear_sub_higherOrderKernelStatistic_le N L c c'
  have h_main : |∑ d ∈ Icc 1 N, c d / (d : ℝ) * higherOrderKernelStatistic N L c' d| ≤
      ∑ d ∈ S, |higherOrderKernelStatistic N L c' d| / (d : ℝ) := by
    have h_eq : ∑ d ∈ Icc 1 N, c d / (d : ℝ) * higherOrderKernelStatistic N L c' d =
        ∑ d ∈ S, c d / (d : ℝ) * higherOrderKernelStatistic N L c' d := by
      rw [← sum_subset hS]
      intro d _ hdS
      rw [hc_supp d hdS, zero_div, zero_mul]
    rw [h_eq]
    calc |∑ d ∈ S, c d / (d : ℝ) * higherOrderKernelStatistic N L c' d|
      _ ≤ ∑ d ∈ S, |c d / (d : ℝ) * higherOrderKernelStatistic N L c' d| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ S, |higherOrderKernelStatistic N L c' d| / (d : ℝ) := by
          refine sum_le_sum fun d hd => ?_
          have hd_pos : (0 : ℝ) < d := by
            have := (mem_Icc.mp (hS hd)).1
            positivity
          rw [abs_mul, abs_div, abs_of_pos hd_pos, div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_right
            (mul_le_of_le_one_left (abs_nonneg _) (hc_le d hd)) (le_of_lt hd_pos)
  have h_rem_d : ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ (L + 1) ≤
      ∑ d ∈ S, (d : ℝ) ^ (L + 1) := by
    have h_eq : ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ (L + 1) =
        ∑ d ∈ S, |c d| * (d : ℝ) ^ (L + 1) := by
      rw [← sum_subset hS]
      intro d _ hdS
      rw [hc_supp d hdS, abs_zero, zero_mul]
    rw [h_eq]
    refine sum_le_sum fun d hd => ?_
    exact mul_le_of_le_one_left (by positivity) (hc_le d hd)
  have h_rem : (2 : ℝ) ^ L * (L + 1).factorial *
        (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ (L + 1)) *
        (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (L + 2)) ≤
      (2 : ℝ) ^ L * (L + 1).factorial *
        (∑ d ∈ S, (d : ℝ) ^ (L + 1)) *
        (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (L + 2)) := by
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left h_rem_d (by positivity)
    · exact sum_nonneg (fun n _ => div_nonneg (abs_nonneg _) (by positivity))
  have h_tri := abs_sub_abs_le_abs_sub
    (rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
      rowBeta N c * finiteHarmonicSum N c')
    (∑ d ∈ Icc 1 N, c d / (d : ℝ) * higherOrderKernelStatistic N L c' d)
  linarith

/-- Pointwise smoothness bound on `higherOrderKernelStatistic` at a prime modulus `p`. -/
theorem abs_higherOrderKernelStatistic_le_smoothnessNorm (N L : ℕ) (c' : ℕ → ℝ) (p : ℕ)
    (hp : p.Prime) (hc' : ∀ n, c' n ≠ 0 → L + 1 ≤ n ∧ n ≤ N) :
    |higherOrderKernelStatistic N L c' p| ≤
      (L : ℝ) * (2 * (4 : ℝ) ^ L * (L + 1).factorial * (p : ℝ) ^ (L + 2) *
        smoothnessNorm N L c' +
        (2 : ℝ) ^ L * L.factorial * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2) := by
  unfold higherOrderKernelStatistic
  exact abs_sum_mul_potentialTerms_le hp hc'

/-- All-order smooth dual-norm bound: for any prime set `S ⊆ Icc 1 N` and any row `c'`
supported in `[L + 1, N]`, the dual norm `∑ p ∈ S, |Λ_{p,L}(c')| / p` is controlled by
`smoothnessNorm N L c' * (∑ p ∈ S, p^{L+1})` plus `(∑ p ∈ S, 1/p) * (∑ n, |c' n| / n^2)`. -/
theorem sum_abs_higherOrderKernelStatistic_le_smoothnessNorm (N L : ℕ) (S : Finset ℕ)
    (hp : ∀ p ∈ S, p.Prime) (c' : ℕ → ℝ) (hc' : ∀ n, c' n ≠ 0 → L + 1 ≤ n ∧ n ≤ N) :
    ∑ p ∈ S, |higherOrderKernelStatistic N L c' p| / (p : ℝ) ≤
      2 * (L : ℝ) * (4 : ℝ) ^ L * (L + 1).factorial *
        (∑ p ∈ S, (p : ℝ) ^ (L + 1)) * smoothnessNorm N L c' +
      (L : ℝ) * (2 : ℝ) ^ L * L.factorial *
        (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) * (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2) := by
  calc ∑ p ∈ S, |higherOrderKernelStatistic N L c' p| / (p : ℝ)
    _ ≤ ∑ p ∈ S, ((L : ℝ) * (2 * (4 : ℝ) ^ L * (L + 1).factorial * (p : ℝ) ^ (L + 2) *
          smoothnessNorm N L c' +
          (2 : ℝ) ^ L * L.factorial * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2)) / (p : ℝ) := by
        refine sum_le_sum fun p hpS => ?_
        have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (hp p hpS).pos
        exact div_le_div_of_nonneg_right
          (abs_higherOrderKernelStatistic_le_smoothnessNorm N L c' p (hp p hpS) hc')
          (le_of_lt hp_pos)
    _ = 2 * (L : ℝ) * (4 : ℝ) ^ L * (L + 1).factorial *
          (∑ p ∈ S, (p : ℝ) ^ (L + 1)) * smoothnessNorm N L c' +
        (L : ℝ) * (2 : ℝ) ^ L * L.factorial *
          (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) * (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2) := by
        have h_term : ∀ p ∈ S,
            ((L : ℝ) * (2 * (4 : ℝ) ^ L * (L + 1).factorial * (p : ℝ) ^ (L + 2) *
              smoothnessNorm N L c' +
              (2 : ℝ) ^ L * L.factorial * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2)) / (p : ℝ) =
            (2 * (L : ℝ) * (4 : ℝ) ^ L * (L + 1).factorial * smoothnessNorm N L c') *
              (p : ℝ) ^ (L + 1) +
            ((L : ℝ) * (2 : ℝ) ^ L * L.factorial * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2) *
              ((1 : ℝ) / (p : ℝ)) := by
          intro p hpS
          have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hp p hpS).ne_zero
          rw [pow_succ (p : ℝ) (L + 1)]
          field_simp [hp_ne]
        rw [sum_congr rfl h_term, sum_add_distrib, ← mul_sum, ← mul_sum]
        ring

end GaloisForLFunctions.SmoothBernoulliPoleCalibration
