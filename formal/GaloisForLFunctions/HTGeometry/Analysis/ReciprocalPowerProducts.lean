import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!+# Uniform bounds for reciprocal-power products

The secant bound for powers gives a telescoping majorant for
`∏_{n=2}^{N+1} (1 - n⁻ˢ)⁻¹`. The quadratic case is exact.
This is the finite-product estimate of Li–Yang, Lemma 2.1,
*Mixed sums of infinite multiple zeta-star values with restricted indices*.
-/

namespace GaloisForLFunctions.HTGeometry.ReciprocalPowerProducts

open Finset

/-- The secant slope of `x ↦ x^(k+1)` between one and two. -/
def slope (k : ℕ) : ℝ := 2 ^ (k + 1) - 1

theorem slope_ge_one (k : ℕ) : 1 ≤ slope k := by
  have h := one_le_pow₀ (n := k) (show (1 : ℝ) ≤ 2 by norm_num)
  dsimp [slope]
  rw [pow_succ]
  linarith

/-- Beyond two, the power graph lies above its secant through one and two. -/
theorem secant_le_power (k n : ℕ) :
    slope k * ((n : ℝ) + 1) + 1 ≤ ((n : ℝ) + 2) ^ (k + 1) := by
  induction k with
  | zero => simp only [slope]; ring_nf; rfl
  | succ k ih =>
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hc : 0 ≤ slope k := (slope_ge_one k).trans' zero_le_one
      have hmul := mul_le_mul_of_nonneg_right ih (by positivity : 0 ≤ (n : ℝ) + 2)
      have hrem := mul_nonneg (mul_nonneg hn (by positivity : 0 ≤ (n : ℝ) + 1)) hc
      have hs : slope (k + 1) = 2 * slope k + 1 := by
        simp only [slope, pow_succ]
        ring
      rw [hs, pow_succ]
      nlinarith only [hmul, hrem]

/-- Reciprocal-power product over the integers from two through `N+1`. -/
noncomputable def product (k N : ℕ) : ℝ :=
  ∏ n ∈ range N, (1 - 1 / ((n : ℝ) + 2) ^ (k + 2))⁻¹

theorem factor_pos (k n : ℕ) :
    0 < 1 - 1 / ((n : ℝ) + 2) ^ (k + 2) := by
  have hp : 1 < ((n : ℝ) + 2) ^ (k + 2) :=
    one_lt_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by omega)
  exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hp)

theorem product_nonneg (k N : ℕ) : 0 ≤ product k N := by
  exact Finset.prod_nonneg fun n _ => (inv_pos.mpr (factor_pos k n)).le

/-- Each factor is bounded by a ratio whose adjacent terms cancel. -/
theorem factor_le_ratio (k n : ℕ) :
    (1 - 1 / ((n : ℝ) + 2) ^ (k + 2))⁻¹ ≤
      (((slope k * ((n : ℝ) + 1) + 1) * ((n : ℝ) + 2)) /
        ((slope k * ((n : ℝ) + 2) + 1) * ((n : ℝ) + 1))) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hc : 0 < slope k := lt_of_lt_of_le zero_lt_one (slope_ge_one k)
  have hp : 0 < ((n : ℝ) + 2) ^ (k + 2) := by positivity
  have hsec := mul_le_mul_of_nonneg_right (secant_le_power k n)
    (by positivity : 0 ≤ (n : ℝ) + 2)
  rw [← pow_succ] at hsec
  have hquot : ((slope k * ((n : ℝ) + 1) + 1) * ((n : ℝ) + 2)) /
      ((n : ℝ) + 2) ^ (k + 2) ≤ 1 := (div_le_one hp).mpr hsec
  rw [← one_div, div_le_div_iff₀ (factor_pos k n) (by positivity),
    one_mul, mul_sub, mul_one, mul_one_div]
  nlinarith only [hquot]

/-- Uniform rational envelope, sharp for exponent two. -/
theorem product_le_envelope (k N : ℕ) :
    product k N ≤
      (slope k + 1) * ((N : ℝ) + 1) / (slope k * ((N : ℝ) + 1) + 1) := by
  have hc : 0 < slope k := lt_of_lt_of_le zero_lt_one (slope_ge_one k)
  induction N with
  | zero => simp [product, ne_of_gt (by positivity : 0 < slope k + 1)]
  | succ N ih =>
      rw [product, prod_range_succ]
      change product k N * _ ≤ _
      calc
        product k N * _ ≤
            ((slope k + 1) * ((N : ℝ) + 1) /
              (slope k * ((N : ℝ) + 1) + 1)) *
            (((slope k * ((N : ℝ) + 1) + 1) * ((N : ℝ) + 2)) /
              ((slope k * ((N : ℝ) + 2) + 1) * ((N : ℝ) + 1))) :=
          mul_le_mul ih (factor_le_ratio k N)
            (inv_pos.mpr (factor_pos k N)).le (by positivity)
        _ = _ := by
          push_cast
          field_simp
          ring

/-- Every finite product lies strictly below the limiting rational envelope. -/
theorem product_lt_uniform (k N : ℕ) :
    product k N < (slope k + 1) / slope k := by
  have hc : 0 < slope k := lt_of_lt_of_le zero_lt_one (slope_ge_one k)
  refine (product_le_envelope k N).trans_lt ?_
  apply (div_lt_div_iff₀ (by positivity) hc).mpr
  nlinarith only [hc]

/-- Exponent two gives the exact telescoping product. -/
theorem product_quadratic (N : ℕ) :
    product 0 N = 2 * ((N : ℝ) + 1) / ((N : ℝ) + 2) := by
  induction N with
  | zero => norm_num [product]
  | succ N ih =>
      rw [product, prod_range_succ]
      change product 0 N * _ = _
      rw [ih]
      have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      have hpow : ((N : ℝ) + 2) ^ 2 - 1 ≠ 0 := by nlinarith only [hn]
      push_cast
      field_simp
      ring

/-- Every factor is at least one, so extending the product increases its value. -/
theorem product_monotone (k : ℕ) : Monotone (product k) := by
  apply monotone_nat_of_le_succ
  intro N
  change product k N ≤ ∏ n ∈ range (N + 1), (1 - 1 / ((n : ℝ) + 2) ^ (k + 2))⁻¹
  rw [prod_range_succ]
  change product k N ≤ product k N * _
  apply le_mul_of_one_le_right (product_nonneg k N)
  apply (one_le_inv₀ (factor_pos k N)).mpr
  exact sub_le_self _ (by positivity)

theorem product_ge_one (k N : ℕ) : 1 ≤ product k N := by
  simpa only [product, range_zero, prod_empty] using product_monotone k (Nat.zero_le N)

/-- The same cutoff-independent bound holds after deleting any factors. -/
theorem subproduct_lt_uniform (k : ℕ) (S : Finset ℕ) :
    (∏ n ∈ S, (1 - 1 / ((n : ℝ) + 2) ^ (k + 2))⁻¹) <
      (slope k + 1) / slope k := by
  have hsub : S ⊆ range (S.sup id + 1) := by
    intro n hn
    exact mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
  refine lt_of_le_of_lt
    (Finset.prod_le_prod_of_subset_of_one_le hsub
      (fun n _ => (inv_pos.mpr (factor_pos k n)).le) ?_)
    (product_lt_uniform k (S.sup id + 1))
  intro n _ _
  exact (one_le_inv₀ (factor_pos k n)).mpr (sub_le_self _ (by positivity))

#print axioms product_le_envelope
#print axioms product_quadratic
#print axioms subproduct_lt_uniform

end GaloisForLFunctions.HTGeometry.ReciprocalPowerProducts
