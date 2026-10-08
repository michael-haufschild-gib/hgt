import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseLocalPolynomialModels
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.FieldSimp

/-!
# Literal finite-period realization of local polynomial valuation weights

Nested divisibility partitions the coefficient sequence into exact valuation
classes. Counting each class over a complete period gives its geometric weight.
-/

open Polynomial Finset
noncomputable section
namespace RHTower.WeilSingularArithmetic

def localPolynomialCoefficientUpTo (p : ℕ) (P : Polynomial ℝ) (D n : ℕ) : ℝ :=
  ∑ j ∈ range (D + 1), if p ^ j ∣ n then P.coeff j else 0

theorem localPolynomialCoefficientUpTo_periodic (p : ℕ) (P : Polynomial ℝ) (D : ℕ) :
    Function.Periodic (localPolynomialCoefficientUpTo p P D) (p ^ D) := by
  intro n
  unfold localPolynomialCoefficientUpTo
  apply Finset.sum_congr rfl
  intro j hj
  have hper : p ^ j ∣ p ^ D := Nat.pow_dvd_pow p (Nat.le_of_lt_succ (mem_range.mp hj))
  have hd : p ^ j ∣ n + p ^ D ↔ p ^ j ∣ n := by
    simpa only [Nat.add_comm] using Nat.dvd_add_right hper
  simp only [hd]

theorem localPolynomialCoefficientUpTo_eq_prefix (p : ℕ) (P : Polynomial ℝ)
    (D n : ℕ) (hd : p ^ D ∣ n) :
    localPolynomialCoefficientUpTo p P D n = localPolynomialPrefix P D := by
  unfold localPolynomialCoefficientUpTo localPolynomialPrefix
  apply Finset.sum_congr rfl
  intro j hj
  exact if_pos ((Nat.pow_dvd_pow p (Nat.le_of_lt_succ (mem_range.mp hj))).trans hd)

/-- Exact valuation partition, before any averaging or asymptotic limit. -/
theorem localPolynomial_valuation_partition (p : ℕ) (P : Polynomial ℝ)
    (F : ℝ → ℝ) (D n : ℕ) :
    F (localPolynomialCoefficientUpTo p P D n) =
      (∑ k ∈ range D, ((if p ^ k ∣ n then (1 : ℝ) else 0) -
        (if p ^ (k + 1) ∣ n then 1 else 0)) * F (localPolynomialPrefix P k)) +
      (if p ^ D ∣ n then (1 : ℝ) else 0) * F (localPolynomialPrefix P D) := by
  induction D with
  | zero => simp [localPolynomialCoefficientUpTo, localPolynomialPrefix]
  | succ D ih =>
    rw [Finset.sum_range_succ]
    by_cases hd : p ^ (D + 1) ∣ n
    · have hd0 : p ^ D ∣ n := (Nat.pow_dvd_pow p (Nat.le_succ D)).trans hd
      rw [localPolynomialCoefficientUpTo_eq_prefix p P (D + 1) n hd,
        if_pos hd0, if_pos hd]
      rw [localPolynomialCoefficientUpTo_eq_prefix p P D n hd0, if_pos hd0] at ih
      simp only [sub_self, zero_mul, add_zero, one_mul]
      simp only [one_mul] at ih
      linarith only [ih]
    · have he : localPolynomialCoefficientUpTo p P (D + 1) n =
          localPolynomialCoefficientUpTo p P D n := by
        simp only [localPolynomialCoefficientUpTo, Finset.sum_range_succ, if_neg hd, add_zero]
      rw [he, ih, if_neg hd]
      ring

/-- The mean of a power-divisibility indicator over an exact full period. -/
theorem localPolynomial_period_mask_mean (p : ℕ) (hp : 0 < p) (D k : ℕ) (hk : k ≤ D) :
    (∑ n ∈ Ioc 0 (p ^ D), if p ^ k ∣ n then (1 : ℝ) else 0) / (p : ℝ) ^ D =
      ((p : ℝ) ^ k)⁻¹ := by
  rw [Finset.sum_boole, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.cast_div_charZero (Nat.pow_dvd_pow p hk)]
  push_cast
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

def localPolynomialPeriodAverage (p D : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ n ∈ Ioc 0 (p ^ D), f n) / (p : ℝ) ^ D

/-- Every observable of the literal coefficient has the exact valuation weights. -/
theorem localPolynomial_period_average (p : ℕ) (hp : 0 < p) (P : Polynomial ℝ)
    (F : ℝ → ℝ) (D : ℕ) :
    localPolynomialPeriodAverage p D (fun n => F (localPolynomialCoefficientUpTo p P D n)) =
      (1 - (p : ℝ)⁻¹) * (∑ k ∈ range D, ((p : ℝ) ^ k)⁻¹ * F (localPolynomialPrefix P k)) +
        ((p : ℝ) ^ D)⁻¹ * F (localPolynomialPrefix P D) := by
  let M (k : ℕ) : ℝ :=
    (∑ n ∈ Ioc 0 (p ^ D), if p ^ k ∣ n then (1 : ℝ) else 0) / (p : ℝ) ^ D
  have hm (k : ℕ) (hk : k ≤ D) : M k = ((p : ℝ) ^ k)⁻¹ :=
    localPolynomial_period_mask_mean p hp D k hk
  have he : localPolynomialPeriodAverage p D
      (fun n => F (localPolynomialCoefficientUpTo p P D n)) =
      (∑ k ∈ range D, (M k - M (k + 1)) * F (localPolynomialPrefix P k)) +
        M D * F (localPolynomialPrefix P D) := by
    unfold localPolynomialPeriodAverage
    simp_rw [localPolynomial_valuation_partition]
    rw [Finset.sum_add_distrib, Finset.sum_comm, add_div, div_eq_mul_inv, Finset.sum_mul]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_mul, Finset.sum_sub_distrib]
      dsimp [M]
      ring
    · rw [← Finset.sum_mul]
      dsimp [M]
      ring
  rw [he, hm D le_rfl, Finset.mul_sum]
  refine congrArg₂ (· + ·) ?_ rfl
  apply Finset.sum_congr rfl
  intro k hk
  rw [hm k (Nat.le_of_lt (mem_range.mp hk)), hm (k + 1) (Nat.succ_le_of_lt (mem_range.mp hk)),
    pow_succ, mul_inv]
  ring

/-- Geometric valuation weights have the polynomial evaluation as their mean. -/
theorem localPolynomial_geometric_prefix_mean (r : ℝ) (P : Polynomial ℝ) (D : ℕ) :
    (1 - r) * (∑ k ∈ range D, r ^ k * localPolynomialPrefix P k) +
      r ^ D * localPolynomialPrefix P D =
        ∑ j ∈ range (D + 1), P.coeff j * r ^ j := by
  induction D with
  | zero => simp [localPolynomialPrefix]
  | succ D ih =>
    have hpre : localPolynomialPrefix P (D + 1) =
        localPolynomialPrefix P D + P.coeff (D + 1) := by
      simp only [localPolynomialPrefix, Finset.sum_range_succ]
    calc
      _ = ((1 - r) * (∑ k ∈ range D, r ^ k * localPolynomialPrefix P k) +
          r ^ D * localPolynomialPrefix P D) + r ^ (D + 1) * P.coeff (D + 1) := by
        rw [Finset.sum_range_succ, hpre, pow_succ]
        ring
      _ = (∑ j ∈ range (D + 1), P.coeff j * r ^ j) + P.coeff (D + 1) * r ^ (D + 1) := by
        rw [ih]
        ring
      _ = _ := (Finset.sum_range_succ (fun j => P.coeff j * r ^ j) (D + 1)).symm

theorem localPolynomial_period_mean (p : ℕ) (hp : 0 < p) (P : Polynomial ℝ) :
    localPolynomialPeriodAverage p P.natDegree
      (localPolynomialCoefficientUpTo p P P.natDegree) = P.eval (p : ℝ)⁻¹ := by
  have hm := localPolynomial_period_average p hp P id P.natDegree
  have hg := localPolynomial_geometric_prefix_mean (p : ℝ)⁻¹ P P.natDegree
  simp only [id_eq, inv_pow] at hm hg
  rw [Polynomial.eval_eq_sum_range]
  simpa only [inv_pow] using hm.trans hg

def localPolynomialPeriodVariance (p : ℕ) (P : Polynomial ℝ) : ℝ :=
  localPolynomialPeriodAverage p P.natDegree
    (fun n => (localPolynomialCoefficientUpTo p P P.natDegree n - P.eval (p : ℝ)⁻¹) ^ 2)

/-- The variance formula is the literal average over the arithmetic period. -/
theorem localPolynomial_period_variance (p : ℕ) (hp : 0 < p) (P : Polynomial ℝ) :
    localPolynomialPeriodVariance p P = localPolynomialValuationVariance (p : ℝ)⁻¹ P := by
  simpa only [localPolynomialPeriodVariance, localPolynomialValuationVariance, inv_pow] using
    localPolynomial_period_average p hp P (fun x => (x - P.eval (p : ℝ)⁻¹) ^ 2) P.natDegree

/-- The literal periodic coefficient variance detects every normalized nonconstant factor. -/
theorem localPolynomial_period_variance_zero_iff (p : ℕ) (hp : 1 < p)
    (P : Polynomial ℝ) (h0 : P.eval 0 = 1) :
    localPolynomialPeriodVariance p P = 0 ↔ P = 1 := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp
  rw [localPolynomial_period_variance p (lt_trans Nat.zero_lt_one hp)]
  exact localPolynomialValuationVariance_normalized_eq_zero_iff
    (inv_pos.mpr (lt_trans zero_lt_one hp1)) (inv_lt_one_of_one_lt₀ hp1) P h0

theorem localPolynomial_period_variance_pos (p : ℕ) (hp : 1 < p)
    (P : Polynomial ℝ) (h0 : P.eval 0 = 1) (hP : P ≠ 1) :
    0 < localPolynomialPeriodVariance p P := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp
  rw [localPolynomial_period_variance p (lt_trans Nat.zero_lt_one hp)]
  exact localPolynomialValuationVariance_pos
    (inv_pos.mpr (lt_trans zero_lt_one hp1)) (inv_lt_one_of_one_lt₀ hp1) P h0 hP

end RHTower.WeilSingularArithmetic
