import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailContactGrowthDetectsZeros
import Mathlib.NumberTheory.AbelSummation

/-!+# Exact Abel summation for the weighted prime error

The literal power-weighted prime prefix is expressed through Chebyshev's
counting function. This identity preserves its jumps and permits a zero
trace to be integrated before the harmonic convolution is taken.
-/

noncomputable section

open Finset MeasureTheory
open scoped ArithmeticFunction.zeta

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- Finite Abel summation of the actual von Mangoldt coefficients. -/
theorem sum_powerTailWeight_vonMangoldt_eq (a : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, powerTailWeight a n * ArithmeticFunction.vonMangoldt n) =
      x ^ (-a) * Chebyshev.psi x +
        a * ∫ t in Set.Ioc (1 : ℝ) x, t ^ (-a - 1) * Chebyshev.psi t := by
  have hd {t : ℝ} (ht : 0 < t) :
      deriv (fun y : ℝ => y ^ (-a)) t = -a * t ^ (-a - 1) :=
    (Real.hasDerivAt_rpow_const (p := -a) (Or.inl ht.ne')).deriv
  have hcont : ContinuousOn (fun t : ℝ => -a * t ^ (-a - 1)) (Set.Icc 1 x) := by
    intro t ht
    exact (continuousAt_const.mul
      (Real.hasDerivAt_rpow_const (p := -a - 1)
        (Or.inl (zero_lt_one.trans_le ht.1).ne')).continuousAt).continuousWithinAt
  have hi : IntegrableOn (deriv (fun t : ℝ => t ^ (-a))) (Set.Icc 1 x) :=
    hcont.integrableOn_Icc.congr_fun
      (fun t ht => (hd (zero_lt_one.trans_le ht.1)).symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n) (f := fun t : ℝ => t ^ (-a))
    (a := 1) (b := x) zero_le_one hx
    (fun t ht => (Real.hasDerivAt_rpow_const
      (Or.inl (zero_lt_one.trans_le ht.1).ne')).differentiableAt) hi
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at h
  simp only [Nat.floor_one, Chebyshev.psi_eq_zero_of_lt_two
    (by norm_num : (1 : ℝ) < 2), mul_zero, sub_zero] at h
  have hint : (∫ t in Set.Ioc (1 : ℝ) x,
      deriv (fun y : ℝ => y ^ (-a)) t * Chebyshev.psi t) =
      -a * ∫ t in Set.Ioc (1 : ℝ) x, t ^ (-a - 1) * Chebyshev.psi t := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    rw [hd (zero_lt_one.trans ht.1)]
    ring
  rw [hint] at h
  have hsum : (∑ n ∈ Finset.Ioc 1 ⌊x⌋₊,
      (n : ℝ) ^ (-a) * ArithmeticFunction.vonMangoldt n) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (n : ℝ) ^ (-a) * ArithmeticFunction.vonMangoldt n := by
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hn).1.le, (Finset.mem_Ioc.mp hn).2⟩
    · intro n hn hnot
      have he : n = 1 := by
        have hm := Finset.mem_Icc.mp hn
        have hm' : ¬ (1 < n ∧ n ≤ ⌊x⌋₊) := by simpa only [Finset.mem_Ioc] using hnot
        omega
      subst n
      simp
  rw [hsum] at h
  simpa only [powerTailWeight, neg_mul, sub_neg_eq_add] using h

/-- The centered weighted arithmetic prefix retains the exact finite
Chebyshev integral and the elementary power prefix. -/
theorem sum_powerTailPrimeDeviation_eq_abel (a : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, powerTailPrimeDeviation a n) =
      x ^ (-a) * Chebyshev.psi x +
        a * (∫ t in Set.Ioc (1 : ℝ) x, t ^ (-a - 1) * Chebyshev.psi t) -
        powerTailPrefix a x := by
  have he : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, powerTailPrimeDeviation a n) =
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        powerTailWeight a n * ArithmeticFunction.vonMangoldt n) - powerTailPrefix a x := by
    rw [powerTailPrefix, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have hh := (Finset.mem_Icc.mp hn).1; omega
    change powerTailWeight a n *
      (ArithmeticFunction.vonMangoldt n - (ζ : ArithmeticFunction ℝ) n) = _
    simp [hn0, mul_sub]
  rw [he, sum_powerTailWeight_vonMangoldt_eq a hx]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
