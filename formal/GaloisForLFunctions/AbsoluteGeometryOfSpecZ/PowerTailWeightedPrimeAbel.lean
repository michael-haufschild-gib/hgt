import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailContactGrowthDetectsZeros
import Mathlib.NumberTheory.AbelSummation

/-!
# Exact Abel summation for the weighted prime error

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

/-- The remainder transported by power-weighted Abel summation. -/
def weightedAbelRemainder (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  x ^ (-a) * f x + a * ∫ t in Set.Ioc (1 : ℝ) x, t ^ (-a - 1) * f t

private theorem abs_powerWeightedIntegrand_le {a κ C : ℝ} {f : ℝ → ℝ}
    (hB : ∀ t : ℝ, 1 ≤ t → |f t| ≤ C * t ^ κ) {t : ℝ} (ht : 1 ≤ t) :
    |t ^ (-a - 1) * f t| ≤ C * t ^ (κ - a - 1) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
  calc
    _ ≤ t ^ (-a - 1) * (C * t ^ κ) :=
      mul_le_mul_of_nonneg_left (hB t ht) (Real.rpow_nonneg ht0.le _)
    _ = C * (t ^ (-a - 1) * t ^ κ) := by ring
    _ = _ := by rw [← Real.rpow_add ht0]; congr 2; ring

/-- The actual weighted remainder is integrable on every finite interval. -/
theorem integrableOn_powerWeightedIntegrand {a κ C : ℝ} {f : ℝ → ℝ}
    (hκ : a < κ) (hf : AEStronglyMeasurable f (volume.restrict (Set.Ici 1)))
    (hB : ∀ t : ℝ, 1 ≤ t → |f t| ≤ C * t ^ κ) {x : ℝ} (hx : 1 ≤ x) :
    IntegrableOn (fun t => t ^ (-a - 1) * f t) (Set.Ioc 1 x) := by
  have hp : IntervalIntegrable (fun t : ℝ => C * t ^ (κ - a - 1)) volume 1 x :=
    (intervalIntegral.intervalIntegrable_rpow'
      (by linarith only [hκ] : (-1 : ℝ) < κ - a - 1)).const_mul C
  have hfm := hf.mono_measure (Measure.restrict_mono
    (show Set.Ioc (1 : ℝ) x ⊆ Set.Ici 1 from fun _ ht => ht.1.le) le_rfl)
  refine ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mp hp).mono'
    ((measurable_id.pow_const (-a - 1)).aestronglyMeasurable.mul hfm) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simpa only [Real.norm_eq_abs] using abs_powerWeightedIntegrand_le hB ht.1.le

/-- A power envelope is shifted by exactly the weight exponent under
finite Abel summation. The positive exponent gap pays the primitive. -/
theorem abs_weightedAbelRemainder_le {a κ C : ℝ} {f : ℝ → ℝ}
    (ha : 0 ≤ a) (hκ : a < κ) (hC : 0 ≤ C)
    (hB : ∀ t : ℝ, 1 ≤ t → |f t| ≤ C * t ^ κ)
    {x : ℝ} (hx : 1 ≤ x) :
    |weightedAbelRemainder a f x| ≤ C * (1 + a / (κ - a)) * x ^ (κ - a) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hd : 0 < κ - a := sub_pos.mpr hκ
  have hpower : IntervalIntegrable (fun t : ℝ => C * t ^ (κ - a - 1)) volume 1 x :=
    (intervalIntegral.intervalIntegrable_rpow'
      (by linarith only [hκ] : (-1 : ℝ) < κ - a - 1)).const_mul C
  have hI : |∫ t in Set.Ioc (1 : ℝ) x, t ^ (-a - 1) * f t| ≤
      C * (x ^ (κ - a) / (κ - a)) := by
    have hi : IntegrableOn (fun t : ℝ => C * t ^ (κ - a - 1)) (Set.Ioc 1 x) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mp hpower
    have hbound : |∫ t in Set.Ioc (1 : ℝ) x, t ^ (-a - 1) * f t| ≤
        ∫ t in Set.Ioc (1 : ℝ) x, C * t ^ (κ - a - 1) := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simpa only [Real.norm_eq_abs] using abs_powerWeightedIntegrand_le hB ht.1.le
    apply hbound.trans
    rw [← intervalIntegral.integral_of_le hx, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith only [hκ] : (-1 : ℝ) < κ - a - 1)),
      show κ - a - 1 + 1 = κ - a by ring, Real.one_rpow]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) hd.le) hC
  have hhead : |x ^ (-a) * f x| ≤ C * x ^ (κ - a) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    calc
      _ ≤ x ^ (-a) * (C * x ^ κ) :=
        mul_le_mul_of_nonneg_left (hB x hx) (Real.rpow_nonneg hx0.le _)
      _ = C * (x ^ (-a) * x ^ κ) := by ring
      _ = _ := by rw [← Real.rpow_add hx0]; congr 2; ring
  unfold weightedAbelRemainder
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_nonneg ha]
  calc
    _ ≤ C * x ^ (κ - a) + a * (C * (x ^ (κ - a) / (κ - a))) :=
      add_le_add hhead (mul_le_mul_of_nonneg_left hI ha)
    _ = _ := by ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
