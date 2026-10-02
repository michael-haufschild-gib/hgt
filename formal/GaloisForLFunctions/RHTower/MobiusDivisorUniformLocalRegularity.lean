import GaloisForLFunctions.RHTower.DivisorContinuousHeadRegularity
import GaloisForLFunctions.RHTower.PrimeMassLowerBound

/-!
# Uniform local regularity of the literal processed source

The square-root divisor remainder bounds the unit source's actual integral
density. Its Lipschitz bound survives every finite Mobius core on a fixed
physical interval, with a constant independent of that core. This is the
source input for transporting a large moving-head endpoint to bulk energy.
-/

noncomputable section
open MeasureTheory Set Finset
namespace RHTower

private def unitDensity (t : ℝ) : ℝ :=
  if 1 < t then primeFreeDivisorDefect ⌊t⌋₊ / (2 * Real.sqrt t) else 0

private theorem density_measurable : Measurable unitDensity := by
  have hD : Measurable (fun t : ℝ => primeFreeDivisorDefect ⌊t⌋₊) :=
    (measurable_of_countable primeFreeDivisorDefect).comp Nat.measurable_floor
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (hD.div (measurable_const.mul Real.continuous_sqrt.measurable)) measurable_const

private theorem density_bound (t : ℝ) : ‖unitDensity t‖ ≤ 12 := by
  by_cases ht : 1 < t
  · have ht0 : 0 < t := by linarith
    have hn : 1 ≤ ⌊t⌋₊ := (Nat.le_floor_iff ht0.le).mpr (by simpa using ht.le)
    have hb := abs_primeFreeDivisorDefect_le hn
    have hs := Real.sqrt_le_sqrt (Nat.floor_le ht0.le)
    rw [unitDensity, if_pos ht, Real.norm_eq_abs, abs_div,
      abs_of_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr ht0))]
    apply (div_le_iff₀ (mul_pos (by norm_num) (Real.sqrt_pos.mpr ht0))).mpr
    linarith
  · simp [unitDensity, ht]

private theorem density_integrable (a b : ℝ) : IntervalIntegrable unitDensity volume a b :=
  (intervalIntegrable_const (c := (12 : ℝ))).mono_fun'
    density_measurable.aestronglyMeasurable (Filter.Eventually.of_forall density_bound)

private theorem unit_eq_integral (x : ℝ) :
    divisorContinuousUnitHead x = ∫ t in (1 : ℝ)..x, unitDensity t := by
  by_cases hx : x ≤ 1
  · rw [divisorContinuousUnitHead_eq_zero hx]
    symm
    calc
      _ = ∫ _t in (1 : ℝ)..x, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_ge hx] at ht
        simp [unitDensity, not_lt.mpr ht.2]
      _ = 0 := by simp
  have hx1 : 1 ≤ x := (lt_of_not_ge hx).le
  rw [divisorContinuousUnitHead, squareRootSummatoryPrimitive_eq_integral,
    intervalIntegral.integral_of_le hx1, integral_Ioc_eq_integral_Ioo]
  have he :
      (∫ t in Ioo (1 : ℝ) x,
        ((t : ℂ) ^ (1 / 2 : ℂ) / (2*t)) *
          ∑ n ∈ Icc 1 ⌊t⌋₊, (primeFreeDivisorIncrement n : ℂ)) =
        ∫ t in Ioo (1 : ℝ) x, (unitDensity t : ℂ) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
    have hroot : (t : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt t : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ht0.le]
      norm_num
    dsimp only
    rw [hroot, ← Complex.ofReal_sum, sum_primeFreeDivisorIncrement,
      unitDensity, if_pos ht.1]
    push_cast
    have hsC : (Real.sqrt t : ℂ)^2 = (t : ℂ) := by exact_mod_cast Real.sq_sqrt ht0.le
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    have hnC : (Real.sqrt t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
    field_simp
    linear_combination (primeFreeDivisorDefect ⌊t⌋₊ : ℂ) * hsC
  rw [he, integral_complex_ofReal, Complex.ofReal_re]

/-- Uniform regularity of the actual unit source, including the zero ray and all integer edges. -/
theorem abs_divisorContinuousUnitHead_sub_le (x y : ℝ) :
    |divisorContinuousUnitHead x - divisorContinuousUnitHead y| ≤ 12 * |x-y| := by
  rw [unit_eq_integral, unit_eq_integral,
    intervalIntegral.integral_interval_sub_left (density_integrable 1 x) (density_integrable 1 y)]
  simpa only [Real.norm_eq_abs] using
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := y) (b := x) (fun t _ => density_bound t)

/-- Core-independent local regularity on every physical cutoff interval. -/
theorem abs_mobiusDivisorContinuousHead_sub_le (P : Finset ℕ) (N : ℕ)
    {x y : ℝ} (hx : x ≤ N) (hy : y ≤ N) :
    |mobiusDivisorContinuousHead P x - mobiusDivisorContinuousHead P y| ≤
      24 * Real.sqrt N * |x-y| := by
  let D := (∏ p ∈ P, p).divisors
  let S := D.filter (fun d => d ≤ N)
  let f : ℕ → ℝ := fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    Real.sqrt d * (divisorContinuousUnitHead (x/d) - divisorContinuousUnitHead (y/d))
  have hS : S ⊆ Icc 1 N := by
    intro d hd
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors (mem_filter.mp hd).1, (mem_filter.mp hd).2⟩
  have he : mobiusDivisorContinuousHead P x - mobiusDivisorContinuousHead P y =
      ∑ d ∈ S, f d := by
    have hfull : mobiusDivisorContinuousHead P x - mobiusDivisorContinuousHead P y =
        ∑ d ∈ D, f d := by
      rw [mobiusDivisorContinuousHead, mobiusDivisorContinuousHead, ← sum_sub_distrib]
      apply sum_congr rfl
      intro d _
      dsimp [f]
      ring
    rw [hfull]
    symm
    apply sum_subset (filter_subset _ _) ?_
    intro d hd hn
    have hdN : N < d := by simpa [S, hd] using hn
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hNd : (N : ℝ) ≤ d := by exact_mod_cast hdN.le
    have hx1 : x/(d : ℝ) ≤ 1 := (div_le_one hd0).mpr (hx.trans hNd)
    have hy1 : y/(d : ℝ) ≤ 1 := (div_le_one hd0).mpr (hy.trans hNd)
    simp [f, divisorContinuousUnitHead_eq_zero hx1, divisorContinuousUnitHead_eq_zero hy1]
  have hterm (d : ℕ) (hd : d ∈ S) : |f d| ≤ 12 * |x-y| / Real.sqrt d := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp (hS hd)).1
    have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd0
    have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    have hcoef : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * Real.sqrt d ≤ Real.sqrt d :=
      by nlinarith
    have hb := abs_divisorContinuousUnitHead_sub_le (x/d) (y/d)
    rw [← sub_div, abs_div, abs_of_pos hd0] at hb
    calc
      |f d| = (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| * Real.sqrt d) *
          |divisorContinuousUnitHead (x/d) - divisorContinuousUnitHead (y/d)| := by
        simp only [f, abs_mul, abs_of_pos hs]
      _ ≤ Real.sqrt d * (12 * (|x-y| / d)) :=
        mul_le_mul hcoef hb (abs_nonneg _) hs.le
      _ = 12 * |x-y| / Real.sqrt d := by
        field_simp
        rw [Real.sq_sqrt hd0.le]
        ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ S, |f d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ S, 12 * |x-y| / Real.sqrt d := sum_le_sum hterm
    _ ≤ ∑ d ∈ Icc 1 N, 12 * |x-y| / Real.sqrt d :=
      sum_le_sum_of_subset_of_nonneg hS (fun d _ _ => by positivity)
    _ = (12 * |x-y|) * ∑ d ∈ Icc 1 N, 1 / Real.sqrt d := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ (12 * |x-y|) * (2 * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left (sum_one_div_sqrt_le N) (by positivity)
    _ = _ := by ring

end RHTower
