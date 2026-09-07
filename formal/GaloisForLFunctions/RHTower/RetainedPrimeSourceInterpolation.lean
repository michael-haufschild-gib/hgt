import GaloisForLFunctions.RHTower.RetainedPrimeSourceMellin
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Exact square-root interpolation of retained source pairings

The continuous summatory primitive agrees with its discrete Abel sum at every
integer cutoff, and is affine in the square-root clock between consecutive
integers. One-sided integer values therefore yield a nonnegative real part
on the entire ray. Applied to the actual retained divisor convolution, its
integer values are exactly the literal source pairings.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace RHTower

private def sqrtIntegrationKernel (x : ℝ) : ℂ := (1 / (2 * Real.sqrt x) : ℝ)

private lemma sqrtIntegrationKernel_eq {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (1 / 2 : ℂ) / (2 * x) = sqrtIntegrationKernel x := by
  have hc : (x : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt x : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx.le]
    norm_num
  have hs := Real.sq_sqrt hx.le
  have hn : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  rw [hc, sqrtIntegrationKernel]
  push_cast
  have hsC : (Real.sqrt x : ℂ) ^ 2 = (x : ℂ) := by exact_mod_cast hs
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hnC : (Real.sqrt x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  apply (div_eq_div_iff (mul_ne_zero (by norm_num) hxC)
    (mul_ne_zero (by norm_num) hnC)).mpr
  linear_combination 2 * hsC

private lemma continuousOn_sqrtIntegrationKernel {a b : ℝ} (ha : 0 < a) :
    ContinuousOn sqrtIntegrationKernel (Icc a b) := by
  apply Complex.continuous_ofReal.comp_continuousOn
  apply continuousOn_const.div (continuousOn_const.mul Real.continuous_sqrt.continuousOn)
  intro x hx
  exact mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr (ha.trans_le hx.1)).ne'

private lemma integral_sqrtIntegrationKernel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, sqrtIntegrationKernel t) = (Real.sqrt b : ℂ) - (Real.sqrt a : ℂ) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact (Real.hasDerivAt_sqrt (ha.trans_le hx.1).ne').ofReal_comp
  · exact (continuousOn_sqrtIntegrationKernel ha).intervalIntegrable_of_Icc hab

private lemma integrableOn_sqrtSummatory (b : ℕ → ℂ) {a x : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t => sqrtIntegrationKernel t * ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, b n) (Icc a x) :=
  integrableOn_mul_sum_Icc b ha.le
    ((continuousOn_sqrtIntegrationKernel ha).integrableOn_Icc)

private lemma squareRootSummatoryPrimitive_eq_intervalIntegral (b : ℕ → ℂ) {x : ℝ} (hx : 1 ≤ x) :
    squareRootSummatoryPrimitive b x =
      ∫ t in (1 : ℝ)..x, sqrtIntegrationKernel t * ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, b n := by
  rw [squareRootSummatoryPrimitive_eq_integral, intervalIntegral.integral_of_le hx,
    integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [sqrtIntegrationKernel_eq (by have := ht.1; linarith)]

/-- Integer cutoffs of the continuous primitive are exactly the discrete
square-root Abel sums; there is no endpoint correction. -/
lemma squareRootSummatoryPrimitive_nat (b : ℕ → ℂ) (M : ℕ) :
    squareRootSummatoryPrimitive b M =
      ∑ k ∈ Finset.Icc 1 (M - 1), ((Real.sqrt (k + 1 : ℕ) - Real.sqrt k : ℝ) : ℂ) *
        ∑ n ∈ Finset.Icc 1 k, b n := by
  rcases M.eq_zero_or_pos with rfl | hM
  · rw [squareRootSummatoryPrimitive_eq_integral]
    simp
  have hM1 : 1 ≤ M := hM
  have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  rw [squareRootSummatoryPrimitive_eq_intervalIntegral b hM1R]
  have ht := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (μ := volume)
    (f := fun t => sqrtIntegrationKernel t * ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, b n)
    (a := fun n : ℕ => (n : ℝ)) hM1 (by
      intro k hk
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by
        exact_mod_cast Nat.le_succ k : (k : ℝ) ≤ (k + 1 : ℕ))]
      apply integrableOn_sqrtSummatory b
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk.1))
  rw [Nat.cast_one] at ht
  rw [← ht]
  have hsets : Finset.Ico 1 M = Finset.Icc 1 (M - 1) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [hsets]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
  have hkk : (k : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.le_succ k
  rw [intervalIntegral.integral_congr_Ioo_of_le hkk (g := fun t =>
    sqrtIntegrationKernel t * ∑ n ∈ Finset.Icc 1 k, b n) (by
      intro t ht
      dsimp only
      have htlo := ht.1
      have hf : ⌊t⌋₊ = k := (Nat.floor_eq_iff (by linarith : 0 ≤ t)).mpr
        ⟨ht.1.le, by exact_mod_cast ht.2⟩
      rw [hf]), intervalIntegral.integral_mul_const,
    integral_sqrtIntegrationKernel hk0 hkk]
  push_cast
  rfl

end RHTower

namespace RHTower

/-- Between consecutive integer cutoffs, the continuous primitive is affine in
the square-root clock, with slope equal to the actual summatory coefficient. -/
lemma squareRootSummatoryPrimitive_between (b : ℕ → ℂ) {k : ℕ} (hk : 1 ≤ k)
    {x : ℝ} (hkx : (k : ℝ) ≤ x) (hxk : x ≤ (k + 1 : ℕ)) :
    squareRootSummatoryPrimitive b x = squareRootSummatoryPrimitive b k +
      ((Real.sqrt x - Real.sqrt k : ℝ) : ℂ) * ∑ n ∈ Finset.Icc 1 k, b n := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hx1 : 1 ≤ x := hkR.trans hkx
  have hk0 : (0 : ℝ) < k := by linarith
  have hleft : IntervalIntegrable
      (fun t => sqrtIntegrationKernel t * ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, b n) volume 1 k := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hkR]
    exact integrableOn_sqrtSummatory b zero_lt_one
  have hright : IntervalIntegrable
      (fun t => sqrtIntegrationKernel t * ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, b n) volume k x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hkx]
    exact integrableOn_sqrtSummatory b hk0
  rw [squareRootSummatoryPrimitive_eq_intervalIntegral b hx1,
    squareRootSummatoryPrimitive_eq_intervalIntegral b hkR,
    ← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  congr 1
  rw [intervalIntegral.integral_congr_Ioo_of_le hkx (g := fun t =>
    sqrtIntegrationKernel t * ∑ n ∈ Finset.Icc 1 k, b n) (by
      intro t ht
      dsimp only
      have htlo := ht.1
      have hf : ⌊t⌋₊ = k := (Nat.floor_eq_iff (by linarith : 0 ≤ t)).mpr
        ⟨ht.1.le, by have h := ht.2.trans_le hxk; exact_mod_cast h⟩
      rw [hf]), intervalIntegral.integral_mul_const, integral_sqrtIntegrationKernel hk0 hkx]
  push_cast
  rfl

/-- Nonnegative integer source pairings give a nonnegative continuous carrier
on the entire ray. This uses exact interpolation, not an asymptotic estimate. -/
lemma squareRootSummatoryPrimitive_re_nonneg (b : ℕ → ℂ)
    (hN : ∀ N : ℕ, 0 ≤ (squareRootSummatoryPrimitive b N).re) {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ (squareRootSummatoryPrimitive b x).re := by
  let k : ℕ := ⌊x⌋₊
  have hk : 1 ≤ k := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr (by simpa using hx)
  have hkx : (k : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxk : x ≤ (k + 1 : ℕ) := by exact_mod_cast (Nat.lt_floor_add_one x).le
  have hkk : (k : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.le_succ k
  have he := squareRootSummatoryPrimitive_between b hk hkx hxk
  have he1 := squareRootSummatoryPrimitive_between b hk hkk le_rfl
  have h0 := hN k
  have h1 := hN (k + 1)
  rw [he1] at h1
  rw [he]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at h1 ⊢
  have hu : 0 ≤ Real.sqrt x - Real.sqrt k := sub_nonneg.mpr (Real.sqrt_le_sqrt hkx)
  have hv : Real.sqrt x - Real.sqrt k ≤ Real.sqrt (k + 1 : ℕ) - Real.sqrt k :=
    sub_le_sub_right (Real.sqrt_le_sqrt hxk) _
  by_cases hA : 0 ≤ (∑ n ∈ Finset.Icc 1 k, b n).re
  · exact add_nonneg h0 (mul_nonneg hu hA)
  · have hm := mul_le_mul_of_nonpos_right hv (le_of_not_ge hA)
    linarith

end RHTower

namespace RHTower

/-- The continuous retained primitive agrees with the complete literal source
pairing at every integer cutoff. -/
lemma squareRootSummatoryPrimitive_retained_nat
    (P : Finset ℕ) (y : Finset ℕ → ℂ) (M : ℕ) :
    squareRootSummatoryPrimitive (retainedPrimeDivisorConvolution P y) M =
      retainedPrimeSourceMean P y M := by
  rw [squareRootSummatoryPrimitive_nat, retainedPrimeSourceMean_eq_convolution_abel]

/-- A one-sided complete retained functional gives the positive continuous
carrier required for the next Landau continuation step. -/
lemma retainedPrimeSourceMean_re_nonneg_ray
    (P : Finset ℕ) (y : Finset ℕ → ℂ)
    (hN : ∀ M : ℕ, 0 ≤ (retainedPrimeSourceMean P y M).re)
    {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ (squareRootSummatoryPrimitive (retainedPrimeDivisorConvolution P y) x).re := by
  apply squareRootSummatoryPrimitive_re_nonneg _ _ hx
  intro M
  rw [squareRootSummatoryPrimitive_retained_nat]
  exact hN M

end RHTower
