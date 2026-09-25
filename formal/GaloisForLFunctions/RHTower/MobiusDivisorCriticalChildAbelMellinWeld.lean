import GaloisForLFunctions.RHTower.MobiusDivisorCriticalAbelMellin
import GaloisForLFunctions.RHTower.RetainedPrimeSourceInterpolation
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalPrimeQuotientBands

/-!
# Literal terminal children are samples of the critical Abel primitive

At every positive prime quotient, the clipped discrete critical child agrees
with the real part of the same continuous square-root summatory primitive
whose Mellin transform is the nonflat centered-current gap. The statement
includes exact quotient endpoints, with no interpolation error.
-/

noncomputable section
open Complex Finset
namespace RHTower

private theorem criticalSourceAbelPrimitive_nat (k : ℕ) :
    (squareRootSummatoryPrimitive criticalSourceCoeff (k : ℝ)).re =
      ∑ n ∈ Ico 1 k, (Real.sqrt (n + 1 : ℕ) - Real.sqrt n) * psiDefect n := by
  rw [squareRootSummatoryPrimitive_nat]
  have hsets : Icc 1 (k - 1) = Ico 1 k := by
    ext n
    simp only [mem_Icc, mem_Ico]
    omega
  rw [hsets, Complex.re_sum]
  apply sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := (mem_Ico.mp hn).1
  rw [criticalSourceCoeff_cumulative n hn1]
  simp

private theorem criticalSourceAbelPrimitive_nat_im_zero (k : ℕ) :
    (squareRootSummatoryPrimitive criticalSourceCoeff (k : ℝ)).im = 0 := by
  rw [squareRootSummatoryPrimitive_nat, Complex.im_sum]
  apply sum_eq_zero
  intro n hn
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  rw [criticalSourceCoeff_cumulative n hn1]
  simp

/-- The critical Abel primitive is real-valued at every real cutoff, not only
at integer and rational prime-quotient samples. -/
theorem criticalSourceAbelPrimitive_eq_real (x : ℝ) :
    squareRootSummatoryPrimitive criticalSourceCoeff x =
      ((squareRootSummatoryPrimitive criticalSourceCoeff x).re : ℂ) := by
  by_cases hx : x ≤ 1
  · rw [squareRootSummatoryPrimitive_eq_integral]
    simp [Set.Ioo_eq_empty_of_le hx]
  · have hx1 : 1 ≤ x := (lt_of_not_ge hx).le
    have hk : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr
      (by simpa using hx1)
    have hlo : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hhi : x ≤ (⌊x⌋₊ + 1 : ℕ) := by
      exact_mod_cast (Nat.lt_floor_add_one x).le
    have hb := squareRootSummatoryPrimitive_between criticalSourceCoeff hk hlo hhi
    have hi := congrArg Complex.im hb
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul] at hi
    rw [criticalSourceCoeff_cumulative _ hk,
      criticalSourceAbelPrimitive_nat_im_zero] at hi
    simp only [Complex.ofReal_im, mul_zero, add_zero] at hi
    apply Complex.ext
    · simp
    · simpa using hi

/-- The physical real continuous Abel source observed by terminal children. -/
def criticalContinuousAbel (x : ℝ) : ℝ :=
  (squareRootSummatoryPrimitive criticalSourceCoeff x).re

/-- Source-specific Mellin identity expressed without an implicit complex
extension of the real terminal source. -/
theorem hasMellin_criticalContinuousAbel {s : ℂ} (hs : 3 / 2 < s.re) :
    HasMellin (fun x : ℝ => (criticalContinuousAbel x : ℂ)) (-s)
      (criticalStepSourceMellin (s - 1 / 2) / (2 * s)) := by
  have hfun : (fun x : ℝ => (criticalContinuousAbel x : ℂ)) =
      squareRootSummatoryPrimitive criticalSourceCoeff := by
    funext x
    exact (criticalSourceAbelPrimitive_eq_real x).symm
  rw [hfun]
  exact hasMellin_criticalSourceAbelPrimitive hs

/-- Exact source-faithful identification of every clipped terminal child
with the Mellin-transformed critical Abel primitive at `M/p`. -/
theorem criticalChild_eq_abelPrimitive_re (M p : ℕ) (hp : 0 < p)
    (hqp : 1 ≤ M / p) :
    mobiusDivisorCriticalChildSource M p =
      (squareRootSummatoryPrimitive criticalSourceCoeff
        ((M : ℝ) / p)).re := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hlo : ((M / p : ℕ) : ℝ) ≤ (M : ℝ) / p := by
    rw [le_div_iff₀ hpR]
    exact_mod_cast Nat.div_mul_le_self M p
  have hhi : (M : ℝ) / p ≤ (M / p + 1 : ℕ) := by
    rw [div_le_iff₀ hpR]
    exact_mod_cast (by simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ M hp).le : M ≤ (M / p + 1) * p)
  have hbetween := squareRootSummatoryPrimitive_between criticalSourceCoeff
    hqp hlo hhi
  have hre := congrArg Complex.re hbetween
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hre
  rw [criticalSourceCoeff_cumulative _ hqp,
    criticalSourceAbelPrimitive_nat] at hre
  simp only [Complex.ofReal_re] at hre
  have hsqrt : Real.sqrt p * Real.sqrt ((M : ℝ) / p) = Real.sqrt M := by
    rw [Real.sqrt_div (Nat.cast_nonneg (α := ℝ) M)]
    have hpS : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hpR).ne'
    field_simp
  apply mul_left_cancel₀ (Real.sqrt_pos.mpr hpR).ne'
  rw [criticalChild_weighted_quotient_normal_form M p hp hqp, hre]
  rw [← hsqrt]
  ring

/-- Every nonempty terminal prime quotient samples the real Mellin source
itself, with the exact arithmetic clip. -/
theorem criticalChild_eq_criticalContinuousAbel (M p : ℕ) (hp : 0 < p)
    (hqp : 1 ≤ M / p) :
    mobiusDivisorCriticalChildSource M p = criticalContinuousAbel ((M : ℝ) / p) :=
  criticalChild_eq_abelPrimitive_re M p hp hqp

end RHTower
