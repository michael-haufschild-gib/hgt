import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaPairRemainder

/-!
# Symmetric Gamma replacement errors on finite interval families

Diagonal differences vanish. The remaining integrated endpoint errors form a
symmetric nonnegative matrix, so their quadratic form is bounded by four times
the coefficient-square mass weighted by the actual row errors.
-/

noncomputable section
open Finset
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals

/-- Actual integrated endpoint errors, with the zero difference on diagonal blocks retained. -/
def gammaFinitePairDefect {ι : Type*} (a b : ι → ℝ) (i j : ι) : ℝ≥0∞ := by
  classical
  exact if i = j then 0 else gammaIntervalPairDefect (a i) (b i) (a j) (b j)

/-- The error matrix is symmetric for every family of intervals. -/
theorem gammaFinitePairDefect_comm {ι : Type*} (a b : ι → ℝ) (i j : ι) :
    gammaFinitePairDefect a b i j = gammaFinitePairDefect a b j i := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  · simp only [gammaFinitePairDefect, if_neg hij, if_neg (Ne.symm hij)]
    exact gammaIntervalPairDefect_comm _ _ _ _

/-- No integrated-kernel diagonal is charged to a constant source on its own interval. -/
theorem gammaFinitePairDefect_self {ι : Type*} (a b : ι → ℝ) (i : ι) :
    gammaFinitePairDefect a b i i = 0 := by
  classical
  simp [gammaFinitePairDefect]

/-- The actual weighted interaction is bounded by its mean edge and explicit replacement error. -/
theorem gammaFinitePairDefect_weighted_kernel_le {ι : Type*} (a b q : ι → ℝ) (i j : ι) :
    ENNReal.ofReal ((q i - q j) ^ 2) * gammaIntervalKernel (a i) (b i) (a j) (b j) ≤
      ENNReal.ofReal ((b i - a i) * (b j - a j) * (q i - q j) ^ 2 *
        archLevyDensity (max (b j - a i) (b i - a j))) +
        ENNReal.ofReal ((q i - q j) ^ 2) * gammaFinitePairDefect a b i j := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero,
      zero_mul, mul_zero, add_zero, le_refl]
  · simp only [gammaFinitePairDefect, if_neg hij]
    have hbound : gammaIntervalKernel (a i) (b i) (a j) (b j) ≤
        gammaIntervalPairDefect (a i) (b i) (a j) (b j) +
          ENNReal.ofReal ((b i - a i) * (b j - a j) *
            archLevyDensity (max (b j - a i) (b i - a j))) := le_tsub_add
    have hbase : ENNReal.ofReal ((q i - q j) ^ 2) *
        ENNReal.ofReal ((b i - a i) * (b j - a j) *
          archLevyDensity (max (b j - a i) (b i - a j))) =
        ENNReal.ofReal ((b i - a i) * (b j - a j) * (q i - q j) ^ 2 *
          archLevyDensity (max (b j - a i) (b i - a j))) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      ring
    refine (mul_le_mul_right hbound (ENNReal.ofReal ((q i - q j) ^ 2))).trans_eq ?_
    rw [mul_add, hbase, add_comm]

/-- The actual symmetric Gamma error is paid by its row sums and squared coefficients. -/
theorem gammaFinitePairDefect_schur {ι : Type*} [Fintype ι] (a b q : ι → ℝ) :
    (∑ i, ∑ j, ENNReal.ofReal ((q i - q j) ^ 2) * gammaFinitePairDefect a b i j) ≤
      4 * ∑ i, ENNReal.ofReal (q i ^ 2) * (∑ j, gammaFinitePairDefect a b i j) := by
  have hpoint (i j : ι) :
      ENNReal.ofReal ((q i - q j) ^ 2) * gammaFinitePairDefect a b i j ≤
        2 * (ENNReal.ofReal (q i ^ 2) * gammaFinitePairDefect a b i j +
          ENNReal.ofReal (q j ^ 2) * gammaFinitePairDefect a b i j) := by
    have hreal : (q i - q j) ^ 2 ≤ 2 * (q i ^ 2 + q j ^ 2) := by
      nlinarith only [sq_nonneg (q i + q j)]
    have hcoef : ENNReal.ofReal ((q i - q j) ^ 2) ≤
        2 * (ENNReal.ofReal (q i ^ 2) + ENNReal.ofReal (q j ^ 2)) := by
      calc
        _ ≤ ENNReal.ofReal (2 * (q i ^ 2 + q j ^ 2)) := ENNReal.ofReal_le_ofReal hreal
        _ = _ := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
          norm_num only [ENNReal.ofReal_ofNat]
    calc
      _ = gammaFinitePairDefect a b i j * ENNReal.ofReal ((q i - q j) ^ 2) := mul_comm _ _
      _ ≤ gammaFinitePairDefect a b i j *
          (2 * (ENNReal.ofReal (q i ^ 2) + ENNReal.ofReal (q j ^ 2))) :=
        mul_le_mul_right hcoef _
      _ = _ := by ring
  have hrow : (∑ i, ∑ j, ENNReal.ofReal (q i ^ 2) * gammaFinitePairDefect a b i j) =
      ∑ i, ENNReal.ofReal (q i ^ 2) * (∑ j, gammaFinitePairDefect a b i j) := by
    simp only [Finset.mul_sum]
  have hcol : (∑ i, ∑ j, ENNReal.ofReal (q j ^ 2) * gammaFinitePairDefect a b i j) =
      ∑ i, ENNReal.ofReal (q i ^ 2) * (∑ j, gammaFinitePairDefect a b i j) := by
    calc
      _ = ∑ i, ∑ j, ENNReal.ofReal (q i ^ 2) * gammaFinitePairDefect a b j i := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [gammaFinitePairDefect_comm a b j i]
  calc
    _ ≤ ∑ i, ∑ j, 2 * (ENNReal.ofReal (q i ^ 2) * gammaFinitePairDefect a b i j +
        ENNReal.ofReal (q j ^ 2) * gammaFinitePairDefect a b i j) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j
    _ = 2 * ∑ i, ∑ j, (ENNReal.ofReal (q i ^ 2) * gammaFinitePairDefect a b i j +
        ENNReal.ofReal (q j ^ 2) * gammaFinitePairDefect a b i j) := by
      simp only [Finset.mul_sum]
    _ = 2 * ((∑ i, ∑ j, ENNReal.ofReal (q i ^ 2) * gammaFinitePairDefect a b i j) +
        (∑ i, ∑ j, ENNReal.ofReal (q j ^ 2) * gammaFinitePairDefect a b i j)) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by rw [hrow, hcol]; ring

#print axioms gammaFinitePairDefect_comm
#print axioms gammaFinitePairDefect_self
#print axioms gammaFinitePairDefect_weighted_kernel_le
#print axioms gammaFinitePairDefect_schur

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals
