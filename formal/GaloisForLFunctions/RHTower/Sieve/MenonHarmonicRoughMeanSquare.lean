import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamare
import GaloisForLFunctions.RHTower.Sieve.SupportMeanSquare

/-!
# Menon's harmonic rough remainder is negligible

On Menon's dyadic source interval `[ceil X, floor(3X)]`, every harmonic coefficient has size at
most `1/X`.  The Möbius support is squarefree, and an integer left by the final Ramaré prime range
is therefore squarefree and smooth below the lower cutoff.  The coefficient-energy mean-value
theorem and the literal final-range Rankin--Euler density estimate then give

```text
∫_{-X}^{X} |E_X(w)|² dw · (log X)^8  →  0.
```

This is the exact harmonic normalization used in Menon's final-frequency argument.
-/

namespace RHTower.Sieve

open Finset Nat MeasureTheory Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- Rough part of Menon's harmonic polynomial on its dyadic source shell. -/
def menonFinalRangeHarmonicRoughSet (x : ℝ) : Finset ℕ :=
  {n ∈ menonFinalRangeShell x |
    primeFactorsIn (menonFinalRangePrimes x) n = ∅}

/-- Squarefree indices in Menon's harmonic rough set are smooth below the final lower cutoff. -/
theorem filter_menonFinalRangeHarmonicRoughSet_squarefree_subset (x : ℝ) :
    (menonFinalRangeHarmonicRoughSet x).filter Squarefree ⊆
      squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
        (menonFinalRangeTopNat x) := by
  intro n hn
  rw [Finset.mem_filter] at hn
  have hnrough := hn.1
  have hnsq := hn.2
  rw [menonFinalRangeHarmonicRoughSet, Finset.mem_filter] at hnrough
  have hnshell := hnrough.1
  have hnempty := hnrough.2
  rw [menonFinalRangeShell, Finset.mem_Icc] at hnshell
  apply filter_supportMeanSquareRoughSet_primesRange_squarefree_subset
  rw [Finset.mem_filter]
  refine ⟨?_, hnsq⟩
  rw [supportMeanSquareRoughSet, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, hnshell.2⟩, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 fun hn0 => not_squarefree_zero (hn0 ▸ hnsq)
  · simpa [menonFinalRangePrimes] using hnempty

/-- Harmonic coefficient energy on Menon's rough set is its smooth squarefree count divided by
`X²`. -/
theorem sum_normSq_harmonicMoebiusC_menonFinalRangeHarmonicRoughSet_le
    (x : ℝ) (hx : 1 ≤ x) :
    ∑ n ∈ menonFinalRangeHarmonicRoughSet x, ‖harmonicMoebiusC n‖ ^ 2 ≤
      ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
        (menonFinalRangeTopNat x)).card : ℝ) / x ^ 2 := by
  classical
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  calc
    ∑ n ∈ menonFinalRangeHarmonicRoughSet x, ‖harmonicMoebiusC n‖ ^ 2 =
        ∑ n ∈ menonFinalRangeHarmonicRoughSet x,
          if Squarefree n then ‖harmonicMoebiusC n‖ ^ 2 else 0 := by
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hnsq : Squarefree n
      · simp [hnsq]
      · rw [if_neg hnsq, harmonicMoebiusC,
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
        simp
    _ = ∑ n ∈ (menonFinalRangeHarmonicRoughSet x).filter Squarefree,
          ‖harmonicMoebiusC n‖ ^ 2 := by
      rw [Finset.sum_filter]
    _ ≤ ∑ _n ∈ (menonFinalRangeHarmonicRoughSet x).filter Squarefree,
          1 / x ^ 2 := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hnmem := (Finset.mem_filter.1 hn).1
      have hnsq := (Finset.mem_filter.1 hn).2
      have hnshell := (Finset.mem_filter.1
        (show n ∈ menonFinalRangeHarmonicRoughSet x from hnmem)).1
      rw [menonFinalRangeShell, Finset.mem_Icc] at hnshell
      have hnx : x ≤ (n : ℝ) := (Nat.le_ceil x).trans (by exact_mod_cast hnshell.1)
      have hcoef : ‖harmonicMoebiusC n‖ ^ 2 = 1 / (n : ℝ) ^ 2 := by
        rw [harmonicMoebiusC, norm_div, Complex.norm_natCast, div_pow]
        have hne : μ n ≠ 0 :=
          ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hnsq
        rcases ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp hne with hmu | hmu <;>
          rw [hmu] <;> norm_num
      rw [hcoef]
      exact one_div_le_one_div_of_le (sq_pos_of_pos hx0) (by nlinarith)
    _ = (((menonFinalRangeHarmonicRoughSet x).filter Squarefree).card : ℝ) /
          x ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
          (menonFinalRangeTopNat x)).card : ℝ) / x ^ 2 := by
      exact div_le_div_of_nonneg_right (by
        exact_mod_cast Finset.card_le_card
          (filter_menonFinalRangeHarmonicRoughSet_squarefree_subset x)) (sq_nonneg x)

/-- Mean-square cost of Menon's harmonic rough remainder. -/
theorem integral_Icc_normSq_menonFinalRangeHarmonicRough_le
    (x : ℝ) (hx : 1 ≤ x) :
    (∫ w in Set.Icc (-x) x,
      ‖logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2) ≤
      (5 * Real.pi / 2 * x +
        5 * Real.exp 1 / 2 * (menonFinalRangeTopNat x : ℝ)) *
          (((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
            (menonFinalRangeTopNat x)).card : ℝ) / x ^ 2) := by
  refine (integral_Icc_normSq_logPoly_le_energy harmonicMoebiusC
    (M := menonFinalRangeTopNat x) ?_ ?_ hx).trans ?_
  · intro hzero
    rw [menonFinalRangeHarmonicRoughSet, Finset.mem_filter] at hzero
    have hshell := hzero.1
    rw [menonFinalRangeShell, Finset.mem_Icc] at hshell
    have hxceil : 1 ≤ ⌈x⌉₊ := by
      exact_mod_cast hx.trans (Nat.le_ceil x)
    omega
  · intro n hn
    rw [menonFinalRangeHarmonicRoughSet, Finset.mem_filter] at hn
    rw [menonFinalRangeShell, Finset.mem_Icc] at hn
    exact hn.1.2
  · exact mul_le_mul_of_nonneg_left
      (sum_normSq_harmonicMoebiusC_menonFinalRangeHarmonicRoughSet_le x hx)
      (by positivity)

/-- Harmonic rough energy on Menon's final frequency interval. -/
def menonFinalRangeHarmonicRoughEnergy (x : ℝ) : ℝ :=
  ∫ w in Set.Icc (-x) x,
    ‖logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2

/-- The rough term in Menon's harmonic Ramaré factorization is negligible with eight logarithms
to spare. -/
theorem tendsto_menonFinalRangeHarmonicRoughEnergy_mul_logPow_zero :
    Tendsto (fun x : ℝ => menonFinalRangeHarmonicRoughEnergy x * (Real.log x) ^ 8)
      atTop (nhds 0) := by
  let C : ℝ := 5 * Real.pi / 2 + 15 * Real.exp 1 / 2
  have hmajor :=
    tendsto_card_squarefreeSmoothUpTo_menonFinalRange_mul_logPow_div_zero.const_mul C
  simp only [mul_zero] at hmajor
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx
    have hx1 : 1 < x := lt_trans (by
      simpa only [Real.exp_zero] using
        Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)) hx
    have hlog : 0 ≤ Real.log x := (Real.log_pos hx1).le
    have hint : 0 ≤ menonFinalRangeHarmonicRoughEnergy x := by
      rw [menonFinalRangeHarmonicRoughEnergy]
      exact integral_nonneg fun _ => by positivity
    positivity
  · filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx
    have he1 : (1 : ℝ) < Real.exp 1 := by
      simpa only [Real.exp_zero] using
        Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
    have hx1 : 1 < x := he1.trans hx
    have hx0 : 0 < x := zero_lt_one.trans hx1
    have hlog1 : 1 < Real.log x :=
      (Real.lt_log_iff_exp_lt (by positivity)).2 hx
    have hlog0 : 0 ≤ Real.log x := le_trans (by norm_num) hlog1.le
    have htop : (menonFinalRangeTopNat x : ℝ) ≤ 3 * x := by
      rw [menonFinalRangeTopNat]
      exact Nat.floor_le (by positivity)
    have henergy := integral_Icc_normSq_menonFinalRangeHarmonicRough_le x hx1.le
    rw [← menonFinalRangeHarmonicRoughEnergy] at henergy
    have hcoef : 5 * Real.pi / 2 * x +
        5 * Real.exp 1 / 2 * (menonFinalRangeTopNat x : ℝ) ≤ C * x := by
      dsimp [C]
      have hexp0 : 0 ≤ 5 * Real.exp 1 / 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left htop hexp0]
    have hcard0 : 0 ≤ ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
        (menonFinalRangeTopNat x)).card : ℝ) := by positivity
    have hquot0 : 0 ≤ ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
        (menonFinalRangeTopNat x)).card : ℝ) / x ^ 2 := by positivity
    have hbound := henergy.trans (mul_le_mul_of_nonneg_right hcoef hquot0)
    have hscaled := mul_le_mul_of_nonneg_right hbound (pow_nonneg hlog0 8)
    have hlogpow : (Real.log x) ^ 8 ≤ (Real.log x) ^ 10 := by
      nlinarith [sq_nonneg ((Real.log x) ^ 4 * (Real.log x - 1))]
    have hcardLog :
        ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
          (menonFinalRangeTopNat x)).card : ℝ) * (Real.log x) ^ 8 / x ≤
        ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
          (menonFinalRangeTopNat x)).card : ℝ) * (Real.log x) ^ 10 / x := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogpow hcard0) hx0.le
    calc
      menonFinalRangeHarmonicRoughEnergy x * (Real.log x) ^ 8 ≤
          (C * x *
            (((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
              (menonFinalRangeTopNat x)).card : ℝ) / x ^ 2)) *
                (Real.log x) ^ 8 := hscaled
      _ = C * (((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
            (menonFinalRangeTopNat x)).card : ℝ) * (Real.log x) ^ 8 / x) := by
        field_simp [ne_of_gt hx0]
      _ ≤ C * (((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
            (menonFinalRangeTopNat x)).card : ℝ) * (Real.log x) ^ 10 / x) := by
        exact mul_le_mul_of_nonneg_left hcardLog (by dsimp [C]; positivity)

end

end RHTower.Sieve
