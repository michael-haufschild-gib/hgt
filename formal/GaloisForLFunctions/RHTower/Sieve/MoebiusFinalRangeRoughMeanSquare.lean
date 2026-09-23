import GaloisForLFunctions.RHTower.Sieve.MenonFinalRangeSmoothDensity
import GaloisForLFunctions.RHTower.Sieve.SupportMeanSquare
import GaloisForLFunctions.RHTower.Sieve.MoebiusWindowVariance
import GaloisForLFunctions.RHTower.Sieve.TuranKubiliusRange
import GaloisForLFunctions.RHTower.Sieve.RamareRoughBridge

namespace RHTower.Sieve

open Finset Nat
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- A squarefree integer up to `M` with no prime factor in `(z,M]` is `z`-smooth. -/
theorem filter_supportMeanSquareRoughSet_primesRange_squarefree_subset (z M : ℕ) :
    (supportMeanSquareRoughSet (primesRange z M) M).filter Squarefree ⊆
      squarefreeSmoothUpTo z M := by
  intro n hn
  rw [Finset.mem_filter] at hn
  have hnrough := hn.1
  have hnsq := hn.2
  rw [supportMeanSquareRoughSet, Finset.mem_filter, Finset.mem_Icc] at hnrough
  rw [mem_squarefreeSmoothUpTo]
  refine ⟨⟨hnrough.1, ?_⟩, hnsq⟩
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  rw [mem_primesLE]
  refine ⟨?_, hp.1⟩
  by_contra hpz
  have hpM : p ≤ M :=
    le_trans (Nat.le_of_dvd (by omega) hp.2.1) hnrough.1.2
  have hprange : p ∈ primesRange z M := by
    rw [primesRange, Finset.mem_sdiff]
    refine ⟨mem_primesLE.2 ⟨hpM, hp.1⟩, ?_⟩
    intro hpSmall
    exact hpz (mem_primesLE.1 hpSmall).1
  have hnodiv := (primeFactorsIn_eq_empty_iff.mp hnrough.2) p hprange
  exact hnodiv hp.2.1

/-- Möbius energy on the final rough set is bounded by the squarefree smooth count. -/
theorem sum_normSq_moebiusC_supportMeanSquareRoughSet_primesRange_le_card (z M : ℕ) :
    ∑ n ∈ supportMeanSquareRoughSet (primesRange z M) M, ‖moebiusC n‖ ^ (2 : ℕ)
      ≤ ((squarefreeSmoothUpTo z M).card : ℝ) := by
  classical
  rw [Finset.sum_congr rfl fun n _ => normSq_moebiusC_eq_indicator n,
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast Finset.card_le_card
    (filter_supportMeanSquareRoughSet_primesRange_squarefree_subset z M)

/-- Mean-square cost of the Möbius remainder with no prime factor in `(z,M]`. -/
theorem integral_Icc_normSq_moebius_rough_primesRange_le_squarefreeSmooth
    (z M : ℕ) {W : ℝ} (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W,
      ‖logPoly moebiusC (supportMeanSquareRoughSet (primesRange z M) M) w‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ)) *
        ((squarefreeSmoothUpTo z M).card : ℝ) := by
  classical
  refine (integral_Icc_normSq_logPoly_le_energy moebiusC (M := M) ?_ ?_ hW).trans ?_
  · rw [supportMeanSquareRoughSet]
    intro hcon
    have := (Finset.mem_filter.1 hcon).1
    rw [Finset.mem_Icc] at this
    omega
  · intro n hn
    rw [supportMeanSquareRoughSet, Finset.mem_filter, Finset.mem_Icc] at hn
    exact hn.1.2
  · exact mul_le_mul_of_nonneg_left
      (sum_normSq_moebiusC_supportMeanSquareRoughSet_primesRange_le_card z M)
      (by positivity)

/-- The literal Menon final-range rough Möbius polynomial is negligible in mean square,
even after eight powers of logarithmic amplification. -/
theorem tendsto_menonFinalRange_roughMeanSquare_mul_logPow_div_zero :
    Filter.Tendsto (fun x : ℝ =>
      (∫ w in Set.Icc (-x) x,
        ‖logPoly moebiusC
          (supportMeanSquareRoughSet
            (primesRange (menonFinalRangePrimeCutoffNat x) (menonFinalRangeTopNat x))
            (menonFinalRangeTopNat x)) w‖ ^ (2 : ℕ)) *
          (Real.log x) ^ (8 : ℕ) / x ^ (2 : ℕ)) Filter.atTop (nhds 0) := by
  let C : ℝ := 5 * Real.pi / 2 + 15 * Real.exp 1 / 2
  have hmajor :=
    tendsto_card_squarefreeSmoothUpTo_menonFinalRange_mul_logPow_div_zero.const_mul C
  simp only [mul_zero] at hmajor
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with x hx
    have hx1 : 1 < x := lt_trans (by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)) hx
    have hlog : 0 ≤ Real.log x := (Real.log_pos hx1).le
    have hint : 0 ≤ ∫ w in Set.Icc (-x) x,
        ‖logPoly moebiusC
          (supportMeanSquareRoughSet
            (primesRange (menonFinalRangePrimeCutoffNat x) (menonFinalRangeTopNat x))
            (menonFinalRangeTopNat x)) w‖ ^ (2 : ℕ) :=
      MeasureTheory.integral_nonneg fun _ => by positivity
    positivity
  · filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with x hx
    have he1 : (1 : ℝ) < Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
    have hx1 : 1 < x := lt_trans he1 hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx1
    have hlog1 : 1 < Real.log x := (Real.lt_log_iff_exp_lt (by positivity)).2 hx
    have hlog0 : 0 ≤ Real.log x := le_trans (by norm_num) hlog1.le
    have htop : ((menonFinalRangeTopNat x : ℕ) : ℝ) ≤ 3 * x := by
      rw [menonFinalRangeTopNat]
      exact Nat.floor_le (by positivity)
    have henergy := integral_Icc_normSq_moebius_rough_primesRange_le_squarefreeSmooth
      (menonFinalRangePrimeCutoffNat x) (menonFinalRangeTopNat x) (W := x) hx1.le
    have hcoef : 5 * Real.pi / 2 * x +
        5 * Real.exp 1 / 2 * ((menonFinalRangeTopNat x : ℕ) : ℝ) ≤ C * x := by
      dsimp [C]
      have hexp0 : 0 ≤ 5 * Real.exp 1 / 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left htop hexp0]
    have hcard0 : 0 ≤ ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
        (menonFinalRangeTopNat x)).card : ℝ) := by positivity
    have hbound := henergy.trans (mul_le_mul_of_nonneg_right hcoef hcard0)
    have hfac0 : 0 ≤ (Real.log x) ^ (8 : ℕ) / x ^ (2 : ℕ) := by positivity
    have hscaled := mul_le_mul_of_nonneg_right hbound hfac0
    have hlogpow : (Real.log x) ^ (8 : ℕ) ≤ (Real.log x) ^ (10 : ℕ) := by
      nlinarith [sq_nonneg ((Real.log x) ^ (4 : ℕ) * (Real.log x - 1))]
    have hcardLog : ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
          (menonFinalRangeTopNat x)).card : ℝ) * (Real.log x) ^ (8 : ℕ) / x
        ≤ ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
          (menonFinalRangeTopNat x)).card : ℝ) * (Real.log x) ^ (10 : ℕ) / x := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogpow hcard0) hx0.le
    calc
      (∫ w in Set.Icc (-x) x,
          ‖logPoly moebiusC
            (supportMeanSquareRoughSet
              (primesRange (menonFinalRangePrimeCutoffNat x) (menonFinalRangeTopNat x))
              (menonFinalRangeTopNat x)) w‖ ^ (2 : ℕ)) * (Real.log x) ^ (8 : ℕ) / x ^ (2 : ℕ)
          = (∫ w in Set.Icc (-x) x,
              ‖logPoly moebiusC
                (supportMeanSquareRoughSet
                  (primesRange (menonFinalRangePrimeCutoffNat x) (menonFinalRangeTopNat x))
                  (menonFinalRangeTopNat x)) w‖ ^ (2 : ℕ)) *
              ((Real.log x) ^ (8 : ℕ) / x ^ (2 : ℕ)) := by ring
      _ ≤ (C * x * ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
              (menonFinalRangeTopNat x)).card : ℝ)) * ((Real.log x) ^ (8 : ℕ) / x ^ (2 : ℕ)) := hscaled
      _ = C * (((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
              (menonFinalRangeTopNat x)).card : ℝ) * (Real.log x) ^ (8 : ℕ) / x) := by
            field_simp
      _ ≤ C * (((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
              (menonFinalRangeTopNat x)).card : ℝ) * (Real.log x) ^ (10 : ℕ) / x) := by
            exact mul_le_mul_of_nonneg_left hcardLog (by dsimp [C]; positivity)

end

end RHTower.Sieve
