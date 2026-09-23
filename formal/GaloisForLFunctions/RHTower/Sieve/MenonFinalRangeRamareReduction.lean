import GaloisForLFunctions.RHTower.Sieve.MoebiusFinalRangeRoughMeanSquare
import GaloisForLFunctions.RHTower.Sieve.RamareRoughSetSplit

namespace RHTower.Sieve

open Finset MeasureTheory Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- Menon's literal final prime range `(P(X), floor(3X)]`. -/
def menonFinalRangePrimes (x : ℝ) : Finset ℕ :=
  primesRange (menonFinalRangePrimeCutoffNat x) (menonFinalRangeTopNat x)

theorem menonFinalRangePrimes_prime (x : ℝ) {p : ℕ}
    (hp : p ∈ menonFinalRangePrimes x) : p.Prime := by
  exact primesRange_prime hp

/-- Full Möbius polynomial energy on Menon's final frequency interval. -/
def menonFinalRangeFullEnergy (x : ℝ) : ℝ :=
  ∫ w in Set.Icc (-x) x,
    ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 (menonFinalRangeTopNat x)) w‖ ^ (2 : ℕ)

/-- Ramaré bilinear energy for Menon's literal final prime range. -/
def menonFinalRangeBilinearEnergy (x : ℝ) : ℝ :=
  ∫ w in Set.Icc (-x) x,
    ‖ramareBilinear (menonFinalRangePrimes x) (menonFinalRangeTopNat x) w‖ ^ (2 : ℕ)

/-- Rough Möbius energy left by Menon's literal final prime range. -/
def menonFinalRangeRoughEnergy (x : ℝ) : ℝ :=
  ∫ w in Set.Icc (-x) x,
    ‖logPoly moebiusC
      (supportMeanSquareRoughSet (menonFinalRangePrimes x) (menonFinalRangeTopNat x)) w‖ ^ (2 : ℕ)

private theorem logPoly_moebiusC_eq_cast (s : Finset ℕ) (w : ℝ) :
    logPoly moebiusC s w = logPoly (fun n => ((μ n : ℤ) : ℂ)) s w := by
  rw [logPoly]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [moebiusC]
  congr 1

/-- Exact pointwise Ramaré decomposition at Menon's literal final range. -/
theorem logPoly_moebius_eq_menonFinalRange_ramare_add_rough (x w : ℝ) :
    logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 (menonFinalRangeTopNat x)) w
      = ramareBilinear (menonFinalRangePrimes x) (menonFinalRangeTopNat x) w
        + logPoly (fun n => ((μ n : ℤ) : ℂ))
            (supportMeanSquareRoughSet (menonFinalRangePrimes x)
              (menonFinalRangeTopNat x)) w := by
  exact logPoly_moebius_eq_ramare_add_rough
    (fun p hp => menonFinalRangePrimes_prime x hp) (menonFinalRangeTopNat x) w

/-- The full final-range energy is the bilinear energy plus the exact rough cost. -/
theorem menonFinalRangeFullEnergy_le_two_mul_bilinear_add_rough (x : ℝ) :
    menonFinalRangeFullEnergy x ≤
      2 * menonFinalRangeBilinearEnergy x + 2 * menonFinalRangeRoughEnergy x := by
  have h := setIntegral_normSq_logPoly_moebius_le_ramare_rough
    (P := menonFinalRangePrimes x) (fun p hp => menonFinalRangePrimes_prime x hp)
    (menonFinalRangeTopNat x) (W := x) (δ := (1 : ℝ)) (E := Set.Icc (-x) x)
    (by norm_num) measurableSet_Icc (fun _ hmem => hmem)
  norm_num at h
  rw [menonFinalRangeFullEnergy, menonFinalRangeBilinearEnergy,
    menonFinalRangeRoughEnergy]
  refine h.trans_eq ?_
  congr 2

/-- After logarithmic normalization, every excess beyond twice the final-range bilinear energy
vanishes.  Thus the only surviving final-range task is the bilinear term itself. -/
theorem tendsto_menonFinalRange_fullEnergy_sub_two_bilinear_posPart_zero :
    Tendsto (fun x : ℝ =>
      max (menonFinalRangeFullEnergy x - 2 * menonFinalRangeBilinearEnergy x) 0 *
        (Real.log x) ^ (8 : ℕ) / x ^ (2 : ℕ)) atTop (nhds 0) := by
  have hrough : Tendsto (fun x : ℝ =>
      menonFinalRangeRoughEnergy x * (Real.log x) ^ (8 : ℕ) / x ^ (2 : ℕ)) atTop (nhds 0) := by
    simpa [menonFinalRangeRoughEnergy, menonFinalRangePrimes] using
      tendsto_menonFinalRange_roughMeanSquare_mul_logPow_div_zero
  have hmajor := hrough.const_mul (2 : ℝ)
  simp only [mul_zero] at hmajor
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx
    have hx0 : 0 < x := lt_trans (Real.exp_pos 1) hx
    have hlog0 : 0 ≤ Real.log x := (Real.log_pos (lt_trans (by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)) hx)).le
    positivity
  · filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx
    have hx0 : 0 < x := lt_trans (Real.exp_pos 1) hx
    have hlog0 : 0 ≤ Real.log x := (Real.log_pos (lt_trans (by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)) hx)).le
    have hrough0 : 0 ≤ menonFinalRangeRoughEnergy x := by
      rw [menonFinalRangeRoughEnergy]
      exact integral_nonneg fun _ => by positivity
    have hsplit := menonFinalRangeFullEnergy_le_two_mul_bilinear_add_rough x
    have hpos : max (menonFinalRangeFullEnergy x -
        2 * menonFinalRangeBilinearEnergy x) 0 ≤ 2 * menonFinalRangeRoughEnergy x := by
      rw [max_le_iff]
      constructor
      · linarith
      · positivity
    have hfac0 : 0 ≤ (Real.log x) ^ (8 : ℕ) / x ^ (2 : ℕ) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hpos hfac0
    calc
      max (menonFinalRangeFullEnergy x - 2 * menonFinalRangeBilinearEnergy x) 0 *
          (Real.log x) ^ (8 : ℕ) / x ^ (2 : ℕ)
          = max (menonFinalRangeFullEnergy x - 2 * menonFinalRangeBilinearEnergy x) 0 *
              ((Real.log x) ^ (8 : ℕ) / x ^ (2 : ℕ)) := by ring
      _ ≤ (2 * menonFinalRangeRoughEnergy x) * ((Real.log x) ^ (8 : ℕ) / x ^ (2 : ℕ)) := hmul
      _ = 2 * (menonFinalRangeRoughEnergy x * (Real.log x) ^ (8 : ℕ) / x ^ (2 : ℕ)) := by ring

end

end RHTower.Sieve
