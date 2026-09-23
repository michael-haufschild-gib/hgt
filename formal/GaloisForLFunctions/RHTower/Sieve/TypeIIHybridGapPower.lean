import GaloisForLFunctions.RHTower.Sieve.TypeIIHybridGapSum
import GaloisForLFunctions.RHTower.Sieve.GapSumDyadic

/-!
# Hybrid gap sum at dyadic parameters

Substituting the effective interval and `Q ≤ 2P` gives the three terms needed for the exact
`(1/2,1/2)` type-II power estimate: growing curvature, reciprocal curvature, and diagonal length.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

theorem hybridGapSumBound_le_power {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B P Q : ℕ} (hA : 1 ≤ A) (hP : 1 ≤ P) (hQ : 2 ≤ Q) (hQ2P : Q ≤ 2 * P) :
    hybridGapSumBound T r (effLow A Q) (effHigh B P) P Q (effGap A B P Q)
      ≤ 1000 * Real.sqrt (T * r) * (B : ℝ) * Real.sqrt B / ((A : ℝ) * P)
        + 20 * Real.pi * (B : ℝ) ^ (2 : ℕ) / (T * r) * invSum B
        + (B : ℝ) / P := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hTr : (0 : ℝ) < T * r := by positivity
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hlow := cast_effLow_ge hA hQ
  have hhigh := cast_effHigh_le (B := B) hP
  have hgap := cast_effGap_le (A := A) (B := B) (P := P) (Q := Q) hP
  have hQ2 : (Q : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hQ2P
  have hlow0 : (0 : ℝ) < ((effLow A Q : ℕ) : ℝ) :=
    lt_of_lt_of_le (by positivity) hlow
  have hfirst : 5000 * Real.sqrt
      (T * r / (((effLow A Q : ℕ) : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P)))
      * (((effGap A B P Q : ℕ) : ℝ) * Real.sqrt (effGap A B P Q))
      ≤ 1000 * Real.sqrt (T * r) * (B : ℝ) * Real.sqrt B / ((A : ℝ) * P) := by
    have hrad : T * r * ((effGap A B P Q : ℕ) : ℝ) ^ (3 : ℕ)
        / (((effLow A Q : ℕ) : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P))
        ≤ (T * r * (B : ℝ) ^ (3 : ℕ) / (((A : ℝ) * P) ^ (2 : ℕ))) / 25 := by
      have hnum : T * r * ((effGap A B P Q : ℕ) : ℝ) ^ (3 : ℕ)
          ≤ T * r * ((B : ℝ) / P) ^ (3 : ℕ) := by
        have := pow_le_pow_left₀ (Nat.cast_nonneg _) hgap 3
        nlinarith [this, hTr]
      have hden : ((A : ℝ) / (2 * P)) ^ (2 : ℕ) * (36 * Real.pi * P)
          ≤ ((effLow A Q : ℕ) : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P) := by
        have hle : (A : ℝ) / (2 * P) ≤ ((effLow A Q : ℕ) : ℝ) := by
          refine le_trans ?_ hlow
          exact div_le_div_of_nonneg_left hA0.le hQ0 hQ2
        have hsq : ((A : ℝ) / (2 * P)) ^ (2 : ℕ) ≤ ((effLow A Q : ℕ) : ℝ) ^ (2 : ℕ) :=
          pow_le_pow_left₀ (by positivity) hle 2
        exact mul_le_mul_of_nonneg_right hsq (by positivity)
      have hstep : T * r * ((effGap A B P Q : ℕ) : ℝ) ^ (3 : ℕ)
          / (((effLow A Q : ℕ) : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P))
          ≤ T * r * ((B : ℝ) / P) ^ (3 : ℕ) /
            (((A : ℝ) / (2 * P)) ^ (2 : ℕ) * (36 * Real.pi * P)) := by
        refine div_le_div₀ (by positivity) hnum (by positivity) hden
      refine le_trans hstep ?_
      have heq : T * r * ((B : ℝ) / P) ^ (3 : ℕ) /
          (((A : ℝ) / (2 * P)) ^ (2 : ℕ) * (36 * Real.pi * P))
          = (4 / (36 * Real.pi)) * (T * r * (B : ℝ) ^ (3 : ℕ) / (((A : ℝ) * P) ^ (2 : ℕ))) := by
        field_simp
        ring
      rw [heq]
      have hcoef : (4 : ℝ) / (36 * Real.pi) ≤ 1 / 25 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hpi3]
      have hpos : (0 : ℝ) ≤ T * r * (B : ℝ) ^ (3 : ℕ) / (((A : ℝ) * P) ^ (2 : ℕ)) := by positivity
      nlinarith [hcoef, hpos]
    have hmerge : Real.sqrt
        (T * r / (((effLow A Q : ℕ) : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P)))
        * (((effGap A B P Q : ℕ) : ℝ) * Real.sqrt (effGap A B P Q))
        = Real.sqrt (T * r * ((effGap A B P Q : ℕ) : ℝ) ^ (3 : ℕ) /
          (((effLow A Q : ℕ) : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P))) := by
      rw [← sqrt_cube (effGap A B P Q : ℝ) (Nat.cast_nonneg _),
        ← Real.sqrt_mul (by positivity)]
      congr 1
      ring
    have hsq := Real.sqrt_le_sqrt hrad
    have hval : Real.sqrt ((T * r * (B : ℝ) ^ (3 : ℕ) / (((A : ℝ) * P) ^ (2 : ℕ))) / 25)
        = Real.sqrt (T * r) * (B : ℝ) * Real.sqrt B / ((A : ℝ) * P) / 5 := by
      rw [Real.sqrt_div (by positivity) (25 : ℝ),
        show (25 : ℝ) = (5 : ℝ) ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num),
        sqrt_cube_div (T * r) (B : ℝ) ((A : ℝ) * P) hTr.le hB0 (by positivity)]
    calc
      5000 * Real.sqrt
          (T * r / (((effLow A Q : ℕ) : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P)))
          * (((effGap A B P Q : ℕ) : ℝ) * Real.sqrt (effGap A B P Q))
          = 5000 * Real.sqrt (T * r * ((effGap A B P Q : ℕ) : ℝ) ^ (3 : ℕ) /
            (((effLow A Q : ℕ) : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P))) := by
              rw [show 5000 * Real.sqrt
                (T * r / (((effLow A Q : ℕ) : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P)))
                * (((effGap A B P Q : ℕ) : ℝ) * Real.sqrt (effGap A B P Q))
                = 5000 * (Real.sqrt
                  (T * r / (((effLow A Q : ℕ) : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P)))
                  * (((effGap A B P Q : ℕ) : ℝ) * Real.sqrt (effGap A B P Q))) by ring,
                hmerge]
      _ ≤ 5000 * (Real.sqrt (T * r) * (B : ℝ) * Real.sqrt B /
            ((A : ℝ) * P) / 5) := mul_le_mul_of_nonneg_left (hval ▸ hsq) (by norm_num)
      _ = 1000 * Real.sqrt (T * r) * (B : ℝ) * Real.sqrt B / ((A : ℝ) * P) := by ring
  have hrec : (75 * Real.pi * (Q : ℝ) ^ (2 : ℕ) * ((effHigh B P : ℕ) : ℝ) ^ (2 : ℕ) /
      (16 * T * r)) * invSum (effGap A B P Q)
      ≤ 20 * Real.pi * (B : ℝ) ^ (2 : ℕ) / (T * r) * invSum B := by
    have hQsq : (Q : ℝ) ^ (2 : ℕ) ≤ (2 * (P : ℝ)) ^ (2 : ℕ) := by gcongr
    have hMsq : ((effHigh B P : ℕ) : ℝ) ^ (2 : ℕ) ≤ ((B : ℝ) / P) ^ (2 : ℕ) := by gcongr
    have hprod : (Q : ℝ) ^ (2 : ℕ) * ((effHigh B P : ℕ) : ℝ) ^ (2 : ℕ) ≤ 4 * (B : ℝ) ^ (2 : ℕ) := by
      calc
        (Q : ℝ) ^ (2 : ℕ) * ((effHigh B P : ℕ) : ℝ) ^ (2 : ℕ)
            ≤ (2 * (P : ℝ)) ^ (2 : ℕ) * ((B : ℝ) / P) ^ (2 : ℕ) :=
              mul_le_mul hQsq hMsq (by positivity) (by positivity)
        _ = 4 * (B : ℝ) ^ (2 : ℕ) := by field_simp; ring
    have hcoef : 75 * Real.pi * (Q : ℝ) ^ (2 : ℕ) * ((effHigh B P : ℕ) : ℝ) ^ (2 : ℕ) /
        (16 * T * r) ≤ 20 * Real.pi * (B : ℝ) ^ (2 : ℕ) / (T * r) := by
      have hnum : 75 * Real.pi * ((Q : ℝ) ^ (2 : ℕ) * ((effHigh B P : ℕ) : ℝ) ^ (2 : ℕ)) / 16
          ≤ 20 * Real.pi * (B : ℝ) ^ (2 : ℕ) := by
        nlinarith [mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ 75 * Real.pi by positivity)]
      calc
        75 * Real.pi * (Q : ℝ) ^ (2 : ℕ) * ((effHigh B P : ℕ) : ℝ) ^ (2 : ℕ) / (16 * T * r)
            = (75 * Real.pi * ((Q : ℝ) ^ (2 : ℕ) * ((effHigh B P : ℕ) : ℝ) ^ (2 : ℕ)) / 16) /
                (T * r) := by ring
        _ ≤ (20 * Real.pi * (B : ℝ) ^ (2 : ℕ)) / (T * r) :=
          div_le_div_of_nonneg_right hnum hTr.le
    have hgapNat : effGap A B P Q ≤ B := by
      rw [effGap, effHigh]
      exact le_trans (Nat.sub_le _ _)
        (le_trans (Nat.div_le_self (B - 1) P) (by omega))
    exact mul_le_mul hcoef (invSum_mono hgapNat) (invSum_nonneg _) (by positivity)
  have hlast : ((effGap A B P Q : ℕ) : ℝ) ≤ (B : ℝ) / P := hgap
  rw [hybridGapSumBound]
  nlinarith [hfirst, hrec, hlast]

end

end RHTower.Sieve
