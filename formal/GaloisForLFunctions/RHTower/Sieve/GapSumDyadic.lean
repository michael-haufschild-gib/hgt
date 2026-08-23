import GaloisForLFunctions.RHTower.Sieve.GapSumSingleSqrt

/-!
# The gap sum at the dyadic parameters

Substituting `M₀ ≍ A/Q`, `M₁ ≍ B/P`, `H ≍ B/P` and `Q ≤ 2P` into the collapsed gap sum leaves two
terms, one growing and one decaying in the curvature scale.  In the exchanged orientation the same
substitution runs with the roles of the two variables reversed.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

theorem sqrt_cube (b : ℝ) (hb : 0 ≤ b) : Real.sqrt (b ^ 3) = b * Real.sqrt b := by
  rw [show b ^ 3 = b ^ 2 * b by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hb]

theorem sqrt_cube_div (X b c : ℝ) (hX : 0 ≤ X) (hb : 0 ≤ b) (hc : 0 < c) :
    Real.sqrt (X * b ^ 3 / c ^ 2) = Real.sqrt X * b * Real.sqrt b / c := by
  rw [Real.sqrt_div (by positivity) (c ^ 2), Real.sqrt_sq hc.le, Real.sqrt_mul hX,
    sqrt_cube b hb]
  ring

/-- The lower end of the effective range dominates the dilated block endpoint. -/
theorem cast_effLow_ge {A Q : ℕ} (hA : 1 ≤ A) (hQ : 2 ≤ Q) :
    (A : ℝ) / Q ≤ ((effLow A Q : ℕ) : ℝ) := by
  have hQ1 : 1 ≤ Q - 1 := by omega
  have hbase := le_cast_fibre_low hA hQ1
  have hcast : (((Q - 1 : ℕ)) : ℝ) = (Q : ℝ) - 1 := by
    have : (1 : ℕ) ≤ Q := by omega
    push_cast [Nat.cast_sub this]; ring
  rw [hcast] at hbase
  have hQ0 : (0 : ℝ) < (Q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith
  have hstep : (A : ℝ) / Q ≤ (A : ℝ) / ((Q : ℝ) - 1) := by
    refine div_le_div_of_nonneg_left (by positivity) hQ0 (by linarith)
  rw [effLow]
  linarith [hstep, hbase]

/-- The upper end of the effective range is dominated by the dilated block endpoint. -/
theorem cast_effHigh_le {B P : ℕ} (hP : 1 ≤ P) :
    ((effHigh B P : ℕ) : ℝ) ≤ (B : ℝ) / P := by
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  rw [effHigh, le_div_iff₀ hP0]
  have hnat : (B - 1) / P * P ≤ B := le_trans (Nat.div_mul_le_self (B - 1) P) (by omega)
  exact_mod_cast hnat

theorem cast_effGap_le {A B P Q : ℕ} (hP : 1 ≤ P) :
    ((effGap A B P Q : ℕ) : ℝ) ≤ (B : ℝ) / P := by
  refine le_trans ?_ (cast_effHigh_le hP)
  have : effGap A B P Q ≤ effHigh B P := by rw [effGap]; omega
  exact_mod_cast this

set_option maxHeartbeats 1600000 in
/-- **The gap sum on a dyadic block, long orientation.** -/
theorem gapSumBound_le_unswap {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {A B P Q : ℕ}
    (hA : 1 ≤ A) (hP : 1 ≤ P) (hQ : 2 ≤ Q) (hQ2P : Q ≤ 2 * P) :
    gapSumBound T r (effLow A Q) (effHigh B P) P Q (effGap A B P Q)
      ≤ 500 * Real.sqrt (T * r) * (B : ℝ) * Real.sqrt B / ((A : ℝ) * P)
        + 1500 * (B : ℝ) * Real.sqrt B / Real.sqrt (T * r) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hTr : (0 : ℝ) < T * r := by positivity
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by
    have : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hlow := cast_effLow_ge hA hQ
  have hhigh := cast_effHigh_le (B := B) hP
  have hgap := cast_effGap_le (A := A) (B := B) (P := P) (Q := Q) hP
  have hQ2 : (Q : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hQ2P
  have hlow0 : (0 : ℝ) < ((effLow A Q : ℕ) : ℝ) := lt_of_lt_of_le (by positivity) hlow
  -- first term
  have hfirst : 2500 * Real.sqrt (T * r * ((effGap A B P Q : ℕ) : ℝ) ^ 3
      / (((effLow A Q : ℕ) : ℝ) ^ 2 * (36 * Real.pi * P)))
      ≤ 500 * Real.sqrt (T * r) * (B : ℝ) * Real.sqrt B / ((A : ℝ) * P) := by
    have hrad : T * r * ((effGap A B P Q : ℕ) : ℝ) ^ 3
        / (((effLow A Q : ℕ) : ℝ) ^ 2 * (36 * Real.pi * P))
        ≤ (T * r * (B : ℝ) ^ 3 / (((A : ℝ) * P) ^ 2)) / 25 := by
      have hnum : T * r * ((effGap A B P Q : ℕ) : ℝ) ^ 3 ≤ T * r * ((B : ℝ) / P) ^ 3 := by
        have := pow_le_pow_left₀ (Nat.cast_nonneg _) hgap 3
        nlinarith [this, hTr]
      have hden : ((A : ℝ) / (2 * P)) ^ 2 * (36 * Real.pi * P)
          ≤ ((effLow A Q : ℕ) : ℝ) ^ 2 * (36 * Real.pi * P) := by
        have hle : (A : ℝ) / (2 * P) ≤ ((effLow A Q : ℕ) : ℝ) := by
          refine le_trans ?_ hlow
          exact div_le_div_of_nonneg_left hA0.le hQ0 hQ2
        have hsq : ((A : ℝ) / (2 * P)) ^ 2 ≤ ((effLow A Q : ℕ) : ℝ) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hle 2
        exact mul_le_mul_of_nonneg_right hsq (by positivity)
      have hstep : T * r * ((effGap A B P Q : ℕ) : ℝ) ^ 3
          / (((effLow A Q : ℕ) : ℝ) ^ 2 * (36 * Real.pi * P))
          ≤ T * r * ((B : ℝ) / P) ^ 3 / (((A : ℝ) / (2 * P)) ^ 2 * (36 * Real.pi * P)) := by
        refine div_le_div₀ (by positivity) hnum (by positivity) hden
      refine le_trans hstep ?_
      have heq : T * r * ((B : ℝ) / P) ^ 3 / (((A : ℝ) / (2 * P)) ^ 2 * (36 * Real.pi * P))
          = (4 / (36 * Real.pi)) * (T * r * (B : ℝ) ^ 3 / (((A : ℝ) * P) ^ 2)) := by
        field_simp
        ring
      rw [heq]
      have hcoef : (4 : ℝ) / (36 * Real.pi) ≤ 1 / 25 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hpi3]
      have hpos : (0 : ℝ) ≤ T * r * (B : ℝ) ^ 3 / (((A : ℝ) * P) ^ 2) := by positivity
      nlinarith [hcoef, hpos]
    have hsq : Real.sqrt (T * r * ((effGap A B P Q : ℕ) : ℝ) ^ 3
        / (((effLow A Q : ℕ) : ℝ) ^ 2 * (36 * Real.pi * P)))
        ≤ Real.sqrt ((T * r * (B : ℝ) ^ 3 / (((A : ℝ) * P) ^ 2)) / 25) := Real.sqrt_le_sqrt hrad
    have hval : Real.sqrt ((T * r * (B : ℝ) ^ 3 / (((A : ℝ) * P) ^ 2)) / 25)
        = Real.sqrt (T * r) * (B : ℝ) * Real.sqrt B / ((A : ℝ) * P) / 5 := by
      rw [Real.sqrt_div (by positivity) (25 : ℝ),
        show (25 : ℝ) = (5 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num),
        sqrt_cube_div (T * r) (B : ℝ) ((A : ℝ) * P) hTr.le hB0 (by positivity)]
    calc 2500 * Real.sqrt (T * r * ((effGap A B P Q : ℕ) : ℝ) ^ 3
            / (((effLow A Q : ℕ) : ℝ) ^ 2 * (36 * Real.pi * P)))
        ≤ 2500 * (Real.sqrt (T * r) * (B : ℝ) * Real.sqrt B / ((A : ℝ) * P) / 5) :=
          mul_le_mul_of_nonneg_left (hval ▸ hsq) (by norm_num)
      _ = 500 * Real.sqrt (T * r) * (B : ℝ) * Real.sqrt B / ((A : ℝ) * P) := by ring
  -- second term
  have hsecond : 44 * Real.sqrt (36 * Real.pi * ((effHigh B P : ℕ) : ℝ) ^ 2 * (Q : ℝ) ^ 3
      * ((effGap A B P Q : ℕ) : ℝ) / (T * r))
      ≤ 1500 * (B : ℝ) * Real.sqrt B / Real.sqrt (T * r) := by
    have hrad : 36 * Real.pi * ((effHigh B P : ℕ) : ℝ) ^ 2 * (Q : ℝ) ^ 3
        * ((effGap A B P Q : ℕ) : ℝ) / (T * r)
        ≤ (1500 / 44) ^ 2 * ((B : ℝ) ^ 3 / (T * r)) := by
      have hnum : 36 * Real.pi * ((effHigh B P : ℕ) : ℝ) ^ 2 * (Q : ℝ) ^ 3
          * ((effGap A B P Q : ℕ) : ℝ)
          ≤ 36 * Real.pi * ((B : ℝ) / P) ^ 2 * (2 * (P : ℝ)) ^ 3 * ((B : ℝ) / P) := by
        have hEnn : (0 : ℝ) ≤ ((effHigh B P : ℕ) : ℝ) := Nat.cast_nonneg _
        have hGnn : (0 : ℝ) ≤ ((effGap A B P Q : ℕ) : ℝ) := Nat.cast_nonneg _
        gcongr
      have heq : 36 * Real.pi * ((B : ℝ) / P) ^ 2 * (2 * (P : ℝ)) ^ 3 * ((B : ℝ) / P)
          = 288 * Real.pi * (B : ℝ) ^ 3 := by
        field_simp
        ring
      have hcoef : 288 * Real.pi ≤ (1500 / 44 : ℝ) ^ 2 := by
        nlinarith [hpi4]
      have hstep : 36 * Real.pi * ((effHigh B P : ℕ) : ℝ) ^ 2 * (Q : ℝ) ^ 3
          * ((effGap A B P Q : ℕ) : ℝ) ≤ (1500 / 44 : ℝ) ^ 2 * (B : ℝ) ^ 3 := by
        rw [heq] at hnum
        nlinarith [hnum, hcoef, pow_nonneg hB0 3]
      have := div_le_div_of_nonneg_right hstep hTr.le
      calc 36 * Real.pi * ((effHigh B P : ℕ) : ℝ) ^ 2 * (Q : ℝ) ^ 3
            * ((effGap A B P Q : ℕ) : ℝ) / (T * r)
          ≤ (1500 / 44 : ℝ) ^ 2 * (B : ℝ) ^ 3 / (T * r) := this
        _ = (1500 / 44 : ℝ) ^ 2 * ((B : ℝ) ^ 3 / (T * r)) := by ring
    have hsq := Real.sqrt_le_sqrt hrad
    have hval : Real.sqrt ((1500 / 44 : ℝ) ^ 2 * ((B : ℝ) ^ 3 / (T * r)))
        = (1500 / 44 : ℝ) * ((B : ℝ) * Real.sqrt B / Real.sqrt (T * r)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
        Real.sqrt_div (by positivity) (T * r), sqrt_cube (B : ℝ) hB0]
    calc 44 * Real.sqrt (36 * Real.pi * ((effHigh B P : ℕ) : ℝ) ^ 2 * (Q : ℝ) ^ 3
            * ((effGap A B P Q : ℕ) : ℝ) / (T * r))
        ≤ 44 * ((1500 / 44 : ℝ) * ((B : ℝ) * Real.sqrt B / Real.sqrt (T * r))) :=
          mul_le_mul_of_nonneg_left (hval ▸ hsq) (by norm_num)
      _ = 1500 * (B : ℝ) * Real.sqrt B / Real.sqrt (T * r) := by ring
  rw [gapSumBound]
  linarith [hfirst, hsecond]

end

end RHTower.Sieve

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

set_option maxHeartbeats 1600000 in
/-- **The gap sum on a dyadic block, short orientation.** -/
theorem gapSumBound_le_swap {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {A B P Q : ℕ}
    (hA : 1 ≤ A) (hP : 1 ≤ P) (hQ : 2 ≤ Q) (hQ2P : Q ≤ 2 * P) (hPB : P ≤ B) :
    gapSumBound T r P (Q - 1) (effLow A Q) (effHigh B P + 1) (Q - 1 - P)
      ≤ 350 * (P : ℝ) * Real.sqrt (T * r) / Real.sqrt A
        + 3000 * (B : ℝ) * Real.sqrt B / Real.sqrt (T * r) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hTr : (0 : ℝ) < T * r := by positivity
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (le_trans hP hPB)
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by
    have : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith
  have hQ2 : (Q : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hQ2P
  have hlow := cast_effLow_ge hA hQ
  have hhigh := cast_effHigh_le (B := B) hP
  have hlow2 : (A : ℝ) / (2 * P) ≤ ((effLow A Q : ℕ) : ℝ) :=
    le_trans (div_le_div_of_nonneg_left hA0.le hQ0 hQ2) hlow
  have hlow0 : (0 : ℝ) < ((effLow A Q : ℕ) : ℝ) := lt_of_lt_of_le (by positivity) hlow2
  have hH : (((Q - 1 - P : ℕ)) : ℝ) ≤ (P : ℝ) := by
    have : Q - 1 - P ≤ P := by omega
    exact_mod_cast this
  have hHnn : (0 : ℝ) ≤ (((Q - 1 - P : ℕ)) : ℝ) := Nat.cast_nonneg _
  have hM₁ : (((Q - 1 : ℕ)) : ℝ) ≤ 2 * (P : ℝ) := by
    have : Q - 1 ≤ 2 * P := by omega
    exact_mod_cast this
  have hM₁nn : (0 : ℝ) ≤ (((Q - 1 : ℕ)) : ℝ) := Nat.cast_nonneg _
  have hQ' : (((effHigh B P + 1 : ℕ)) : ℝ) ≤ 2 * (B : ℝ) / P := by
    have hone : (1 : ℝ) ≤ (B : ℝ) / P := by
      rw [le_div_iff₀ hP0, one_mul]
      exact_mod_cast hPB
    have h2 : ((effHigh B P : ℕ) : ℝ) + 1 ≤ (B : ℝ) / P + (B : ℝ) / P := add_le_add hhigh hone
    have h3 : (B : ℝ) / P + (B : ℝ) / P = 2 * (B : ℝ) / P := by ring
    push_cast
    linarith [h2, h3]
  have hQ'nn : (0 : ℝ) ≤ (((effHigh B P + 1 : ℕ)) : ℝ) := Nat.cast_nonneg _
  have hfirst : 2500 * Real.sqrt (T * r * (((Q - 1 - P : ℕ)) : ℝ) ^ 3
      / ((P : ℝ) ^ 2 * (36 * Real.pi * ((effLow A Q : ℕ) : ℝ))))
      ≤ 350 * (P : ℝ) * Real.sqrt (T * r) / Real.sqrt A := by
    have hrad : T * r * (((Q - 1 - P : ℕ)) : ℝ) ^ 3
        / ((P : ℝ) ^ 2 * (36 * Real.pi * ((effLow A Q : ℕ) : ℝ)))
        ≤ (350 / 2500 : ℝ) ^ 2 * (T * r * (P : ℝ) ^ 2 / (A : ℝ)) := by
      have hstep : T * r * (((Q - 1 - P : ℕ)) : ℝ) ^ 3
          / ((P : ℝ) ^ 2 * (36 * Real.pi * ((effLow A Q : ℕ) : ℝ)))
          ≤ T * r * (P : ℝ) ^ 3 / ((P : ℝ) ^ 2 * (36 * Real.pi * ((A : ℝ) / (2 * P)))) := by
        gcongr
      refine le_trans hstep ?_
      have heq : T * r * (P : ℝ) ^ 3 / ((P : ℝ) ^ 2 * (36 * Real.pi * ((A : ℝ) / (2 * P))))
          = (2 / (36 * Real.pi)) * (T * r * (P : ℝ) ^ 2 / (A : ℝ)) := by
        field_simp
      rw [heq]
      have hcoef : (2 : ℝ) / (36 * Real.pi) ≤ (350 / 2500 : ℝ) ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hpi3]
      have hpos : (0 : ℝ) ≤ T * r * (P : ℝ) ^ 2 / (A : ℝ) := by positivity
      nlinarith [hcoef, hpos]
    have hsq := Real.sqrt_le_sqrt hrad
    have hval : Real.sqrt ((350 / 2500 : ℝ) ^ 2 * (T * r * (P : ℝ) ^ 2 / (A : ℝ)))
        = (350 / 2500 : ℝ) * ((P : ℝ) * Real.sqrt (T * r) / Real.sqrt A) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
        Real.sqrt_div (by positivity) ((A : ℝ)), Real.sqrt_mul hTr.le, Real.sqrt_sq hP0.le]
      ring
    calc 2500 * Real.sqrt (T * r * (((Q - 1 - P : ℕ)) : ℝ) ^ 3
            / ((P : ℝ) ^ 2 * (36 * Real.pi * ((effLow A Q : ℕ) : ℝ))))
        ≤ 2500 * ((350 / 2500 : ℝ) * ((P : ℝ) * Real.sqrt (T * r) / Real.sqrt A)) :=
          mul_le_mul_of_nonneg_left (hval ▸ hsq) (by norm_num)
      _ = 350 * (P : ℝ) * Real.sqrt (T * r) / Real.sqrt A := by ring
  have hsecond : 44 * Real.sqrt (36 * Real.pi * (((Q - 1 : ℕ)) : ℝ) ^ 2
      * (((effHigh B P + 1 : ℕ)) : ℝ) ^ 3 * (((Q - 1 - P : ℕ)) : ℝ) / (T * r))
      ≤ 3000 * (B : ℝ) * Real.sqrt B / Real.sqrt (T * r) := by
    have hrad : 36 * Real.pi * (((Q - 1 : ℕ)) : ℝ) ^ 2
        * (((effHigh B P + 1 : ℕ)) : ℝ) ^ 3 * (((Q - 1 - P : ℕ)) : ℝ) / (T * r)
        ≤ (3000 / 44 : ℝ) ^ 2 * ((B : ℝ) ^ 3 / (T * r)) := by
      have hnum : 36 * Real.pi * (((Q - 1 : ℕ)) : ℝ) ^ 2
          * (((effHigh B P + 1 : ℕ)) : ℝ) ^ 3 * (((Q - 1 - P : ℕ)) : ℝ)
          ≤ 36 * Real.pi * (2 * (P : ℝ)) ^ 2 * (2 * (B : ℝ) / P) ^ 3 * (P : ℝ) := by
        gcongr
      have heq : 36 * Real.pi * (2 * (P : ℝ)) ^ 2 * (2 * (B : ℝ) / P) ^ 3 * (P : ℝ)
          = 1152 * Real.pi * (B : ℝ) ^ 3 := by
        field_simp
        ring
      have hcoef : 1152 * Real.pi ≤ (3000 / 44 : ℝ) ^ 2 := by
        nlinarith [hpi4]
      have hstep : 36 * Real.pi * (((Q - 1 : ℕ)) : ℝ) ^ 2
          * (((effHigh B P + 1 : ℕ)) : ℝ) ^ 3 * (((Q - 1 - P : ℕ)) : ℝ)
          ≤ (3000 / 44 : ℝ) ^ 2 * (B : ℝ) ^ 3 := by
        rw [heq] at hnum
        nlinarith [hnum, hcoef, pow_nonneg hB0.le 3]
      calc 36 * Real.pi * (((Q - 1 : ℕ)) : ℝ) ^ 2
            * (((effHigh B P + 1 : ℕ)) : ℝ) ^ 3 * (((Q - 1 - P : ℕ)) : ℝ) / (T * r)
          ≤ (3000 / 44 : ℝ) ^ 2 * (B : ℝ) ^ 3 / (T * r) :=
            div_le_div_of_nonneg_right hstep hTr.le
        _ = (3000 / 44 : ℝ) ^ 2 * ((B : ℝ) ^ 3 / (T * r)) := by ring
    have hsq := Real.sqrt_le_sqrt hrad
    have hval : Real.sqrt ((3000 / 44 : ℝ) ^ 2 * ((B : ℝ) ^ 3 / (T * r)))
        = (3000 / 44 : ℝ) * ((B : ℝ) * Real.sqrt B / Real.sqrt (T * r)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
        Real.sqrt_div (by positivity) (T * r), sqrt_cube (B : ℝ) hB0.le]
    calc 44 * Real.sqrt (36 * Real.pi * (((Q - 1 : ℕ)) : ℝ) ^ 2
            * (((effHigh B P + 1 : ℕ)) : ℝ) ^ 3 * (((Q - 1 - P : ℕ)) : ℝ) / (T * r))
        ≤ 44 * ((3000 / 44 : ℝ) * ((B : ℝ) * Real.sqrt B / Real.sqrt (T * r))) :=
          mul_le_mul_of_nonneg_left (hval ▸ hsq) (by norm_num)
      _ = 3000 * (B : ℝ) * Real.sqrt B / Real.sqrt (T * r) := by ring
  rw [gapSumBound]
  linarith [hfirst, hsecond]

end

end RHTower.Sieve
