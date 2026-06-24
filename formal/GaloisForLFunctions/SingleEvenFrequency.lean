import GaloisForLFunctions.Core

/-!
# Single even frequency determinant

This file formalizes the arithmetic core of
`docs/drafts/pipeline/2-fully-proven/single-even-frequency-not-stieltjes.md`.

For the model seam moments

* `T_1 = B lambda^2`,
* `T_2 = -B lambda^4 / 6`,
* `T_3 = B lambda^6 / 120`,

the first shifted Hankel determinant is negative when `B>0` and `lambda>0`.
No analytic claim about `xi`, Euler products, or RH is formalized here.

The file also formalizes the finite positive-mixture shadow: if every amplitude
and frequency is positive, then the second shifted seam moment of the positive
even-frequency cone is strictly negative.
-/

open scoped BigOperators
open Filter

namespace GaloisForLFunctions

noncomputable section

/-- Exact determinant identity for the first shifted Hankel block of one even frequency. -/
theorem singleEvenFrequency_det_identity (B lambda : Real) :
    (B * lambda ^ 2) * (B * lambda ^ 6 / 120) - (-B * lambda ^ 4 / 6) ^ 2 =
      -7 * B ^ 2 * lambda ^ 8 / 360 := by
  ring

/-- Positivity of the amplitude and frequency makes the determinant strictly negative. -/
theorem singleEvenFrequency_det_neg {B lambda : Real} (hB : 0 < B) (hlambda : 0 < lambda) :
    (B * lambda ^ 2) * (B * lambda ^ 6 / 120) - (-B * lambda ^ 4 / 6) ^ 2 < 0 := by
  rw [singleEvenFrequency_det_identity]
  have hpos : 0 < (7 : Real) * B ^ 2 * lambda ^ 8 / 360 := by positivity
  nlinarith

/-- Exact determinant identity for the half-turn repaired one-frequency moments. -/
theorem singleEvenFrequency_halfTurn_det_identity (B lambda : Real) :
    (B * lambda ^ 2) * (B * lambda ^ 6 / 120) - (B * lambda ^ 4 / 6) ^ 2 =
      -7 * B ^ 2 * lambda ^ 8 / 360 := by
  ring

/-- The half-turn repaired one-frequency moments still have negative determinant. -/
theorem singleEvenFrequency_halfTurn_det_neg {B lambda : Real}
    (hB : 0 < B) (hlambda : 0 < lambda) :
    (B * lambda ^ 2) * (B * lambda ^ 6 / 120) - (B * lambda ^ 4 / 6) ^ 2 < 0 := by
  rw [singleEvenFrequency_halfTurn_det_identity]
  have hpos : 0 < (7 : Real) * B ^ 2 * lambda ^ 8 / 360 := by positivity
  nlinarith

/-- Exact numerator identity for the first Hankel determinant of a repaired two-frequency mixture. -/
theorem twoFrequency_halfTurn_pairNumerator_identity (A C x y : Real) :
    3 * ((A * x + C * y) * (A * x ^ 3 + C * y ^ 3))
      - 10 * (A * x ^ 2 + C * y ^ 2) ^ 2 =
      -7 * A ^ 2 * x ^ 4 - 7 * C ^ 2 * y ^ 4
        + A * C * x * y * (3 * x ^ 2 - 20 * x * y + 3 * y ^ 2) := by
  ring

/-- If the repaired two-frequency cross-term is nonpositive, the first determinant is negative. -/
theorem twoFrequency_halfTurn_det_neg_of_cross_nonpos {A C x y : Real}
    (hA : 0 < A) (hC : 0 < C) (hx : 0 < x) (hy : 0 < y)
    (hcross : 3 * x ^ 2 - 20 * x * y + 3 * y ^ 2 <= 0) :
    ((A * x + C * y) * (A * x ^ 3 + C * y ^ 3)) / 120
        - ((A * x ^ 2 + C * y ^ 2) / 6) ^ 2 < 0 := by
  have hnum :
      3 * ((A * x + C * y) * (A * x ^ 3 + C * y ^ 3))
        - 10 * (A * x ^ 2 + C * y ^ 2) ^ 2 < 0 := by
    rw [twoFrequency_halfTurn_pairNumerator_identity]
    have hdiagA : 0 < 7 * A ^ 2 * x ^ 4 := by positivity
    have hdiagC : 0 < 7 * C ^ 2 * y ^ 4 := by positivity
    have hcoef_nonneg : 0 <= A * C * x * y := by positivity
    have hcrossTerm : A * C * x * y * (3 * x ^ 2 - 20 * x * y + 3 * y ^ 2) <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcoef_nonneg hcross
    nlinarith
  nlinarith

/-- Moment-ratio form of the first repaired Hankel determinant gate. -/
theorem halfTurn_det_neg_of_moment_ratio_lt {M1 M2 M3 : Real}
    (hratio : 3 * (M1 * M3) < 10 * M2 ^ 2) :
    M1 * M3 / 120 - (M2 / 6) ^ 2 < 0 := by
  nlinarith

/-- Below the optimized two-frequency spread threshold, every positive weighting fails. -/
theorem twoFrequency_halfTurn_det_neg_of_ratio_quad_lt {A C x y : Real}
    (hA : 0 < A) (hC : 0 < C) (hx : 0 < x) (hy : 0 < y)
    (hratio : 3 * (x ^ 2 + y ^ 2) < 34 * x * y) :
    ((A * x + C * y) * (A * x ^ 3 + C * y ^ 3)) / 120
        - ((A * x ^ 2 + C * y ^ 2) / 6) ^ 2 < 0 := by
  have hnum :
      3 * ((A * x + C * y) * (A * x ^ 3 + C * y ^ 3))
        - 10 * (A * x ^ 2 + C * y ^ 2) ^ 2 < 0 := by
    rw [twoFrequency_halfTurn_pairNumerator_identity]
    have hcoef_pos : 0 < A * C * x * y := by positivity
    have hcross_lt :
        3 * x ^ 2 - 20 * x * y + 3 * y ^ 2 < 14 * x * y := by
      nlinarith
    have hcrossTerm_lt :
        A * C * x * y * (3 * x ^ 2 - 20 * x * y + 3 * y ^ 2) <
          A * C * x * y * (14 * x * y) :=
      mul_lt_mul_of_pos_left hcross_lt hcoef_pos
    have hsquare : 0 <= (A * x ^ 2 - C * y ^ 2) ^ 2 := sq_nonneg _
    have hdiag_bound :
        A * C * x * y * (14 * x * y) <= 7 * A ^ 2 * x ^ 4 + 7 * C ^ 2 * y ^ 4 := by
      nlinarith
    nlinarith
  have hratioMom :
      3 * ((A * x + C * y) * (A * x ^ 3 + C * y ^ 3)) <
        10 * (A * x ^ 2 + C * y ^ 2) ^ 2 := by
    nlinarith
  exact halfTurn_det_neg_of_moment_ratio_lt hratioMom

/-- Exact determinant for the balanced repaired two-frequency packet. -/
theorem twoFrequency_halfTurn_balanced_det_identity (x y : Real) :
    ((y ^ 2 * x + x ^ 2 * y) * (y ^ 2 * x ^ 3 + x ^ 2 * y ^ 3)) / 120
        - ((y ^ 2 * x ^ 2 + x ^ 2 * y ^ 2) / 6) ^ 2 =
      x ^ 3 * y ^ 3 * (3 * x ^ 2 - 34 * x * y + 3 * y ^ 2) / 360 := by
  ring

/-- Above the optimized spread threshold, a balanced repaired two-frequency packet passes gate one. -/
theorem twoFrequency_halfTurn_balanced_det_pos {x y : Real}
    (hx : 0 < x) (hy : 0 < y) (hratio : 34 * x * y < 3 * (x ^ 2 + y ^ 2)) :
    0 < ((y ^ 2 * x + x ^ 2 * y) * (y ^ 2 * x ^ 3 + x ^ 2 * y ^ 3)) / 120
        - ((y ^ 2 * x ^ 2 + x ^ 2 * y ^ 2) / 6) ^ 2 := by
  rw [twoFrequency_halfTurn_balanced_det_identity]
  have hq : 0 < 3 * x ^ 2 - 34 * x * y + 3 * y ^ 2 := by
    nlinarith
  have hx3 : 0 < x ^ 3 := pow_pos hx 3
  have hy3 : 0 < y ^ 3 := pow_pos hy 3
  have hprod : 0 < x ^ 3 * y ^ 3 * (3 * x ^ 2 - 34 * x * y + 3 * y ^ 2) :=
    mul_pos (mul_pos hx3 hy3) hq
  norm_num [div_pos hprod]

/-- Finite positive mixtures of even frequencies have negative second shifted moment. -/
theorem positiveEvenFrequencyCone_T2_neg {n : Nat} [Nonempty (Fin n)]
    (B lambda : Fin n -> Real) (hB : forall i, 0 < B i) (hlambda : forall i, 0 < lambda i) :
    -((Finset.univ.sum fun i => B i * lambda i ^ 4) / 6) < 0 := by
  have hsum : 0 < Finset.univ.sum fun i : Fin n => B i * lambda i ^ 4 := by
    refine Finset.sum_pos ?hpos ?hnonempty
    case hpos =>
      intro i _
      exact mul_pos (hB i) (pow_pos (hlambda i) 4)
    case hnonempty =>
      exact Finset.univ_nonempty
  nlinarith

/-- In a two-frequency real signed sum, a positive top coefficient controls the tail sign. -/
theorem twoFrequency_dominant_positive_eventually {c1 c2 x1 x2 : Real}
    (hx1 : 0 < x1) (hx12 : x1 < x2) (hc2 : 0 < c2) :
    Filter.Eventually (fun k : Nat => 0 < c1 * x1 ^ k + c2 * x2 ^ k) atTop := by
  have hx2 : 0 < x2 := lt_trans hx1 hx12
  have hr_nonneg : 0 <= x1 / x2 := div_nonneg hx1.le hx2.le
  have hr_lt : x1 / x2 < 1 := by
    rw [div_lt_one hx2]
    exact hx12
  have htend : Tendsto (fun k : Nat => c2 + c1 * (x1 / x2) ^ k) atTop (nhds c2) := by
    have hpow : Tendsto (fun k : Nat => (x1 / x2) ^ k) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr_nonneg hr_lt
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hpow)
  have hev : Filter.Eventually (fun k : Nat => 0 < c2 + c1 * (x1 / x2) ^ k) atTop :=
    htend.eventually (Ioi_mem_nhds hc2)
  filter_upwards [hev] with k hk
  have hpowpos : 0 < x2 ^ k := pow_pos hx2 k
  have hfactor : c1 * x1 ^ k + c2 * x2 ^ k = x2 ^ k * (c2 + c1 * (x1 / x2) ^ k) := by
    rw [div_pow]
    field_simp [hx2.ne']
    ring
  rw [hfactor]
  exact mul_pos hpowpos hk

/-- In a two-frequency real signed sum, a negative top coefficient controls the tail sign. -/
theorem twoFrequency_dominant_negative_eventually {c1 c2 x1 x2 : Real}
    (hx1 : 0 < x1) (hx12 : x1 < x2) (hc2 : c2 < 0) :
    Filter.Eventually (fun k : Nat => c1 * x1 ^ k + c2 * x2 ^ k < 0) atTop := by
  have hpos := twoFrequency_dominant_positive_eventually (c1 := -c1) (c2 := -c2)
    (x1 := x1) (x2 := x2) hx1 hx12 (neg_pos.mpr hc2)
  filter_upwards [hpos] with k hk
  have hneg :
      (-c1) * x1 ^ k + (-c2) * x2 ^ k = -(c1 * x1 ^ k + c2 * x2 ^ k) := by
    ring
  rw [hneg] at hk
  nlinarith

end

end GaloisForLFunctions
