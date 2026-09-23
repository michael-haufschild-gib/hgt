import GaloisForLFunctions.Core

/-!
# Single even frequency determinant

This file formalizes the arithmetic core of
`docs/drafts/pipeline/2-fully-proven/single-even-frequency-not-stieltjes.md`.

For the model seam moments

* `T_1 = B lambda^(2 : ℕ)`,
* `T_2 = -B lambda^(4 : ℕ) / 6`,
* `T_3 = B lambda^(6 : ℕ) / 120`,

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
@[aesop safe]
theorem singleEvenFrequency_det_identity (B lambda : Real) :
    (B * lambda ^ (2 : ℕ)) * (B * lambda ^ (6 : ℕ) / 120) - (-B * lambda ^ (4 : ℕ) / 6) ^ (2 : ℕ) =
      -7 * B ^ (2 : ℕ) * lambda ^ (8 : ℕ) / 360 := by
  ring

/-- Positivity of the amplitude and frequency makes the determinant strictly negative. -/
@[aesop safe]
theorem singleEvenFrequency_det_neg {B lambda : Real} (hB : 0 < B) (hlambda : 0 < lambda) :
    (B * lambda ^ (2 : ℕ)) * (B * lambda ^ (6 : ℕ) / 120) - (-B * lambda ^ (4 : ℕ) / 6) ^ (2 : ℕ) < 0 := by
  rw [singleEvenFrequency_det_identity]
  have hpos : 0 < (7 : Real) * B ^ (2 : ℕ) * lambda ^ (8 : ℕ) / 360 := by positivity
  nlinarith

/-- Exact determinant identity for the half-turn repaired one-frequency moments. -/
@[aesop safe]
theorem singleEvenFrequency_halfTurn_det_identity (B lambda : Real) :
    (B * lambda ^ (2 : ℕ)) * (B * lambda ^ (6 : ℕ) / 120) - (B * lambda ^ (4 : ℕ) / 6) ^ (2 : ℕ) =
      -7 * B ^ (2 : ℕ) * lambda ^ (8 : ℕ) / 360 := by
  ring

/-- The half-turn repaired one-frequency moments still have negative determinant. -/
@[aesop safe]
theorem singleEvenFrequency_halfTurn_det_neg {B lambda : Real}
    (hB : 0 < B) (hlambda : 0 < lambda) :
    (B * lambda ^ (2 : ℕ)) * (B * lambda ^ (6 : ℕ) / 120) - (B * lambda ^ (4 : ℕ) / 6) ^ (2 : ℕ) < 0 := by
  rw [singleEvenFrequency_halfTurn_det_identity]
  have hpos : 0 < (7 : Real) * B ^ (2 : ℕ) * lambda ^ (8 : ℕ) / 360 := by positivity
  nlinarith

/-- Exact numerator identity for the first Hankel determinant of a repaired two-frequency mixture. -/
@[aesop safe]
theorem twoFrequency_halfTurn_pairNumerator_identity (A C x y : Real) :
    3 * ((A * x + C * y) * (A * x ^ (3 : ℕ) + C * y ^ (3 : ℕ)))
      - 10 * (A * x ^ (2 : ℕ) + C * y ^ (2 : ℕ)) ^ (2 : ℕ) =
      -7 * A ^ (2 : ℕ) * x ^ (4 : ℕ) - 7 * C ^ (2 : ℕ) * y ^ (4 : ℕ)
        + A * C * x * y * (3 * x ^ (2 : ℕ) - 20 * x * y + 3 * y ^ (2 : ℕ)) := by
  ring

/-- If the repaired two-frequency cross-term is nonpositive, the first determinant is negative. -/
@[aesop safe]
theorem twoFrequency_halfTurn_det_neg_of_cross_nonpos {A C x y : Real}
    (hA : 0 < A) (hC : 0 < C) (hx : 0 < x) (hy : 0 < y)
    (hcross : 3 * x ^ (2 : ℕ) - 20 * x * y + 3 * y ^ (2 : ℕ) <= 0) :
    ((A * x + C * y) * (A * x ^ (3 : ℕ) + C * y ^ (3 : ℕ))) / 120
        - ((A * x ^ (2 : ℕ) + C * y ^ (2 : ℕ)) / 6) ^ (2 : ℕ) < 0 := by
  have hnum :
      3 * ((A * x + C * y) * (A * x ^ (3 : ℕ) + C * y ^ (3 : ℕ)))
        - 10 * (A * x ^ (2 : ℕ) + C * y ^ (2 : ℕ)) ^ (2 : ℕ) < 0 := by
    rw [twoFrequency_halfTurn_pairNumerator_identity]
    have hdiagA : 0 < 7 * A ^ (2 : ℕ) * x ^ (4 : ℕ) := by positivity
    have hdiagC : 0 < 7 * C ^ (2 : ℕ) * y ^ (4 : ℕ) := by positivity
    have hcoef_nonneg : 0 <= A * C * x * y := by positivity
    have hcrossTerm : A * C * x * y * (3 * x ^ (2 : ℕ) - 20 * x * y + 3 * y ^ (2 : ℕ)) <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcoef_nonneg hcross
    nlinarith
  nlinarith

/-- Moment-ratio form of the first repaired Hankel determinant gate. -/
@[aesop safe]
theorem halfTurn_det_neg_of_moment_ratio_lt {M1 M2 M3 : Real}
    (hratio : 3 * (M1 * M3) < 10 * M2 ^ (2 : ℕ)) :
    M1 * M3 / 120 - (M2 / 6) ^ (2 : ℕ) < 0 := by
  nlinarith

/-- Below the optimized two-frequency spread threshold, every positive weighting fails. -/
@[aesop safe]
theorem twoFrequency_halfTurn_det_neg_of_ratio_quad_lt {A C x y : Real}
    (hA : 0 < A) (hC : 0 < C) (hx : 0 < x) (hy : 0 < y)
    (hratio : 3 * (x ^ (2 : ℕ) + y ^ (2 : ℕ)) < 34 * x * y) :
    ((A * x + C * y) * (A * x ^ (3 : ℕ) + C * y ^ (3 : ℕ))) / 120
        - ((A * x ^ (2 : ℕ) + C * y ^ (2 : ℕ)) / 6) ^ (2 : ℕ) < 0 := by
  have hnum :
      3 * ((A * x + C * y) * (A * x ^ (3 : ℕ) + C * y ^ (3 : ℕ)))
        - 10 * (A * x ^ (2 : ℕ) + C * y ^ (2 : ℕ)) ^ (2 : ℕ) < 0 := by
    rw [twoFrequency_halfTurn_pairNumerator_identity]
    have hcoef_pos : 0 < A * C * x * y := by positivity
    have hcross_lt :
        3 * x ^ (2 : ℕ) - 20 * x * y + 3 * y ^ (2 : ℕ) < 14 * x * y := by
      nlinarith
    have hcrossTerm_lt :
        A * C * x * y * (3 * x ^ (2 : ℕ) - 20 * x * y + 3 * y ^ (2 : ℕ)) <
          A * C * x * y * (14 * x * y) :=
      mul_lt_mul_of_pos_left hcross_lt hcoef_pos
    have hsquare : 0 <= (A * x ^ (2 : ℕ) - C * y ^ (2 : ℕ)) ^ (2 : ℕ) := sq_nonneg _
    have hdiag_bound :
        A * C * x * y * (14 * x * y) <= 7 * A ^ (2 : ℕ) * x ^ (4 : ℕ) + 7 * C ^ (2 : ℕ) * y ^ (4 : ℕ) := by
      nlinarith
    nlinarith
  have hratioMom :
      3 * ((A * x + C * y) * (A * x ^ (3 : ℕ) + C * y ^ (3 : ℕ))) <
        10 * (A * x ^ (2 : ℕ) + C * y ^ (2 : ℕ)) ^ (2 : ℕ) := by
    nlinarith
  exact halfTurn_det_neg_of_moment_ratio_lt hratioMom

/-- Exact determinant for the balanced repaired two-frequency packet. -/
@[aesop safe]
theorem twoFrequency_halfTurn_balanced_det_identity (x y : Real) :
    ((y ^ (2 : ℕ) * x + x ^ (2 : ℕ) * y) * (y ^ (2 : ℕ) * x ^ (3 : ℕ) + x ^ (2 : ℕ) * y ^ (3 : ℕ))) / 120
        - ((y ^ (2 : ℕ) * x ^ (2 : ℕ) + x ^ (2 : ℕ) * y ^ (2 : ℕ)) / 6) ^ (2 : ℕ) =
      x ^ (3 : ℕ) * y ^ (3 : ℕ) * (3 * x ^ (2 : ℕ) - 34 * x * y + 3 * y ^ (2 : ℕ)) / 360 := by
  ring

/-- Above the optimized spread threshold, a balanced repaired two-frequency packet passes gate one. -/
@[aesop safe]
theorem twoFrequency_halfTurn_balanced_det_pos {x y : Real}
    (hx : 0 < x) (hy : 0 < y) (hratio : 34 * x * y < 3 * (x ^ (2 : ℕ) + y ^ (2 : ℕ))) :
    0 < ((y ^ (2 : ℕ) * x + x ^ (2 : ℕ) * y) * (y ^ (2 : ℕ) * x ^ (3 : ℕ) + x ^ (2 : ℕ) * y ^ (3 : ℕ))) / 120
        - ((y ^ (2 : ℕ) * x ^ (2 : ℕ) + x ^ (2 : ℕ) * y ^ (2 : ℕ)) / 6) ^ (2 : ℕ) := by
  rw [twoFrequency_halfTurn_balanced_det_identity]
  have hq : 0 < 3 * x ^ (2 : ℕ) - 34 * x * y + 3 * y ^ (2 : ℕ) := by
    nlinarith
  have hx3 : 0 < x ^ (3 : ℕ) := pow_pos hx 3
  have hy3 : 0 < y ^ (3 : ℕ) := pow_pos hy 3
  have hprod : 0 < x ^ (3 : ℕ) * y ^ (3 : ℕ) * (3 * x ^ (2 : ℕ) - 34 * x * y + 3 * y ^ (2 : ℕ)) :=
    mul_pos (mul_pos hx3 hy3) hq
  norm_num [div_pos hprod]

/-- The lower root of the balanced two-frequency first-gate polynomial. -/
def halfTurnLowerThreshold : Real := (17 - 2 * Real.sqrt 70) / 3

/-- The sharp upper spread threshold for the balanced two-frequency first gate. -/
def halfTurnUpperThreshold : Real := (17 + 2 * Real.sqrt 70) / 3

theorem halfTurn_sqrt70_sq : (Real.sqrt 70) ^ (2 : ℕ) = (70 : Real) := by
  exact Real.sq_sqrt (by norm_num)

theorem halfTurn_lowerThreshold_lt_one : halfTurnLowerThreshold < 1 := by
  have hs0 : 0 < Real.sqrt 70 := Real.sqrt_pos.2 (by norm_num)
  have hs : (Real.sqrt 70) ^ (2 : ℕ) = (70 : Real) := halfTurn_sqrt70_sq
  unfold halfTurnLowerThreshold
  nlinarith

/-- Factorization of the sharp first-gate ratio polynomial. -/
theorem halfTurn_ratio_factor (r : Real) :
    3 * r ^ (2 : ℕ) - 34 * r + 3 =
      3 * (r - halfTurnLowerThreshold) * (r - halfTurnUpperThreshold) := by
  have hs : (Real.sqrt 70) ^ (2 : ℕ) = (70 : Real) := halfTurn_sqrt70_sq
  unfold halfTurnLowerThreshold halfTurnUpperThreshold
  nlinarith

theorem halfTurn_ratio_quad_pos_iff {r : Real} (hr : 1 ≤ r) :
    0 < 3 * r ^ (2 : ℕ) - 34 * r + 3 ↔ halfTurnUpperThreshold < r := by
  rw [halfTurn_ratio_factor]
  have hl : 0 < r - halfTurnLowerThreshold :=
    sub_pos.mpr (lt_of_lt_of_le halfTurn_lowerThreshold_lt_one hr)
  constructor
  · intro h
    have hprod : 0 < (r - halfTurnLowerThreshold) * (r - halfTurnUpperThreshold) := by
      nlinarith
    rcases mul_pos_iff.mp hprod with hpos | hneg
    · exact sub_pos.mp hpos.2
    · exact False.elim (not_lt_of_ge hl.le hneg.1)
  · intro h
    have hu : 0 < r - halfTurnUpperThreshold := sub_pos.mpr h
    positivity

theorem halfTurn_ratio_quad_eq_zero_iff {r : Real} (hr : 1 ≤ r) :
    3 * r ^ (2 : ℕ) - 34 * r + 3 = 0 ↔ r = halfTurnUpperThreshold := by
  rw [halfTurn_ratio_factor]
  have hl : 0 < r - halfTurnLowerThreshold :=
    sub_pos.mpr (lt_of_lt_of_le halfTurn_lowerThreshold_lt_one hr)
  constructor
  · intro h
    have hprod : (r - halfTurnLowerThreshold) * (r - halfTurnUpperThreshold) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hprod with hlower | hupper
    · exact False.elim (by nlinarith)
    · exact sub_eq_zero.mp hupper
  · intro h
    rw [h]
    ring

theorem halfTurn_ratio_quad_neg_iff {r : Real} (hr : 1 ≤ r) :
    3 * r ^ (2 : ℕ) - 34 * r + 3 < 0 ↔ r < halfTurnUpperThreshold := by
  rw [halfTurn_ratio_factor]
  have hl : 0 < r - halfTurnLowerThreshold :=
    sub_pos.mpr (lt_of_lt_of_le halfTurn_lowerThreshold_lt_one hr)
  constructor
  · intro h
    have hprod : (r - halfTurnLowerThreshold) * (r - halfTurnUpperThreshold) < 0 := by
      nlinarith
    rcases mul_neg_iff.mp hprod with hpos | hneg
    · exact sub_neg.mp hpos.2
    · exact False.elim (not_lt_of_ge hl.le hneg.1)
  · intro h
    have hu : r - halfTurnUpperThreshold < 0 := sub_neg.mpr h
    have hprod : (r - halfTurnLowerThreshold) * (r - halfTurnUpperThreshold) < 0 :=
      mul_neg_of_pos_of_neg hl hu
    nlinarith

/-- Equality branch of the balanced two-frequency first-gate trichotomy. -/
theorem twoFrequency_halfTurn_balanced_det_eq_zero {x y : Real}
    (hratio : 3 * (x ^ (2 : ℕ) + y ^ (2 : ℕ)) = 34 * x * y) :
    ((y ^ (2 : ℕ) * x + x ^ (2 : ℕ) * y) * (y ^ (2 : ℕ) * x ^ (3 : ℕ) + x ^ (2 : ℕ) * y ^ (3 : ℕ))) / 120
        - ((y ^ (2 : ℕ) * x ^ (2 : ℕ) + x ^ (2 : ℕ) * y ^ (2 : ℕ)) / 6) ^ (2 : ℕ) = 0 := by
  rw [twoFrequency_halfTurn_balanced_det_identity]
  have hq : 3 * x ^ (2 : ℕ) - 34 * x * y + 3 * y ^ (2 : ℕ) = 0 := by
    nlinarith
  rw [hq]
  ring

/-- Negative branch of the balanced two-frequency first-gate trichotomy. -/
theorem twoFrequency_halfTurn_balanced_det_neg {x y : Real}
    (hx : 0 < x) (hy : 0 < y) (hratio : 3 * (x ^ (2 : ℕ) + y ^ (2 : ℕ)) < 34 * x * y) :
    ((y ^ (2 : ℕ) * x + x ^ (2 : ℕ) * y) * (y ^ (2 : ℕ) * x ^ (3 : ℕ) + x ^ (2 : ℕ) * y ^ (3 : ℕ))) / 120
        - ((y ^ (2 : ℕ) * x ^ (2 : ℕ) + x ^ (2 : ℕ) * y ^ (2 : ℕ)) / 6) ^ (2 : ℕ) < 0 := by
  rw [twoFrequency_halfTurn_balanced_det_identity]
  have hq : 3 * x ^ (2 : ℕ) - 34 * x * y + 3 * y ^ (2 : ℕ) < 0 := by
    nlinarith
  have hx3 : 0 < x ^ (3 : ℕ) := pow_pos hx 3
  have hy3 : 0 < y ^ (3 : ℕ) := pow_pos hy 3
  have hprod : x ^ (3 : ℕ) * y ^ (3 : ℕ) * (3 * x ^ (2 : ℕ) - 34 * x * y + 3 * y ^ (2 : ℕ)) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hx3 hy3) hq
  exact div_neg_of_neg_of_pos hprod (by norm_num)

/-- On ratios at least one, the sharp ratio polynomial has its full sign trichotomy
at `halfTurnUpperThreshold`. -/
theorem halfTurn_ratio_quad_sign_trichotomy {x y : Real}
    (hx : 0 < x) (hxy : x ≤ y) :
    (0 < 3 * (x ^ (2 : ℕ) + y ^ (2 : ℕ)) - 34 * x * y ↔ halfTurnUpperThreshold < y / x) ∧
      (3 * (x ^ (2 : ℕ) + y ^ (2 : ℕ)) - 34 * x * y = 0 ↔ y / x = halfTurnUpperThreshold) ∧
      (3 * (x ^ (2 : ℕ) + y ^ (2 : ℕ)) - 34 * x * y < 0 ↔ y / x < halfTurnUpperThreshold) := by
  have hr : 1 ≤ y / x := by
    apply (le_div_iff₀ hx).mpr
    simpa using hxy
  have hx2 : 0 < x ^ (2 : ℕ) := pow_pos hx 2
  have hfactor : 3 * (x ^ (2 : ℕ) + y ^ (2 : ℕ)) - 34 * x * y =
      x ^ (2 : ℕ) * (3 * (y / x) ^ (2 : ℕ) - 34 * (y / x) + 3) := by
    field_simp [hx.ne']
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hfactor]
    constructor
    · intro h
      rcases mul_pos_iff.mp h with hpos | hneg
      · exact (halfTurn_ratio_quad_pos_iff hr).mp hpos.2
      · exact False.elim (not_lt_of_ge hx2.le hneg.1)
    · intro h
      exact mul_pos hx2 ((halfTurn_ratio_quad_pos_iff hr).mpr h)
  · rw [hfactor]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with hx0 | hq
      · exact False.elim (by nlinarith)
      · exact (halfTurn_ratio_quad_eq_zero_iff hr).mp hq
    · intro h
      rw [(halfTurn_ratio_quad_eq_zero_iff hr).mpr h]
      ring
  · rw [hfactor]
    constructor
    · intro h
      rcases mul_neg_iff.mp h with hpos | hneg
      · exact (halfTurn_ratio_quad_neg_iff hr).mp hpos.2
      · exact False.elim (not_lt_of_ge hx2.le hneg.1)
    · intro h
      exact mul_neg_of_pos_of_neg hx2 ((halfTurn_ratio_quad_neg_iff hr).mpr h)

/-- Complete sharp threshold classification for the balanced two-frequency first Hankel gate. -/
theorem twoFrequency_halfTurn_balanced_det_threshold_sharp {x y : Real}
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) :
    (0 < ((y ^ (2 : ℕ) * x + x ^ (2 : ℕ) * y) * (y ^ (2 : ℕ) * x ^ (3 : ℕ) + x ^ (2 : ℕ) * y ^ (3 : ℕ))) / 120
        - ((y ^ (2 : ℕ) * x ^ (2 : ℕ) + x ^ (2 : ℕ) * y ^ (2 : ℕ)) / 6) ^ (2 : ℕ) ↔
      halfTurnUpperThreshold < y / x) ∧
      (((y ^ (2 : ℕ) * x + x ^ (2 : ℕ) * y) * (y ^ (2 : ℕ) * x ^ (3 : ℕ) + x ^ (2 : ℕ) * y ^ (3 : ℕ))) / 120
        - ((y ^ (2 : ℕ) * x ^ (2 : ℕ) + x ^ (2 : ℕ) * y ^ (2 : ℕ)) / 6) ^ (2 : ℕ) = 0 ↔
      y / x = halfTurnUpperThreshold) ∧
      (((y ^ (2 : ℕ) * x + x ^ (2 : ℕ) * y) * (y ^ (2 : ℕ) * x ^ (3 : ℕ) + x ^ (2 : ℕ) * y ^ (3 : ℕ))) / 120
        - ((y ^ (2 : ℕ) * x ^ (2 : ℕ) + x ^ (2 : ℕ) * y ^ (2 : ℕ)) / 6) ^ (2 : ℕ) < 0 ↔
      y / x < halfTurnUpperThreshold) := by
  obtain ⟨hqpos, hqzero, hqneg⟩ := halfTurn_ratio_quad_sign_trichotomy hx hxy
  have hqeq : 3 * x ^ (2 : ℕ) - 34 * x * y + 3 * y ^ (2 : ℕ) =
      3 * (x ^ (2 : ℕ) + y ^ (2 : ℕ)) - 34 * x * y := by ring
  have hQpos : 0 < 3 * x ^ (2 : ℕ) - 34 * x * y + 3 * y ^ (2 : ℕ) ↔
      halfTurnUpperThreshold < y / x := by
    rw [hqeq]
    exact hqpos
  have hQzero : 3 * x ^ (2 : ℕ) - 34 * x * y + 3 * y ^ (2 : ℕ) = 0 ↔
      y / x = halfTurnUpperThreshold := by
    rw [hqeq]
    exact hqzero
  have hQneg : 3 * x ^ (2 : ℕ) - 34 * x * y + 3 * y ^ (2 : ℕ) < 0 ↔
      y / x < halfTurnUpperThreshold := by
    rw [hqeq]
    exact hqneg
  have hscale : 0 < x ^ (3 : ℕ) * y ^ (3 : ℕ) := mul_pos (pow_pos hx 3) (pow_pos hy 3)
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h
      rw [twoFrequency_halfTurn_balanced_det_identity] at h
      have hnum : 0 < x ^ (3 : ℕ) * y ^ (3 : ℕ) * (3 * x ^ (2 : ℕ) - 34 * x * y + 3 * y ^ (2 : ℕ)) := by
        nlinarith
      rcases mul_pos_iff.mp hnum with hpos | hneg
      · exact hQpos.mp hpos.2
      · exact False.elim (not_lt_of_ge hscale.le hneg.1)
    · intro h
      rw [twoFrequency_halfTurn_balanced_det_identity]
      exact div_pos (mul_pos hscale (hQpos.mpr h)) (by norm_num)
  · constructor
    · intro h
      rw [twoFrequency_halfTurn_balanced_det_identity] at h
      have hnum : x ^ (3 : ℕ) * y ^ (3 : ℕ) * (3 * x ^ (2 : ℕ) - 34 * x * y + 3 * y ^ (2 : ℕ)) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hnum with hscale0 | hq
      · exact False.elim (by nlinarith)
      · exact hQzero.mp hq
    · intro h
      rw [twoFrequency_halfTurn_balanced_det_identity, (hQzero.mpr h)]
      ring
  · constructor
    · intro h
      rw [twoFrequency_halfTurn_balanced_det_identity] at h
      have hnum : x ^ (3 : ℕ) * y ^ (3 : ℕ) * (3 * x ^ (2 : ℕ) - 34 * x * y + 3 * y ^ (2 : ℕ)) < 0 := by
        nlinarith
      rcases mul_neg_iff.mp hnum with hpos | hneg
      · exact hQneg.mp hpos.2
      · exact False.elim (not_lt_of_ge hscale.le hneg.1)
    · intro h
      rw [twoFrequency_halfTurn_balanced_det_identity]
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hscale (hQneg.mpr h)) (by norm_num)

/-- Finite positive mixtures of even frequencies have negative second shifted moment. -/
@[aesop safe]
theorem positiveEvenFrequencyCone_T2_neg {n : Nat} [Nonempty (Fin n)]
    (B lambda : Fin n -> Real) (hB : forall i, 0 < B i) (hlambda : forall i, 0 < lambda i) :
    -((Finset.univ.sum fun i => B i * lambda i ^ (4 : ℕ)) / 6) < 0 := by
  have hsum : 0 < Finset.univ.sum fun i : Fin n => B i * lambda i ^ (4 : ℕ) := by
    refine Finset.sum_pos ?hpos ?hnonempty
    case hpos =>
      intro i _
      exact mul_pos (hB i) (pow_pos (hlambda i) 4)
    case hnonempty =>
      exact Finset.univ_nonempty
  nlinarith

/-- In a two-frequency real signed sum, a positive top coefficient controls the tail sign. -/
@[aesop safe]
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
@[aesop safe]
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
