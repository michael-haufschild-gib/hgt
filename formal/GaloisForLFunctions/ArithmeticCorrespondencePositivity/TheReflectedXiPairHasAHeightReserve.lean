import GaloisForLFunctions.RHTower.ZetaTypicalLocalZeroCountLower
import Mathlib.Tactic

/-!
# Reflected-pair bounds

An empty quadratic ascent cone makes every reflected zero pair nonnegative
on the ray to its right. Pairs a bounded nonzero distance away contribute a
uniform positive amount proportional to the ray's starting depth.
-/

open RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- Strict cone separation makes both denominators of a reflected pair positive. -/
theorem reflected_pair_denominators_pos {x b y : ℝ}
    (hsq : b ^ 2 < x ^ 2 + y ^ 2) :
    0 < (x - b) ^ 2 + y ^ 2 ∧ 0 < (x + b) ^ 2 + y ^ 2 := by
  constructor
  · by_contra hd
    have hz : (x - b) ^ 2 + y ^ 2 = 0 :=
      le_antisymm (le_of_not_gt hd) (by positivity)
    have hy2 : y ^ 2 = 0 := by nlinarith only [hz, sq_nonneg (x - b), sq_nonneg y]
    have hxb2 : (x - b) ^ 2 = 0 := by
      nlinarith only [hz, sq_nonneg (x - b), sq_nonneg y]
    have hy : y = 0 := sq_eq_zero_iff.mp hy2
    have hxb : x - b = 0 := sq_eq_zero_iff.mp hxb2
    have hx : x = b := by linarith only [hxb]
    rw [hx, hy] at hsq
    simp at hsq
  · by_contra hd
    have hz : (x + b) ^ 2 + y ^ 2 = 0 :=
      le_antisymm (le_of_not_gt hd) (by positivity)
    have hy2 : y ^ 2 = 0 := by nlinarith only [hz, sq_nonneg (x + b), sq_nonneg y]
    have hxb2 : (x + b) ^ 2 = 0 := by
      nlinarith only [hz, sq_nonneg (x + b), sq_nonneg y]
    have hy : y = 0 := sq_eq_zero_iff.mp hy2
    have hxb : x + b = 0 := sq_eq_zero_iff.mp hxb2
    have hx : x = -b := by linarith only [hxb]
    rw [hx, hy] at hsq
    simp at hsq

/-- Beyond a terminal depth, every reflected pair has nonnegative real part. -/
theorem xiLinePairRe_nonneg_of_quadratic_cone {a x b y : ℝ}
    (ha : 0 ≤ a) (hax : a < x) (hcone : b ^ 2 ≤ a ^ 2 + y ^ 2) :
    0 ≤ xiLinePairRe x b y := by
  have hx : 0 < x := lt_of_le_of_lt ha hax
  have hdiff : 0 < (x - a) * (x + a) :=
    mul_pos (sub_pos.mpr hax) (by linarith)
  have hsq : b ^ 2 < x ^ 2 + y ^ 2 := by nlinarith only [hdiff, hcone]
  obtain ⟨hd1, hd2⟩ := reflected_pair_denominators_pos hsq
  rw [xiLinePairRe_eq_div x b y hd1 hd2]
  have hcore : 0 < x ^ 2 - b ^ 2 + y ^ 2 := by linarith
  positivity

/-- A reflected pair in a fixed-height band contributes a positive depth reserve. -/
theorem xiLinePairRe_height_reserve {a x b y H : ℝ}
    (ha : 0 < a) (hax : a ≤ x) (hx : x ≤ 1 / 2)
    (hb : |b| ≤ 1 / 2) (hy : 1 ≤ |y|) (hyH : |y| ≤ H) :
    ((3 / 2) * a) / (1 + H ^ 2) ^ 2 ≤ xiLinePairRe x b y := by
  have hx0 : 0 < x := lt_of_lt_of_le ha hax
  have hH0 : 0 ≤ H := by linarith [abs_nonneg y]
  have hy2 : 1 ≤ y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
  have hy2H : y ^ 2 ≤ H ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
  have hb2 : b ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith [sq_abs b, abs_nonneg b]
  have hb' := abs_le.mp hb
  have hmlo : -(1 : ℝ) ≤ x - b := by linarith [hb'.2]
  have hmhi : x - b ≤ 1 := by linarith [hb'.1]
  have hplo : -(1 : ℝ) ≤ x + b := by linarith [hb'.1]
  have hphi : x + b ≤ 1 := by linarith [hb'.2]
  have hmsq : (x - b) ^ 2 ≤ 1 := by
    nlinarith only [mul_nonneg (show 0 ≤ 1 - (x - b) by linarith)
      (show 0 ≤ 1 + (x - b) by linarith)]
  have hpsq : (x + b) ^ 2 ≤ 1 := by
    nlinarith only [mul_nonneg (show 0 ≤ 1 - (x + b) by linarith)
      (show 0 ≤ 1 + (x + b) by linarith)]
  have hd1 : 0 < (x - b) ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (x - b)]
  have hd2 : 0 < (x + b) ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (x + b)]
  have hd1le : (x - b) ^ 2 + y ^ 2 ≤ 1 + H ^ 2 := by linarith
  have hd2le : (x + b) ^ 2 + y ^ 2 ≤ 1 + H ^ 2 := by linarith
  have hden : ((x - b) ^ 2 + y ^ 2) * ((x + b) ^ 2 + y ^ 2) ≤
      (1 + H ^ 2) ^ 2 := by
    calc
      _ ≤ (1 + H ^ 2) * (1 + H ^ 2) :=
        mul_le_mul hd1le hd2le hd2.le (by positivity)
      _ = _ := by ring
  have hcore : (3 / 4 : ℝ) ≤ x ^ 2 - b ^ 2 + y ^ 2 := by
    nlinarith only [hb2, hy2, sq_nonneg x]
  have hnum : (3 / 2) * a ≤ 2 * x * (x ^ 2 - b ^ 2 + y ^ 2) := by
    have hprod := mul_nonneg (show 0 ≤ 2 * x by positivity)
      (show 0 ≤ x ^ 2 - b ^ 2 + y ^ 2 - 3 / 4 by linarith)
    nlinarith only [hprod, hax]
  calc
    ((3 / 2) * a) / (1 + H ^ 2) ^ 2 ≤
        ((3 / 2) * a) / (((x - b) ^ 2 + y ^ 2) * ((x + b) ^ 2 + y ^ 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ ≤ (2 * x * (x ^ 2 - b ^ 2 + y ^ 2)) /
        (((x - b) ^ 2 + y ^ 2) * ((x + b) ^ 2 + y ^ 2)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = xiLinePairRe x b y := (xiLinePairRe_eq_div x b y hd1 hd2).symm

/-- The pair at the terminal zero gives its two explicit principal terms. -/
theorem xiLinePairRe_at_zero {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    xiLinePairRe (a + h) a 0 = 1 / h + 1 / (2 * a + h) := by
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hp0 : 2 * a + h ≠ 0 := ne_of_gt (by linarith)
  unfold xiLinePairRe
  have hm : a + h - a = h := by ring
  have hp : a + h + a = 2 * a + h := by ring
  rw [hm, hp]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
  field_simp

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
