import GaloisForLFunctions.RHTower.SerreQ8RootNumberNegOneTopRadicand
import GaloisForLFunctions.RHTower.DeningerQ8RootNumberNegOneRadicalLifts

/-!
# Square-class separation of the two Q8 radical presentations

The source-selected radical `√((5 + √5) * (41 + 6 * √41))` and the
traditional Serre radical `√((5 + √5) * (41 + √205))` live over the same
biquadratic field `ℚ(√5, √41)`.  They must not be treated as the same Kummer
extension without proof.  This module proves the exact obstruction: their
radicand quotient is not a square in that base field.

Thus no `ℚ(√5,√41)`-linear identification can transport one top radical to a
base-field multiple of the other.  This is a source-fidelity separation theorem,
not a root-number calculation and not a claim that the abstract degree-eight
fields are non-isomorphic.
-/

namespace RHTower

noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField

local instance : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective

/-- Quotient of the two non-common upper radical factors. -/
def q8PresentationRatio : K2 := serreQ8TopS / deningerQ8RootNumberNegOneTopS

private theorem nat_eightyTwo_not_square : ¬ IsSquare (82 : ℕ) := by
  rintro ⟨n, hn⟩
  by_cases hle : n ≤ 9
  · have hnle : n * n ≤ 9 * 9 := Nat.mul_le_mul hle hle
    have : 82 ≤ 9 * 9 := by rw [hn]; exact hnle
    norm_num at this
  · have hge : 10 ≤ n := by omega
    have hnge : 10 * 10 ≤ n * n := Nat.mul_le_mul hge hge
    have : 10 * 10 ≤ 82 := by rw [hn]; exact hnge
    norm_num at this

private theorem nat_fourHundredTen_not_square : ¬ IsSquare (410 : ℕ) := by
  rintro ⟨n, hn⟩
  by_cases hle : n ≤ 20
  · have hnle : n * n ≤ 20 * 20 := Nat.mul_le_mul hle hle
    have : 410 ≤ 20 * 20 := by rw [hn]; exact hnle
    norm_num at this
  · have hge : 21 ≤ n := by omega
    have hnge : 21 * 21 ≤ n * n := Nat.mul_le_mul hge hge
    have : 21 * 21 ≤ 410 := by rw [hn]; exact hnge
    norm_num at this

private theorem nat_two_not_square : ¬ IsSquare (2 : ℕ) := by
  rintro ⟨n, hn⟩
  by_cases hle : n ≤ 1
  · have hnle : n * n ≤ 1 * 1 := Nat.mul_le_mul hle hle
    have : 2 ≤ 1 * 1 := by rw [hn]; exact hnle
    norm_num at this
  · have hge : 2 ≤ n := by omega
    have hnge : 2 * 2 ≤ n * n := Nat.mul_le_mul hge hge
    have : 2 * 2 ≤ 2 := by
      calc
        2 * 2 ≤ n * n := hnge
        _ = 2 := hn.symm
    norm_num at this

private theorem nat_threeHundredSixty_not_square : ¬ IsSquare (360 : ℕ) := by
  rintro ⟨n, hn⟩
  by_cases hle : n ≤ 18
  · have hnle : n * n ≤ 18 * 18 := Nat.mul_le_mul hle hle
    have : 360 ≤ 18 * 18 := by rw [hn]; exact hnle
    norm_num at this
  · have hge : 19 ≤ n := by omega
    have hnge : 19 * 19 ≤ n * n := Nat.mul_le_mul hge hge
    have : 19 * 19 ≤ 360 := by rw [hn]; exact hnge
    norm_num at this

private theorem firstQuadratic_sq_ne_eightyTwo_div_five (v : K1) :
    v ^ 2 ≠ (82 / 5 : K1) := by
  intro hv
  obtain ⟨r, s, hrs⟩ := deningerQ8RootNumberNegOneFirstQuadratic_normal_form v
  have hscaled : (5 : K1) * v ^ 2 = 82 := by rw [hv]; norm_num
  have hcoord :
      ((5 * r ^ 2 + 25 * s ^ 2 - 82 : ℚ) : K1) +
          (10 * r * s : ℚ) * deningerQ8RootNumberNegOneFirstQuadraticRoot = 0 := by
    calc
      ((5 * r ^ 2 + 25 * s ^ 2 - 82 : ℚ) : K1) +
          (10 * r * s : ℚ) * deningerQ8RootNumberNegOneFirstQuadraticRoot =
          (5 : K1) * ((r : K1) ^ 2 + 2 * (r : K1) * (s : K1) *
            deningerQ8RootNumberNegOneFirstQuadraticRoot + (s : K1) ^ 2 *
              deningerQ8RootNumberNegOneFirstQuadraticRoot ^ 2) - 82 := by
            rw [deningerQ8RootNumberNegOneFirstQuadraticRoot_sq]
            push_cast
            ring
      _ = (5 : K1) * ((r : K1) + s * deningerQ8RootNumberNegOneFirstQuadraticRoot) ^ 2 - 82 := by
        ring
      _ = 0 := by rw [← hrs, hscaled]; ring
  rcases deningerQ8RootNumberNegOneFirstQuadratic_coordinates_eq_zero hcoord with
    ⟨hscalar, hcross⟩
  have hrs0 : r * s = 0 := by
    have hten : (10 : ℚ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp (by simpa [mul_assoc] using hcross)).resolve_left hten
  rcases mul_eq_zero.mp hrs0 with hr | hs
  · apply nat_eightyTwo_not_square
    apply Rat.isSquare_natCast_iff.mp
    refine ⟨5 * s, ?_⟩
    rw [hr] at hscalar
    norm_num [pow_two] at hscalar ⊢
    linarith
  · apply nat_fourHundredTen_not_square
    apply Rat.isSquare_natCast_iff.mp
    refine ⟨5 * r, ?_⟩
    rw [hs] at hscalar
    norm_num [pow_two] at hscalar ⊢
    linarith

private theorem firstQuadratic_sq_ne_serreTraceDefect (v : K1) :
    v ^ 2 ≠ (3362 - 984 * deningerQ8RootNumberNegOneFirstQuadraticRoot) / 205 := by
  intro hv
  obtain ⟨r, s, hrs⟩ := deningerQ8RootNumberNegOneFirstQuadratic_normal_form v
  have hscaled : (205 : K1) * v ^ 2 =
      3362 - 984 * deningerQ8RootNumberNegOneFirstQuadraticRoot := by
    rw [hv]
    field_simp
  have hcoord :
      ((205 * r ^ 2 + 1025 * s ^ 2 - 3362 : ℚ) : K1) +
          (410 * r * s + 984 : ℚ) * deningerQ8RootNumberNegOneFirstQuadraticRoot = 0 := by
    calc
      ((205 * r ^ 2 + 1025 * s ^ 2 - 3362 : ℚ) : K1) +
          (410 * r * s + 984 : ℚ) * deningerQ8RootNumberNegOneFirstQuadraticRoot =
          (205 : K1) * ((r : K1) ^ 2 + 2 * (r : K1) * (s : K1) *
            deningerQ8RootNumberNegOneFirstQuadraticRoot + (s : K1) ^ 2 *
              deningerQ8RootNumberNegOneFirstQuadraticRoot ^ 2) -
            (3362 - 984 * deningerQ8RootNumberNegOneFirstQuadraticRoot) := by
            rw [deningerQ8RootNumberNegOneFirstQuadraticRoot_sq]
            push_cast
            ring
      _ = (205 : K1) * ((r : K1) + s * deningerQ8RootNumberNegOneFirstQuadraticRoot) ^ 2 -
            (3362 - 984 * deningerQ8RootNumberNegOneFirstQuadraticRoot) := by
        ring
      _ = 0 := by rw [← hrs, hscaled]; ring
  rcases deningerQ8RootNumberNegOneFirstQuadratic_coordinates_eq_zero hcoord with
    ⟨hscalar, hcross⟩
  have hscalarEq : 205 * (r ^ 2 + 5 * s ^ 2) = 3362 := by
    nlinarith [hscalar]
  have hcrossEq : 410 * r * s = -984 := by
    nlinarith [hcross]
  have hscalarSq : (205 * (r ^ 2 + 5 * s ^ 2)) ^ 2 = 3362 ^ 2 := by
    rw [hscalarEq]
  have hcrossSq : (410 * r * s) ^ 2 = 984 ^ 2 := by
    rw [hcrossEq]
    norm_num
  have hnormSq : (205 * (r ^ 2 - 5 * s ^ 2)) ^ 2 = 2542 ^ 2 := by
    calc
      (205 * (r ^ 2 - 5 * s ^ 2)) ^ 2 =
          (205 * (r ^ 2 + 5 * s ^ 2)) ^ 2 - 5 * (410 * r * s) ^ 2 := by ring
      _ = 3362 ^ 2 - 5 * 984 ^ 2 := by rw [hscalarSq, hcrossSq]
      _ = 2542 ^ 2 := by norm_num
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hnormSq with hnorm | hnorm
  · have hrSq : r ^ 2 = 72 / 5 := by
      nlinarith [hscalarEq, hnorm]
    apply nat_threeHundredSixty_not_square
    apply Rat.isSquare_natCast_iff.mp
    refine ⟨5 * r, ?_⟩
    norm_num [pow_two] at hrSq ⊢
    linarith
  · have hrSq : r ^ 2 = 2 := by
      nlinarith [hscalarEq, hnorm]
    apply nat_two_not_square
    apply Rat.isSquare_natCast_iff.mp
    refine ⟨r, ?_⟩
    norm_num [pow_two] at hrSq ⊢
    linarith

/-- Relative norm of the presentation ratio. -/
theorem q8PresentationRatio_mul_conj :
    q8PresentationRatio * deningerQ8RootNumberNegOneSecondConjugation q8PresentationRatio =
      (36 / 5 : K2) := by
  unfold q8PresentationRatio
  rw [map_div₀, serreQ8_secondConjugation_topS,
    deningerQ8RootNumberNegOne_secondConjugation_topS]
  have hactual : deningerQ8RootNumberNegOneTopS ≠ 0 := by
    exact deningerQ8RootNumberNegOne_s_ne_zero
      deningerQ8RootNumberNegOneSecondQuadraticRoot_sq
  have hactualConj : deningerQ8RootNumberNegOneTopSConj ≠ 0 := by
    intro h
    have hnorm := deningerQ8RootNumberNegOne_topS_mul_conj
    rw [h] at hnorm
    norm_num at hnorm
  field_simp [hactual, hactualConj]
  rw [serreQ8_topS_mul_conj, deningerQ8RootNumberNegOne_topS_mul_conj]
  norm_num

/-- Relative trace of the presentation ratio. -/
theorem q8PresentationRatio_add_conj :
    q8PresentationRatio + deningerQ8RootNumberNegOneSecondConjugation q8PresentationRatio =
      (3362 - 492 * deningerQ8RootNumberNegOneFirstQuadraticRoot) / 205 := by
  unfold q8PresentationRatio
  rw [map_div₀, serreQ8_secondConjugation_topS,
    deningerQ8RootNumberNegOne_secondConjugation_topS]
  have hactual : deningerQ8RootNumberNegOneTopS ≠ 0 := by
    exact deningerQ8RootNumberNegOne_s_ne_zero
      deningerQ8RootNumberNegOneSecondQuadraticRoot_sq
  have hactualConj : deningerQ8RootNumberNegOneTopSConj ≠ 0 := by
    intro h
    have hnorm := deningerQ8RootNumberNegOne_topS_mul_conj
    rw [h] at hnorm
    norm_num at hnorm
  field_simp [hactual, hactualConj]
  unfold serreQ8TopS serreQ8TopSConj
    deningerQ8RootNumberNegOneTopS deningerQ8RootNumberNegOneTopSConj
  have h41 : AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
      (41 : K1) = (41 : K2) := by
    change AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
      ((41 : ℕ) : K1) = (41 : K2)
    exact (map_natCast
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial) 41).symm
  have h6 : AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
      (6 : K1) = (6 : K2) := by
    change AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
      ((6 : ℕ) : K1) = (6 : K2)
    exact (map_natCast
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial) 6).symm
  rw [h41, h6]
  ring_nf
  rw [deningerQ8RootNumberNegOneSecondQuadraticRoot_sq]
  norm_num
  ring

/-- The quotient of the two upper radical factors is not a square in the
common biquadratic base field. -/
theorem q8PresentationRatio_not_square (w : K2) : w ^ 2 ≠ q8PresentationRatio := by
  intro hw
  let n : K2 := w * deningerQ8RootNumberNegOneSecondConjugation w
  have ha : (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2) ^ 2 = 5 := by
    rw [← map_pow, deningerQ8RootNumberNegOneFirstQuadraticRoot_sq]
    exact (map_natCast
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial) 5).symm
  have ha0 : (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2) ≠ 0 := by
    intro h
    rw [h] at ha
    norm_num at ha
  have hsix : (6 / (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2)) ^ 2 =
      (36 / 5 : K2) := by
    rw [div_pow, ha]
    norm_num
  have hnSq : n ^ 2 = (36 / 5 : K2) := by
    unfold n
    calc
      (w * deningerQ8RootNumberNegOneSecondConjugation w) ^ 2 =
          w ^ 2 * (deningerQ8RootNumberNegOneSecondConjugation w) ^ 2 := by ring
      _ = q8PresentationRatio * deningerQ8RootNumberNegOneSecondConjugation
          q8PresentationRatio := by
        have hconj : (deningerQ8RootNumberNegOneSecondConjugation w) ^ 2 =
            deningerQ8RootNumberNegOneSecondConjugation q8PresentationRatio := by
          rw [← map_pow, hw]
        rw [hw, hconj]
      _ = 36 / 5 := q8PresentationRatio_mul_conj
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hnSq.trans hsix.symm) with hn | hn
  · let t : K2 := w + deningerQ8RootNumberNegOneSecondConjugation w
    have htFixed : deningerQ8RootNumberNegOneSecondConjugation t = t := by
      unfold t
      rw [map_add, deningerQ8RootNumberNegOne_secondConjugation_involutive]
      ring
    obtain ⟨v, hv⟩ := deningerQ8RootNumberNegOne_secondConjugation_fixed_descent t htFixed
    have htSq : t ^ 2 = (82 / 5 : K2) := by
      unfold t
      calc
        (w + deningerQ8RootNumberNegOneSecondConjugation w) ^ 2 = w ^ 2 +
            2 * (w * deningerQ8RootNumberNegOneSecondConjugation w) +
              (deningerQ8RootNumberNegOneSecondConjugation w) ^ 2 := by ring
        _ = q8PresentationRatio + 2 * n +
            deningerQ8RootNumberNegOneSecondConjugation q8PresentationRatio := by
          have hconj : (deningerQ8RootNumberNegOneSecondConjugation w) ^ 2 =
              deningerQ8RootNumberNegOneSecondConjugation q8PresentationRatio := by
            rw [← map_pow, hw]
          rw [hw, hconj]
        _ = (q8PresentationRatio + deningerQ8RootNumberNegOneSecondConjugation
              q8PresentationRatio) + 2 * n := by ring
        _ = (3362 - 492 * deningerQ8RootNumberNegOneFirstQuadraticRoot) / 205 +
            2 * (6 / (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2)) := by
          rw [q8PresentationRatio_add_conj, hn]
        _ = 82 / 5 := by
          field_simp [ha0]
          ring_nf
          rw [ha]
          ring
    apply firstQuadratic_sq_ne_eightyTwo_div_five v
    apply (algebraMap K1 K2).injective
    calc
      algebraMap K1 K2 (v ^ 2) = (v : K2) ^ 2 := map_pow _ v 2
      _ = t ^ 2 := by rw [hv]
      _ = 82 / 5 := htSq
      _ = algebraMap K1 K2 (82 / 5) := by
        rw [map_div₀]
        change (82 : K2) / 5 =
          algebraMap K1 K2 ((82 : ℕ) : K1) / algebraMap K1 K2 ((5 : ℕ) : K1)
        rw [map_natCast (algebraMap K1 K2) 82, map_natCast (algebraMap K1 K2) 5]
        norm_num
  · let t : K2 := w + deningerQ8RootNumberNegOneSecondConjugation w
    have htFixed : deningerQ8RootNumberNegOneSecondConjugation t = t := by
      unfold t
      rw [map_add, deningerQ8RootNumberNegOne_secondConjugation_involutive]
      ring
    obtain ⟨v, hv⟩ := deningerQ8RootNumberNegOne_secondConjugation_fixed_descent t htFixed
    have htSq : t ^ 2 =
        (3362 - 984 * deningerQ8RootNumberNegOneFirstQuadraticRoot) / 205 := by
      unfold t
      calc
        (w + deningerQ8RootNumberNegOneSecondConjugation w) ^ 2 = w ^ 2 +
            2 * (w * deningerQ8RootNumberNegOneSecondConjugation w) +
              (deningerQ8RootNumberNegOneSecondConjugation w) ^ 2 := by ring
        _ = q8PresentationRatio + 2 * n +
            deningerQ8RootNumberNegOneSecondConjugation q8PresentationRatio := by
          have hconj : (deningerQ8RootNumberNegOneSecondConjugation w) ^ 2 =
              deningerQ8RootNumberNegOneSecondConjugation q8PresentationRatio := by
            rw [← map_pow, hw]
          rw [hw, hconj]
        _ = (q8PresentationRatio + deningerQ8RootNumberNegOneSecondConjugation
              q8PresentationRatio) + 2 * n := by ring
        _ = (3362 - 492 * deningerQ8RootNumberNegOneFirstQuadraticRoot) / 205 +
            2 * (-(6 / (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2))) := by
          rw [q8PresentationRatio_add_conj, hn]
        _ = (3362 - 984 * deningerQ8RootNumberNegOneFirstQuadraticRoot) / 205 := by
          field_simp [ha0]
          ring_nf
          rw [ha]
          ring
    apply firstQuadratic_sq_ne_serreTraceDefect v
    apply (algebraMap K1 K2).injective
    calc
      algebraMap K1 K2 (v ^ 2) = (v : K2) ^ 2 := map_pow _ v 2
      _ = t ^ 2 := by rw [hv]
      _ = (3362 - 984 * deningerQ8RootNumberNegOneFirstQuadraticRoot) / 205 := htSq
      _ = algebraMap K1 K2
          ((3362 - 984 * deningerQ8RootNumberNegOneFirstQuadraticRoot) / 205) := by
        rw [map_div₀, map_sub, map_mul]
        change
          ((3362 : K2) - 984 * (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2)) / 205 =
            (algebraMap K1 K2 ((3362 : ℕ) : K1) -
              algebraMap K1 K2 ((984 : ℕ) : K1) *
                algebraMap K1 K2 deningerQ8RootNumberNegOneFirstQuadraticRoot) /
              algebraMap K1 K2 ((205 : ℕ) : K1)
        rw [map_natCast (algebraMap K1 K2) 3362,
          map_natCast (algebraMap K1 K2) 984,
          map_natCast (algebraMap K1 K2) 205]
        rfl

/-- Exact quotient of the top radicands. -/
theorem serreQ8TopRadicand_div_deningerQ8RootNumberNegOneTopRadicand :
    serreQ8TopRadicand / deningerQ8RootNumberNegOneTopRadicand = q8PresentationRatio := by
  have htopR : (deningerQ8RootNumberNegOneTopR : K2) ≠ 0 := by
    intro h
    apply deningerQ8RootNumberNegOne_topR_ne_zero
    apply (algebraMap K1 K2).injective
    simpa using h
  unfold serreQ8TopRadicand deningerQ8RootNumberNegOneTopRadicand q8PresentationRatio
    serreQ8TopR deningerQ8RootNumberNegOneTopR
  have hR :
      AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
        (5 + deningerQ8RootNumberNegOneFirstQuadraticRoot) ≠ 0 := by
    simpa [deningerQ8RootNumberNegOneTopR] using htopR
  field_simp [hR]

/-- The two top radicands have different square classes in the common
biquadratic base field. -/
theorem serreQ8TopRadicand_div_deningerQ8RootNumberNegOneTopRadicand_not_square
    (w : K2) : w ^ 2 ≠ serreQ8TopRadicand / deningerQ8RootNumberNegOneTopRadicand := by
  rw [serreQ8TopRadicand_div_deningerQ8RootNumberNegOneTopRadicand]
  exact q8PresentationRatio_not_square w

end

end RHTower
