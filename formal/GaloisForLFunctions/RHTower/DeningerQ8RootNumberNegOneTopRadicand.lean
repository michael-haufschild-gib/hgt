import GaloisForLFunctions.RHTower.DeningerQ8RootNumberNegOneSecondQuadratic

/-!
# Final quadratic gate for a legacy explicit Q8 radical field

This module constructs the literal radical field historically labelled
`RootNumberNegOne`,
`ℚ(√5, √41, √((5 + √5) * (41 + 6 * √41)))` and proves it has degree eight
over `ℚ`.

The key non-square proof is a genuine relative-norm descent.  The involution
of the second quadratic field sending `√41` to `-√41` fixes any prospective
relative norm.  A square root of the final radicand would therefore descend to
a square root of `205` in `ℚ(√5)`, contradicted by the exact coefficient proof
in the preceding module.

The constructed degree-eight field is now separately proved Galois with group
`Q₈`.  No source has authenticated root number `-1` for it; that claim belongs
to a distinct Serre field and remains a separate formalization obligation.
-/

open Polynomial

namespace RHTower

noncomputable section

/-- The nontrivial involution of the literal second quadratic extension. -/
def deningerQ8RootNumberNegOneSecondConjugation :
    deningerQ8RootNumberNegOneSecondQuadraticField →+*
      deningerQ8RootNumberNegOneSecondQuadraticField :=
  AdjoinRoot.lift
    (algebraMap deningerQ8RootNumberNegOneFirstQuadraticField
      deningerQ8RootNumberNegOneSecondQuadraticField)
    (-deningerQ8RootNumberNegOneSecondQuadraticRoot) (by
      change (X ^ 2 - C (41 : deningerQ8RootNumberNegOneFirstQuadraticField)).eval₂
        (algebraMap deningerQ8RootNumberNegOneFirstQuadraticField
          deningerQ8RootNumberNegOneSecondQuadraticField)
        (-deningerQ8RootNumberNegOneSecondQuadraticRoot) = 0
      rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      rw [neg_sq, deningerQ8RootNumberNegOneSecondQuadraticRoot_sq]
      change (41 : deningerQ8RootNumberNegOneSecondQuadraticField) -
        algebraMap deningerQ8RootNumberNegOneFirstQuadraticField
          deningerQ8RootNumberNegOneSecondQuadraticField
          (41 : deningerQ8RootNumberNegOneFirstQuadraticField) = 0
      change (41 : deningerQ8RootNumberNegOneSecondQuadraticField) -
        algebraMap deningerQ8RootNumberNegOneFirstQuadraticField
          deningerQ8RootNumberNegOneSecondQuadraticField
          ((41 : ℕ) : deningerQ8RootNumberNegOneFirstQuadraticField) = 0
      have h41 := map_natCast
        (algebraMap deningerQ8RootNumberNegOneFirstQuadraticField
          deningerQ8RootNumberNegOneSecondQuadraticField) 41
      rw [h41]
      ring)

theorem deningerQ8RootNumberNegOne_secondConjugation_algebraMap
    (a : deningerQ8RootNumberNegOneFirstQuadraticField) :
    deningerQ8RootNumberNegOneSecondConjugation
      (algebraMap deningerQ8RootNumberNegOneFirstQuadraticField
        deningerQ8RootNumberNegOneSecondQuadraticField a) =
      algebraMap deningerQ8RootNumberNegOneFirstQuadraticField
        deningerQ8RootNumberNegOneSecondQuadraticField a := by
  unfold deningerQ8RootNumberNegOneSecondConjugation
  exact AdjoinRoot.lift_of _

theorem deningerQ8RootNumberNegOne_secondConjugation_root :
    deningerQ8RootNumberNegOneSecondConjugation
      deningerQ8RootNumberNegOneSecondQuadraticRoot =
      -deningerQ8RootNumberNegOneSecondQuadraticRoot := by
  unfold deningerQ8RootNumberNegOneSecondConjugation
  exact AdjoinRoot.lift_root _

theorem deningerQ8RootNumberNegOne_secondConjugation_of
    (a : deningerQ8RootNumberNegOneFirstQuadraticField) :
    deningerQ8RootNumberNegOneSecondConjugation
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial a) =
      AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial a := by
  unfold deningerQ8RootNumberNegOneSecondConjugation
  exact AdjoinRoot.lift_of _

theorem deningerQ8RootNumberNegOne_secondConjugation_normal
    (a b : deningerQ8RootNumberNegOneFirstQuadraticField) :
    deningerQ8RootNumberNegOneSecondConjugation
      (a + b * deningerQ8RootNumberNegOneSecondQuadraticRoot) =
      a - b * deningerQ8RootNumberNegOneSecondQuadraticRoot := by
  rw [map_add, map_mul, deningerQ8RootNumberNegOne_secondConjugation_root]
  rw [deningerQ8RootNumberNegOne_secondConjugation_of,
    deningerQ8RootNumberNegOne_secondConjugation_of]
  ring

/-- Exact descent for elements fixed by the literal second conjugation. -/
theorem deningerQ8RootNumberNegOne_secondConjugation_fixed_descent
    (v : deningerQ8RootNumberNegOneSecondQuadraticField)
    (hv : deningerQ8RootNumberNegOneSecondConjugation v = v) :
    ∃ a : deningerQ8RootNumberNegOneFirstQuadraticField,
      (a : deningerQ8RootNumberNegOneSecondQuadraticField) = v := by
  obtain ⟨a, b, h⟩ := deningerQ8RootNumberNegOneSecondQuadratic_normal_form v
  refine ⟨a, ?_⟩
  rw [h] at hv ⊢
  rw [deningerQ8RootNumberNegOne_secondConjugation_normal] at hv
  letI : CharZero deningerQ8RootNumberNegOneSecondQuadraticField :=
    charZero_of_injective_algebraMap
      (algebraMap ℚ deningerQ8RootNumberNegOneSecondQuadraticField).injective
  have hb : (b : deningerQ8RootNumberNegOneSecondQuadraticField) = 0 := by
    have htwo : (2 : deningerQ8RootNumberNegOneSecondQuadraticField) ≠ 0 := by
      norm_num
    have hroot : deningerQ8RootNumberNegOneSecondQuadraticRoot ≠ 0 := by
      intro hz
      have hs := deningerQ8RootNumberNegOneSecondQuadraticRoot_sq
      rw [hz] at hs
      norm_num at hs
    apply (mul_eq_zero.mp ?_).resolve_right hroot
    have hneg : -((b : deningerQ8RootNumberNegOneSecondQuadraticField) *
          deningerQ8RootNumberNegOneSecondQuadraticRoot) =
        (b : deningerQ8RootNumberNegOneSecondQuadraticField) *
          deningerQ8RootNumberNegOneSecondQuadraticRoot := by
      linear_combination hv
    have htwoby : (2 : deningerQ8RootNumberNegOneSecondQuadraticField) *
        ((b : deningerQ8RootNumberNegOneSecondQuadraticField) *
          deningerQ8RootNumberNegOneSecondQuadraticRoot) = 0 := by
      calc
        (2 : deningerQ8RootNumberNegOneSecondQuadraticField) *
            ((b : deningerQ8RootNumberNegOneSecondQuadraticField) *
              deningerQ8RootNumberNegOneSecondQuadraticRoot) =
            (b : deningerQ8RootNumberNegOneSecondQuadraticField) *
              deningerQ8RootNumberNegOneSecondQuadraticRoot -
                -((b : deningerQ8RootNumberNegOneSecondQuadraticField) *
                  deningerQ8RootNumberNegOneSecondQuadraticRoot) := by
          ring
        _ = 0 := by rw [hneg]; ring
    exact (mul_eq_zero.mp htwoby).resolve_left htwo
  rw [hb]
  simp

theorem deningerQ8RootNumberNegOne_secondConjugation_involutive
    (w : deningerQ8RootNumberNegOneSecondQuadraticField) :
    deningerQ8RootNumberNegOneSecondConjugation
      (deningerQ8RootNumberNegOneSecondConjugation w) = w := by
  obtain ⟨a, b, h⟩ := deningerQ8RootNumberNegOneSecondQuadratic_normal_form w
  calc
    deningerQ8RootNumberNegOneSecondConjugation
        (deningerQ8RootNumberNegOneSecondConjugation w) =
        deningerQ8RootNumberNegOneSecondConjugation
          (a - b * deningerQ8RootNumberNegOneSecondQuadraticRoot) := by
      rw [h, deningerQ8RootNumberNegOne_secondConjugation_normal]
    _ = deningerQ8RootNumberNegOneSecondConjugation
          (a + (-b) * deningerQ8RootNumberNegOneSecondQuadraticRoot) := by
      congr 1
      ring
    _ = a + b * deningerQ8RootNumberNegOneSecondQuadraticRoot := by
      rw [map_add, map_mul, map_neg,
        deningerQ8RootNumberNegOne_secondConjugation_of,
        deningerQ8RootNumberNegOne_secondConjugation_of,
        deningerQ8RootNumberNegOne_secondConjugation_root]
      ring
    _ = w := h.symm

/-- The first factor in the final radicand. -/
def deningerQ8RootNumberNegOneTopR :
    deningerQ8RootNumberNegOneFirstQuadraticField :=
  5 + deningerQ8RootNumberNegOneFirstQuadraticRoot

/-- The `√41`-dependent factor in the final radicand. -/
def deningerQ8RootNumberNegOneTopS :
    deningerQ8RootNumberNegOneSecondQuadraticField :=
  ((41 : deningerQ8RootNumberNegOneFirstQuadraticField) :
    deningerQ8RootNumberNegOneSecondQuadraticField) +
    ((6 : deningerQ8RootNumberNegOneFirstQuadraticField) :
      deningerQ8RootNumberNegOneSecondQuadraticField) *
        deningerQ8RootNumberNegOneSecondQuadraticRoot

def deningerQ8RootNumberNegOneTopSConj :
    deningerQ8RootNumberNegOneSecondQuadraticField :=
  ((41 : deningerQ8RootNumberNegOneFirstQuadraticField) :
    deningerQ8RootNumberNegOneSecondQuadraticField) -
    ((6 : deningerQ8RootNumberNegOneFirstQuadraticField) :
      deningerQ8RootNumberNegOneSecondQuadraticField) *
        deningerQ8RootNumberNegOneSecondQuadraticRoot

/-- The literal final radicand from the documented quaternion witness. -/
def deningerQ8RootNumberNegOneTopRadicand :
    deningerQ8RootNumberNegOneSecondQuadraticField :=
  (deningerQ8RootNumberNegOneTopR :
    deningerQ8RootNumberNegOneSecondQuadraticField) * deningerQ8RootNumberNegOneTopS

theorem deningerQ8RootNumberNegOne_secondConjugation_topS :
    deningerQ8RootNumberNegOneSecondConjugation deningerQ8RootNumberNegOneTopS =
      deningerQ8RootNumberNegOneTopSConj := by
  simpa [deningerQ8RootNumberNegOneTopS, deningerQ8RootNumberNegOneTopSConj] using
    deningerQ8RootNumberNegOne_secondConjugation_normal
      (41 : deningerQ8RootNumberNegOneFirstQuadraticField)
      (6 : deningerQ8RootNumberNegOneFirstQuadraticField)

theorem deningerQ8RootNumberNegOne_topS_mul_conj :
    deningerQ8RootNumberNegOneTopS * deningerQ8RootNumberNegOneTopSConj = 205 := by
  letI : CharZero deningerQ8RootNumberNegOneSecondQuadraticField :=
    charZero_of_injective_algebraMap
      (algebraMap ℚ deningerQ8RootNumberNegOneSecondQuadraticField).injective
  unfold deningerQ8RootNumberNegOneTopS deningerQ8RootNumberNegOneTopSConj
  calc
    ((AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial 41) +
        (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial 6) *
          deningerQ8RootNumberNegOneSecondQuadraticRoot) *
      ((AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial 41) -
        (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial 6) *
          deningerQ8RootNumberNegOneSecondQuadraticRoot) =
        (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial 41) ^ 2 -
          (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial 6) ^ 2 *
            deningerQ8RootNumberNegOneSecondQuadraticRoot ^ 2 := by
      ring
    _ = (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial 41) ^ 2 -
          (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial 6) ^ 2 * 41 := by
      rw [deningerQ8RootNumberNegOneSecondQuadraticRoot_sq]
    _ = 205 := by
      have h41 : AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
          (41 : deningerQ8RootNumberNegOneFirstQuadraticField) =
          (41 : deningerQ8RootNumberNegOneSecondQuadraticField) := by
        change AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
          ((41 : ℕ) : deningerQ8RootNumberNegOneFirstQuadraticField) =
          (41 : deningerQ8RootNumberNegOneSecondQuadraticField)
        exact (map_natCast
          (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial) 41).symm
      have h6 : AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
          (6 : deningerQ8RootNumberNegOneFirstQuadraticField) =
          (6 : deningerQ8RootNumberNegOneSecondQuadraticField) := by
        change AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
          ((6 : ℕ) : deningerQ8RootNumberNegOneFirstQuadraticField) =
          (6 : deningerQ8RootNumberNegOneSecondQuadraticField)
        exact (map_natCast
          (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial) 6).symm
      rw [h41, h6]
      norm_num

theorem deningerQ8RootNumberNegOne_secondConjugation_topRadicand :
    deningerQ8RootNumberNegOneSecondConjugation deningerQ8RootNumberNegOneTopRadicand =
      (deningerQ8RootNumberNegOneTopR :
        deningerQ8RootNumberNegOneSecondQuadraticField) *
          deningerQ8RootNumberNegOneTopSConj := by
  unfold deningerQ8RootNumberNegOneTopRadicand
  rw [map_mul, deningerQ8RootNumberNegOne_secondConjugation_of,
    deningerQ8RootNumberNegOne_secondConjugation_topS]

theorem deningerQ8RootNumberNegOne_topRadicand_mul_conj :
    deningerQ8RootNumberNegOneTopRadicand *
        deningerQ8RootNumberNegOneSecondConjugation
          deningerQ8RootNumberNegOneTopRadicand =
      (205 : deningerQ8RootNumberNegOneSecondQuadraticField) *
        (deningerQ8RootNumberNegOneTopR :
          deningerQ8RootNumberNegOneSecondQuadraticField) ^ 2 := by
  rw [deningerQ8RootNumberNegOne_secondConjugation_topRadicand]
  change (deningerQ8RootNumberNegOneTopR :
      deningerQ8RootNumberNegOneSecondQuadraticField) * deningerQ8RootNumberNegOneTopS *
      ((deningerQ8RootNumberNegOneTopR :
        deningerQ8RootNumberNegOneSecondQuadraticField) *
          deningerQ8RootNumberNegOneTopSConj) =
    205 * (deningerQ8RootNumberNegOneTopR :
      deningerQ8RootNumberNegOneSecondQuadraticField) ^ 2
  calc
    (deningerQ8RootNumberNegOneTopR :
        deningerQ8RootNumberNegOneSecondQuadraticField) * deningerQ8RootNumberNegOneTopS *
        ((deningerQ8RootNumberNegOneTopR :
          deningerQ8RootNumberNegOneSecondQuadraticField) *
            deningerQ8RootNumberNegOneTopSConj) =
        (deningerQ8RootNumberNegOneTopR :
          deningerQ8RootNumberNegOneSecondQuadraticField) ^ 2 *
          (deningerQ8RootNumberNegOneTopS * deningerQ8RootNumberNegOneTopSConj) := by
      ring
    _ = 205 * (deningerQ8RootNumberNegOneTopR :
        deningerQ8RootNumberNegOneSecondQuadraticField) ^ 2 := by
      rw [deningerQ8RootNumberNegOne_topS_mul_conj]
      ring

theorem deningerQ8RootNumberNegOne_topR_ne_zero :
    deningerQ8RootNumberNegOneTopR ≠ 0 := by
  intro h
  letI : CharZero deningerQ8RootNumberNegOneFirstQuadraticField :=
    charZero_of_injective_algebraMap
      (algebraMap ℚ deningerQ8RootNumberNegOneFirstQuadraticField).injective
  have hroot : deningerQ8RootNumberNegOneFirstQuadraticRoot = -5 := by
    dsimp [deningerQ8RootNumberNegOneTopR] at h
    linear_combination h
  have hs := deningerQ8RootNumberNegOneFirstQuadraticRoot_sq
  rw [hroot] at hs
  norm_num at hs

/-- The final radicand is not a square in `ℚ(√5,√41)`. -/
theorem deningerQ8RootNumberNegOne_topRadicand_not_square
    (w : deningerQ8RootNumberNegOneSecondQuadraticField) :
    w ^ 2 ≠ deningerQ8RootNumberNegOneTopRadicand := by
  intro hw
  let r : deningerQ8RootNumberNegOneSecondQuadraticField :=
    deningerQ8RootNumberNegOneTopR
  let n : deningerQ8RootNumberNegOneSecondQuadraticField :=
    w * deningerQ8RootNumberNegOneSecondConjugation w
  let v : deningerQ8RootNumberNegOneSecondQuadraticField := n / r
  have hr : r ≠ 0 := by
    intro hr
    apply deningerQ8RootNumberNegOne_topR_ne_zero
    apply (algebraMap deningerQ8RootNumberNegOneFirstQuadraticField
      deningerQ8RootNumberNegOneSecondQuadraticField).injective
    simpa [r] using hr
  have hn_sq : n ^ 2 = 205 * r ^ 2 := by
    unfold n
    calc
      (w * deningerQ8RootNumberNegOneSecondConjugation w) ^ 2 =
          w ^ 2 * (deningerQ8RootNumberNegOneSecondConjugation w) ^ 2 := by
        ring
      _ = deningerQ8RootNumberNegOneTopRadicand *
          deningerQ8RootNumberNegOneSecondConjugation
            deningerQ8RootNumberNegOneTopRadicand := by
        have hconj : (deningerQ8RootNumberNegOneSecondConjugation w) ^ 2 =
            deningerQ8RootNumberNegOneSecondConjugation
              deningerQ8RootNumberNegOneTopRadicand := by
          rw [← map_pow, hw]
        rw [hw, hconj]
      _ = 205 * r ^ 2 := by
        simpa [r] using deningerQ8RootNumberNegOne_topRadicand_mul_conj
  have hv_sq : v ^ 2 = 205 := by
    unfold v
    rw [div_pow, hn_sq]
    field_simp
  have hn_fixed : deningerQ8RootNumberNegOneSecondConjugation n = n := by
    unfold n
    rw [map_mul, deningerQ8RootNumberNegOne_secondConjugation_involutive]
    ring
  have hr_fixed : deningerQ8RootNumberNegOneSecondConjugation r = r := by
    unfold r deningerQ8RootNumberNegOneTopR
    exact deningerQ8RootNumberNegOne_secondConjugation_of _
  have hv_fixed : deningerQ8RootNumberNegOneSecondConjugation v = v := by
    unfold v
    rw [map_div₀, hn_fixed, hr_fixed]
  obtain ⟨a, ha⟩ :=
    deningerQ8RootNumberNegOne_secondConjugation_fixed_descent v hv_fixed
  apply deningerQ8RootNumberNegOne_twoHundredFive_not_square_in_firstQuadratic a
  apply (algebraMap deningerQ8RootNumberNegOneFirstQuadraticField
    deningerQ8RootNumberNegOneSecondQuadraticField).injective
  calc
    algebraMap deningerQ8RootNumberNegOneFirstQuadraticField
        deningerQ8RootNumberNegOneSecondQuadraticField (a ^ 2) =
        (a : deningerQ8RootNumberNegOneSecondQuadraticField) ^ 2 := by
      exact map_pow _ a 2
    _ = v ^ 2 := by rw [ha]
    _ = 205 := hv_sq
    _ = algebraMap deningerQ8RootNumberNegOneFirstQuadraticField
        deningerQ8RootNumberNegOneSecondQuadraticField
          (205 : deningerQ8RootNumberNegOneFirstQuadraticField) := by
      change (205 : deningerQ8RootNumberNegOneSecondQuadraticField) =
        algebraMap deningerQ8RootNumberNegOneFirstQuadraticField
          deningerQ8RootNumberNegOneSecondQuadraticField ((205 : ℕ) :
            deningerQ8RootNumberNegOneFirstQuadraticField)
      exact (map_natCast
        (algebraMap deningerQ8RootNumberNegOneFirstQuadraticField
          deningerQ8RootNumberNegOneSecondQuadraticField) 205).symm

/-- The final quadratic polynomial of the literal degree-eight radical field. -/
def deningerQ8RootNumberNegOneThirdQuadraticPolynomial :
    deningerQ8RootNumberNegOneSecondQuadraticField[X] :=
  X ^ 2 - C deningerQ8RootNumberNegOneTopRadicand

theorem deningerQ8RootNumberNegOne_thirdQuadratic_irreducible :
    Irreducible deningerQ8RootNumberNegOneThirdQuadraticPolynomial := by
  exact X_pow_sub_C_irreducible_of_prime Nat.prime_two
    deningerQ8RootNumberNegOne_topRadicand_not_square

noncomputable instance :
    Fact (Irreducible deningerQ8RootNumberNegOneThirdQuadraticPolynomial) :=
  ⟨deningerQ8RootNumberNegOne_thirdQuadratic_irreducible⟩

/-- The actual degree-eight radical field in the documented Q8 witness. -/
abbrev deningerQ8RootNumberNegOneTopField :=
  AdjoinRoot deningerQ8RootNumberNegOneThirdQuadraticPolynomial

/-- The literal top radical. -/
def deningerQ8RootNumberNegOneTopRoot : deningerQ8RootNumberNegOneTopField :=
  AdjoinRoot.root deningerQ8RootNumberNegOneThirdQuadraticPolynomial

theorem deningerQ8RootNumberNegOneTopRoot_sq :
    deningerQ8RootNumberNegOneTopRoot ^ 2 = deningerQ8RootNumberNegOneTopRadicand := by
  have h := AdjoinRoot.eval₂_root deningerQ8RootNumberNegOneThirdQuadraticPolynomial
  rw [deningerQ8RootNumberNegOneThirdQuadraticPolynomial, eval₂_sub, eval₂_pow,
    eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

theorem deningerQ8RootNumberNegOneTopField_finrank_over_second :
    Module.finrank deningerQ8RootNumberNegOneSecondQuadraticField
      deningerQ8RootNumberNegOneTopField = 2 := by
  rw [PowerBasis.finrank]
  rw [AdjoinRoot.powerBasis_dim
    deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero]
  norm_num [deningerQ8RootNumberNegOneThirdQuadraticPolynomial]

theorem deningerQ8RootNumberNegOneSecondQuadraticField_finrank_over_rat :
    Module.finrank ℚ deningerQ8RootNumberNegOneSecondQuadraticField = 4 := by
  rw [← Module.finrank_mul_finrank ℚ deningerQ8RootNumberNegOneFirstQuadraticField
    deningerQ8RootNumberNegOneSecondQuadraticField]
  rw [deningerQ8RootNumberNegOneFirstQuadraticField_finrank,
    deningerQ8RootNumberNegOneSecondQuadraticField_finrank]

/-- Exact degree of the literal radical witness field over `ℚ`. -/
theorem deningerQ8RootNumberNegOneTopField_finrank_over_rat :
    Module.finrank ℚ deningerQ8RootNumberNegOneTopField = 8 := by
  rw [← Module.finrank_mul_finrank ℚ deningerQ8RootNumberNegOneSecondQuadraticField
    deningerQ8RootNumberNegOneTopField]
  rw [deningerQ8RootNumberNegOneSecondQuadraticField_finrank_over_rat,
    deningerQ8RootNumberNegOneTopField_finrank_over_second]

end

end RHTower
