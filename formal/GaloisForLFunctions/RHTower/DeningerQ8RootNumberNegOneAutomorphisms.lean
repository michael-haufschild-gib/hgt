import GaloisForLFunctions.RHTower.DeningerQ8RootNumberNegOnePrimitiveField
import GaloisForLFunctions.RHTower.DeningerQ8RootNumberNegOneRadicalLifts

/-!
# Explicit quaternionic automorphisms of a legacy radical Q8 field

For the literal primitive degree-eight field historically labelled
`RootNumberNegOne`, this module installs the displayed radical formulas as genuine field
automorphisms.  It proves their central-square and anti-commutation laws:
`I² = J² = C`, `C² = 1`, and `I J = C J I`.

Thus the concrete field carries actual quaternionic automorphism structure,
rather than merely a symbolic radical identity.  The field is now separately
proved Galois with group `Q₈`; its root-number-minus-one attribution remains
unverified and belongs to Serre's distinct documented witness.
-/
open Polynomial

namespace RHTower

noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField

def q8FirstConjugation : K1 →+* K1 :=
  AdjoinRoot.lift (algebraMap ℚ K1)
    (-deningerQ8RootNumberNegOneFirstQuadraticRoot) (by
      change (X ^ (2 : ℕ) - C (5 : ℚ)).eval₂ (algebraMap ℚ K1)
        (-deningerQ8RootNumberNegOneFirstQuadraticRoot) = 0
      rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      rw [neg_sq, deningerQ8RootNumberNegOneFirstQuadraticRoot_sq]
      change (5 : K1) - algebraMap ℚ K1 ((5 : ℕ) : ℚ) = 0
      have h5 := map_natCast (algebraMap ℚ K1) 5
      rw [h5]
      ring)

theorem q8FirstConjugation_of (a : ℚ) :
    q8FirstConjugation (AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial a) =
      AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial a := by
  unfold q8FirstConjugation
  exact AdjoinRoot.lift_of _

theorem q8FirstConjugation_root :
    q8FirstConjugation deningerQ8RootNumberNegOneFirstQuadraticRoot =
      -deningerQ8RootNumberNegOneFirstQuadraticRoot := by
  unfold q8FirstConjugation
  exact AdjoinRoot.lift_root _

theorem q8FirstConjugation_rat (a : ℚ) :
    q8FirstConjugation (a : K1) = a := by
  change q8FirstConjugation
    (AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial a) =
      AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial a
  exact q8FirstConjugation_of a

theorem q8FirstConjugation_fortyOne :
    q8FirstConjugation (41 : K1) = 41 := by
  change q8FirstConjugation
    (AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial (41 : ℚ)) =
      AdjoinRoot.of deningerQ8RootNumberNegOneFirstQuadraticPolynomial (41 : ℚ)
  exact q8FirstConjugation_of 41

theorem q8FirstConjugation_normal (a b : ℚ) :
    q8FirstConjugation (a + b * deningerQ8RootNumberNegOneFirstQuadraticRoot) =
      a - b * deningerQ8RootNumberNegOneFirstQuadraticRoot := by
  rw [map_add, map_mul, q8FirstConjugation_root,
    q8FirstConjugation_rat, q8FirstConjugation_rat]
  ring

theorem q8FirstConjugation_involutive (w : K1) :
    q8FirstConjugation (q8FirstConjugation w) = w := by
  obtain ⟨a,b,h⟩ := deningerQ8RootNumberNegOneFirstQuadratic_normal_form w
  calc
    q8FirstConjugation (q8FirstConjugation w) =
        q8FirstConjugation (a - b * deningerQ8RootNumberNegOneFirstQuadraticRoot) := by
      rw [h, q8FirstConjugation_normal]
    _ = q8FirstConjugation
        (a + (-b) * deningerQ8RootNumberNegOneFirstQuadraticRoot) := by
      congr 1
      ring
    _ = a + b * deningerQ8RootNumberNegOneFirstQuadraticRoot := by
      rw [map_add, map_mul, map_neg, q8FirstConjugation_rat,
        q8FirstConjugation_rat, q8FirstConjugation_root]
      ring
    _ = w := h.symm

def q8FirstConjugationToSecond : K1 →+* K2 :=
  (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial).comp
    q8FirstConjugation

def q8FirstConjugationSecond : K2 →+* K2 :=
  AdjoinRoot.lift q8FirstConjugationToSecond
    deningerQ8RootNumberNegOneSecondQuadraticRoot (by
      change (X ^ (2 : ℕ) - C (41 : K1)).eval₂ q8FirstConjugationToSecond
        deningerQ8RootNumberNegOneSecondQuadraticRoot = 0
      rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
        deningerQ8RootNumberNegOneSecondQuadraticRoot_sq]
      change (41 : K2) - q8FirstConjugationToSecond (41 : K1) = 0
      change (41 : K2) -
        AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
          (q8FirstConjugation (41 : K1)) = 0
      rw [q8FirstConjugation_fortyOne]
      rw [deningerQ8RootNumberNegOne_second_fortyOne]
      ring)

theorem q8FirstConjugationSecond_of (a : K1) :
    q8FirstConjugationSecond
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial a) =
      q8FirstConjugationToSecond a := by
  unfold q8FirstConjugationSecond
  exact AdjoinRoot.lift_of _

theorem q8FirstConjugationSecond_root :
    q8FirstConjugationSecond deningerQ8RootNumberNegOneSecondQuadraticRoot =
      deningerQ8RootNumberNegOneSecondQuadraticRoot := by
  unfold q8FirstConjugationSecond
  exact AdjoinRoot.lift_root _

theorem q8FirstConjugationSecond_normal (a b : K1) :
    q8FirstConjugationSecond (a + b * deningerQ8RootNumberNegOneSecondQuadraticRoot) =
      q8FirstConjugationToSecond a + q8FirstConjugationToSecond b *
        deningerQ8RootNumberNegOneSecondQuadraticRoot := by
  rw [map_add, map_mul, q8FirstConjugationSecond_of,
    q8FirstConjugationSecond_of, q8FirstConjugationSecond_root]

theorem q8FirstConjugationSecond_base_twice (a : K1) :
    q8FirstConjugationSecond (q8FirstConjugationToSecond a) =
      AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial a := by
  change q8FirstConjugationSecond
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
        (q8FirstConjugation a)) =
    AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial a
  rw [q8FirstConjugationSecond_of]
  unfold q8FirstConjugationToSecond
  change AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
    (q8FirstConjugation (q8FirstConjugation a)) = _
  rw [q8FirstConjugation_involutive]

theorem q8FirstConjugationSecond_involutive (w : K2) :
    q8FirstConjugationSecond (q8FirstConjugationSecond w) = w := by
  obtain ⟨a,b,h⟩ := deningerQ8RootNumberNegOneSecondQuadratic_normal_form w
  calc
    q8FirstConjugationSecond (q8FirstConjugationSecond w) =
        q8FirstConjugationSecond
          (q8FirstConjugationToSecond a + q8FirstConjugationToSecond b *
            deningerQ8RootNumberNegOneSecondQuadraticRoot) := by
      rw [h, q8FirstConjugationSecond_normal]
    _ = q8FirstConjugationSecond
          (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
            (q8FirstConjugation a) +
            AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
              (q8FirstConjugation b) * deningerQ8RootNumberNegOneSecondQuadraticRoot) := by rfl
    _ = AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial a +
          AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial b *
            deningerQ8RootNumberNegOneSecondQuadraticRoot := by
      rw [map_add, map_mul, q8FirstConjugationSecond_of,
        q8FirstConjugationSecond_of]
      rw [q8FirstConjugationSecond_root]
      change AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
          (q8FirstConjugation (q8FirstConjugation a)) +
          AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
            (q8FirstConjugation (q8FirstConjugation b)) *
              deningerQ8RootNumberNegOneSecondQuadraticRoot = _
      simp_rw [q8FirstConjugation_involutive]
    _ = w := h.symm

def q8IBase : K2 →+* K3 :=
  (AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial).comp
    q8FirstConjugationSecond

def q8JBase : K2 →+* K3 :=
  (AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial).comp
    deningerQ8RootNumberNegOneSecondConjugation

theorem q8IBase_firstRoot :
    q8IBase (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2) =
      -deningerQ8RootNumberNegOneTopX := by
  unfold q8IBase deningerQ8RootNumberNegOneTopX
  change AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
    (q8FirstConjugationSecond
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
        deningerQ8RootNumberNegOneFirstQuadraticRoot)) = _
  rw [q8FirstConjugationSecond_of]
  change AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
    (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
      (q8FirstConjugation deningerQ8RootNumberNegOneFirstQuadraticRoot)) = _
  rw [q8FirstConjugation_root, map_neg, map_neg]

theorem q8IBase_secondRoot :
    q8IBase deningerQ8RootNumberNegOneSecondQuadraticRoot =
      deningerQ8RootNumberNegOneTopY := by
  unfold q8IBase deningerQ8RootNumberNegOneTopY
  change AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
    (q8FirstConjugationSecond deningerQ8RootNumberNegOneSecondQuadraticRoot) = _
  rw [q8FirstConjugationSecond_root]

theorem q8JBase_firstRoot :
    q8JBase (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2) =
      deningerQ8RootNumberNegOneTopX := by
  unfold q8JBase deningerQ8RootNumberNegOneTopX
  change AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
    (deningerQ8RootNumberNegOneSecondConjugation
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
        deningerQ8RootNumberNegOneFirstQuadraticRoot)) = _
  rw [deningerQ8RootNumberNegOne_secondConjugation_of]

theorem q8JBase_secondRoot :
    q8JBase deningerQ8RootNumberNegOneSecondQuadraticRoot =
      -deningerQ8RootNumberNegOneTopY := by
  unfold q8JBase deningerQ8RootNumberNegOneTopY
  change AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
    (deningerQ8RootNumberNegOneSecondConjugation
      deningerQ8RootNumberNegOneSecondQuadraticRoot) = _
  rw [deningerQ8RootNumberNegOne_secondConjugation_root, map_neg]

theorem q8TopRoot_radical_relation :
    deningerQ8RootNumberNegOneTopRoot ^ (2 : ℕ) =
      deningerQ8RootNumberNegOneR deningerQ8RootNumberNegOneTopX *
        deningerQ8RootNumberNegOneS deningerQ8RootNumberNegOneTopY := by
  simpa [deningerQ8RootNumberNegOneTopU,
    deningerQ8RootNumberNegOneTopRInField,
    deningerQ8RootNumberNegOneTopSInField,
    deningerQ8RootNumberNegOneR, deningerQ8RootNumberNegOneS] using
      deningerQ8RootNumberNegOne_topU_eq_topR_mul_topS

theorem q8IBase_rat (q : ℚ) : q8IBase (q : K2) = q := by
  change q8IBase (algebraMap ℚ K2 q) = algebraMap ℚ K3 q
  exact q8IBase.map_rat_algebraMap q

theorem q8JBase_rat (q : ℚ) : q8JBase (q : K2) = q := by
  change q8JBase (algebraMap ℚ K2 q) = algebraMap ℚ K3 q
  exact q8JBase.map_rat_algebraMap q

theorem q8IBase_topR :
    q8IBase (deningerQ8RootNumberNegOneTopR : K2) =
      deningerQ8RootNumberNegOneRConj deningerQ8RootNumberNegOneTopX := by
  unfold deningerQ8RootNumberNegOneTopR deningerQ8RootNumberNegOneRConj
  rw [map_add]
  change q8IBase (5 + (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2)) = _
  rw [map_add, q8IBase_firstRoot]
  change q8IBase ((5 : ℚ) : K2) - deningerQ8RootNumberNegOneTopX = _
  rw [q8IBase_rat]
  norm_num

theorem q8IBase_topS :
    q8IBase deningerQ8RootNumberNegOneTopS =
      deningerQ8RootNumberNegOneS deningerQ8RootNumberNegOneTopY := by
  unfold deningerQ8RootNumberNegOneTopS deningerQ8RootNumberNegOneS
  change q8IBase ((41 : K2) + (6 : K2) *
    deningerQ8RootNumberNegOneSecondQuadraticRoot) = _
  rw [map_add, map_mul, q8IBase_secondRoot]
  change q8IBase ((41 : ℚ) : K2) + q8IBase ((6 : ℚ) : K2) *
    deningerQ8RootNumberNegOneTopY = _
  rw [q8IBase_rat, q8IBase_rat]
  norm_num

theorem q8JBase_topR :
    q8JBase (deningerQ8RootNumberNegOneTopR : K2) =
      deningerQ8RootNumberNegOneR deningerQ8RootNumberNegOneTopX := by
  unfold deningerQ8RootNumberNegOneTopR deningerQ8RootNumberNegOneR
  rw [map_add]
  change q8JBase (5 + (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2)) = _
  rw [map_add, q8JBase_firstRoot]
  change q8JBase ((5 : ℚ) : K2) + deningerQ8RootNumberNegOneTopX = _
  rw [q8JBase_rat]
  norm_num

theorem q8JBase_topS :
    q8JBase deningerQ8RootNumberNegOneTopS =
      deningerQ8RootNumberNegOneSConj deningerQ8RootNumberNegOneTopY := by
  unfold deningerQ8RootNumberNegOneTopS deningerQ8RootNumberNegOneSConj
  change q8JBase ((41 : K2) + (6 : K2) *
    deningerQ8RootNumberNegOneSecondQuadraticRoot) = _
  rw [map_add, map_mul, q8JBase_secondRoot]
  change q8JBase ((41 : ℚ) : K2) + q8JBase ((6 : ℚ) : K2) *
    (-deningerQ8RootNumberNegOneTopY) = _
  rw [q8JBase_rat, q8JBase_rat]
  norm_num
  ring

theorem q8IBase_topRadicand :
    q8IBase deningerQ8RootNumberNegOneTopRadicand =
      deningerQ8RootNumberNegOneRConj deningerQ8RootNumberNegOneTopX *
        deningerQ8RootNumberNegOneS deningerQ8RootNumberNegOneTopY := by
  unfold deningerQ8RootNumberNegOneTopRadicand
  rw [map_mul, q8IBase_topR, q8IBase_topS]

theorem q8JBase_topRadicand :
    q8JBase deningerQ8RootNumberNegOneTopRadicand =
      deningerQ8RootNumberNegOneR deningerQ8RootNumberNegOneTopX *
        deningerQ8RootNumberNegOneSConj deningerQ8RootNumberNegOneTopY := by
  unfold deningerQ8RootNumberNegOneTopRadicand
  rw [map_mul, q8JBase_topR, q8JBase_topS]

def q8ITopCandidate : K3 :=
  deningerQ8RootNumberNegOneILift deningerQ8RootNumberNegOneTopX
    deningerQ8RootNumberNegOneTopY deningerQ8RootNumberNegOneTopRoot

def q8JTopCandidate : K3 :=
  deningerQ8RootNumberNegOneJLift deningerQ8RootNumberNegOneTopX
    deningerQ8RootNumberNegOneTopY deningerQ8RootNumberNegOneTopRoot

def q8I : K3 →+* K3 :=
  AdjoinRoot.lift q8IBase q8ITopCandidate (by
    letI : CharZero K3 :=
      charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
    change (X ^ (2 : ℕ) - C deningerQ8RootNumberNegOneTopRadicand).eval₂ q8IBase
      q8ITopCandidate = 0
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    change q8ITopCandidate ^ (2 : ℕ) - q8IBase deningerQ8RootNumberNegOneTopRadicand = 0
    have hz := q8TopRoot_radical_relation
    rw [show q8ITopCandidate ^ (2 : ℕ) =
      deningerQ8RootNumberNegOneRConj deningerQ8RootNumberNegOneTopX *
        deningerQ8RootNumberNegOneS deningerQ8RootNumberNegOneTopY by
          exact deningerQ8RootNumberNegOne_iLift_sq
            deningerQ8RootNumberNegOne_topX_sq
            deningerQ8RootNumberNegOne_topY_sq hz]
    rw [q8IBase_topRadicand]
    ring)

def q8J : K3 →+* K3 :=
  AdjoinRoot.lift q8JBase q8JTopCandidate (by
    letI : CharZero K3 :=
      charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
    change (X ^ (2 : ℕ) - C deningerQ8RootNumberNegOneTopRadicand).eval₂ q8JBase
      q8JTopCandidate = 0
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    change q8JTopCandidate ^ (2 : ℕ) - q8JBase deningerQ8RootNumberNegOneTopRadicand = 0
    have hz := q8TopRoot_radical_relation
    rw [show q8JTopCandidate ^ (2 : ℕ) =
      deningerQ8RootNumberNegOneR deningerQ8RootNumberNegOneTopX *
        deningerQ8RootNumberNegOneSConj deningerQ8RootNumberNegOneTopY by
          exact deningerQ8RootNumberNegOne_jLift_sq
            deningerQ8RootNumberNegOne_topX_sq
            deningerQ8RootNumberNegOne_topY_sq hz]
    rw [q8JBase_topRadicand]
    ring)

theorem q8I_root : q8I deningerQ8RootNumberNegOneTopRoot = q8ITopCandidate := by
  unfold q8I
  exact AdjoinRoot.lift_root _

theorem q8J_root : q8J deningerQ8RootNumberNegOneTopRoot = q8JTopCandidate := by
  unfold q8J
  exact AdjoinRoot.lift_root _

theorem q8I_of (a : K2) :
    q8I (AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial a) =
      q8IBase a := by
  unfold q8I
  exact AdjoinRoot.lift_of _

theorem q8J_of (a : K2) :
    q8J (AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial a) =
      q8JBase a := by
  unfold q8J
  exact AdjoinRoot.lift_of _

theorem q8I_topX :
    q8I deningerQ8RootNumberNegOneTopX = -deningerQ8RootNumberNegOneTopX := by
  unfold deningerQ8RootNumberNegOneTopX
  rw [q8I_of, q8IBase_firstRoot]
  simp [deningerQ8RootNumberNegOneTopX]

theorem q8I_topY :
    q8I deningerQ8RootNumberNegOneTopY = deningerQ8RootNumberNegOneTopY := by
  unfold deningerQ8RootNumberNegOneTopY
  rw [q8I_of, q8IBase_secondRoot]
  simp [deningerQ8RootNumberNegOneTopY]

theorem q8J_topX :
    q8J deningerQ8RootNumberNegOneTopX = deningerQ8RootNumberNegOneTopX := by
  unfold deningerQ8RootNumberNegOneTopX
  rw [q8J_of, q8JBase_firstRoot]
  simp [deningerQ8RootNumberNegOneTopX]

theorem q8J_topY :
    q8J deningerQ8RootNumberNegOneTopY = -deningerQ8RootNumberNegOneTopY := by
  unfold deningerQ8RootNumberNegOneTopY
  rw [q8J_of, q8JBase_secondRoot]
  simp [deningerQ8RootNumberNegOneTopY]

theorem q8I_rat (q : ℚ) : q8I (q : K3) = q := by
  change q8I (algebraMap ℚ K3 q) = algebraMap ℚ K3 q
  exact q8I.map_rat_algebraMap q

theorem q8J_rat (q : ℚ) : q8J (q : K3) = q := by
  change q8J (algebraMap ℚ K3 q) = algebraMap ℚ K3 q
  exact q8J.map_rat_algebraMap q

theorem q8I_topSInField :
    q8I deningerQ8RootNumberNegOneTopSInField =
      deningerQ8RootNumberNegOneTopSInField := by
  unfold deningerQ8RootNumberNegOneTopSInField
  rw [map_add, map_mul, q8I_topY]
  change q8I ((41 : ℚ) : K3) + q8I ((6 : ℚ) : K3) *
    deningerQ8RootNumberNegOneTopY = _
  rw [q8I_rat, q8I_rat]
  norm_num

theorem q8J_topRInField :
    q8J deningerQ8RootNumberNegOneTopRInField =
      deningerQ8RootNumberNegOneTopRInField := by
  unfold deningerQ8RootNumberNegOneTopRInField
  rw [map_add, q8J_topX]
  change q8J ((5 : ℚ) : K3) + deningerQ8RootNumberNegOneTopX = _
  rw [q8J_rat]
  norm_num

theorem q8I_topRInField :
    q8I deningerQ8RootNumberNegOneTopRInField =
      deningerQ8RootNumberNegOneRConj deningerQ8RootNumberNegOneTopX := by
  unfold deningerQ8RootNumberNegOneTopRInField
  rw [map_add, q8I_topX]
  change q8I ((5 : ℚ) : K3) - deningerQ8RootNumberNegOneTopX = _
  rw [q8I_rat]
  norm_num
  unfold deningerQ8RootNumberNegOneRConj
  ring

theorem q8J_topSInField :
    q8J deningerQ8RootNumberNegOneTopSInField =
      deningerQ8RootNumberNegOneSConj deningerQ8RootNumberNegOneTopY := by
  unfold deningerQ8RootNumberNegOneTopSInField
  rw [map_add, map_mul, q8J_topY]
  change q8J ((41 : ℚ) : K3) + q8J ((6 : ℚ) : K3) *
    (-deningerQ8RootNumberNegOneTopY) = _
  rw [q8J_rat, q8J_rat]
  norm_num
  unfold deningerQ8RootNumberNegOneSConj
  ring

theorem q8TopX_ne_zero : deningerQ8RootNumberNegOneTopX ≠ 0 := by
  intro h
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  have hs := deningerQ8RootNumberNegOne_topX_sq
  rw [h] at hs
  norm_num at hs

theorem q8TopSInField_ne_zero : deningerQ8RootNumberNegOneTopSInField ≠ 0 := by
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  exact deningerQ8RootNumberNegOne_s_ne_zero
    deningerQ8RootNumberNegOne_topY_sq

theorem q8TopRoot_ne_zero : deningerQ8RootNumberNegOneTopRoot ≠ 0 := by
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  exact deningerQ8RootNumberNegOne_z_ne_zero
    deningerQ8RootNumberNegOne_topX_sq
    deningerQ8RootNumberNegOne_topY_sq q8TopRoot_radical_relation

theorem q8I_candidate : q8I q8ITopCandidate = -deningerQ8RootNumberNegOneTopRoot := by
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  unfold q8ITopCandidate deningerQ8RootNumberNegOneILift
  rw [map_div₀, map_mul, map_mul, q8I_topX, q8I_root]
  change q8I ((2 : ℚ) : K3) * (-deningerQ8RootNumberNegOneTopX) *
      q8I deningerQ8RootNumberNegOneTopSInField / q8ITopCandidate = _
  rw [q8I_rat, q8I_topSInField]
  unfold q8ITopCandidate deningerQ8RootNumberNegOneILift
  have hS : deningerQ8RootNumberNegOneTopSInField =
      deningerQ8RootNumberNegOneS deningerQ8RootNumberNegOneTopY := by rfl
  have hs : deningerQ8RootNumberNegOneS deningerQ8RootNumberNegOneTopY ≠ 0 := by
    simpa [hS] using q8TopSInField_ne_zero
  rw [hS]
  field_simp [q8TopX_ne_zero, hs, q8TopRoot_ne_zero]
  ring

theorem q8TopY_ne_zero : deningerQ8RootNumberNegOneTopY ≠ 0 := by
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  exact deningerQ8RootNumberNegOne_y_ne_zero
    deningerQ8RootNumberNegOne_topY_sq

theorem q8J_candidate : q8J q8JTopCandidate = -deningerQ8RootNumberNegOneTopRoot := by
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  unfold q8JTopCandidate deningerQ8RootNumberNegOneJLift
  rw [map_div₀, map_mul, map_mul, q8J_topX, q8J_topY,
    q8J_root]
  change deningerQ8RootNumberNegOneTopX *
      (-deningerQ8RootNumberNegOneTopY) *
        q8J deningerQ8RootNumberNegOneTopRInField / q8JTopCandidate = _
  rw [q8J_topRInField]
  unfold q8JTopCandidate deningerQ8RootNumberNegOneJLift
  have hR : deningerQ8RootNumberNegOneTopRInField =
      deningerQ8RootNumberNegOneR deningerQ8RootNumberNegOneTopX := by rfl
  have hr : deningerQ8RootNumberNegOneR deningerQ8RootNumberNegOneTopX ≠ 0 := by
    simpa [hR] using deningerQ8RootNumberNegOne_topRInField_ne_zero
  rw [hR]
  field_simp [q8TopX_ne_zero, q8TopY_ne_zero, hr, q8TopRoot_ne_zero]

theorem q8End_eq_of_topRoot (f g : K3 →+* K3)
    (hroot : f deningerQ8RootNumberNegOneTopRoot =
      g deningerQ8RootNumberNegOneTopRoot) : f = g := by
  apply RingHom.ext
  intro w
  have hw : w ∈ deningerQ8RootNumberNegOnePrimitiveField := by
    rw [deningerQ8RootNumberNegOne_primitiveField_eq_top]
    trivial
  refine IntermediateField.adjoin_induction
    (F := ℚ) (s := {deningerQ8RootNumberNegOneTopRoot})
    (p := fun x _ => f x = g x) ?_ ?_ ?_ ?_ ?_ hw
  · intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hroot
  · intro q
    exact (f.map_rat_algebraMap q).trans (g.map_rat_algebraMap q).symm
  · intro x y _ _ hx hy
    rw [map_add, map_add, hx, hy]
  · intro x _ hx
    rw [map_inv₀, map_inv₀, hx]
  · intro x y _ _ hx hy
    rw [map_mul, map_mul, hx, hy]

def q8C : K3 →+* K3 :=
  AdjoinRoot.lift (AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial)
    (-deningerQ8RootNumberNegOneTopRoot) (by
      change (X ^ (2 : ℕ) - C deningerQ8RootNumberNegOneTopRadicand).eval₂
        (AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial)
        (-deningerQ8RootNumberNegOneTopRoot) = 0
      rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, neg_sq,
        deningerQ8RootNumberNegOneTopRoot_sq]
      ring)

theorem q8C_root :
    q8C deningerQ8RootNumberNegOneTopRoot = -deningerQ8RootNumberNegOneTopRoot := by
  unfold q8C
  exact AdjoinRoot.lift_root _

theorem q8C_of (a : K2) :
    q8C (AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial a) =
      AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial a := by
  unfold q8C
  exact AdjoinRoot.lift_of _

theorem q8I_sq_eq_q8C : q8I.comp q8I = q8C := by
  apply q8End_eq_of_topRoot
  rw [RingHom.comp_apply, q8I_root, q8I_candidate, q8C_root]

theorem q8J_sq_eq_q8C : q8J.comp q8J = q8C := by
  apply q8End_eq_of_topRoot
  rw [RingHom.comp_apply, q8J_root, q8J_candidate, q8C_root]

theorem q8C_sq_eq_id : q8C.comp q8C = RingHom.id K3 := by
  apply q8End_eq_of_topRoot
  rw [RingHom.comp_apply, q8C_root, map_neg, q8C_root]
  simp

theorem q8I_fourth_apply (w : K3) :
    q8I (q8I (q8I (q8I w))) = w := by
  have hI (v : K3) : q8I (q8I v) = q8C v := by
    exact congrArg (fun h : K3 →+* K3 => h v) q8I_sq_eq_q8C
  have hC (v : K3) : q8C (q8C v) = v := by
    have hc := congrArg (fun h : K3 →+* K3 => h v) q8C_sq_eq_id
    simpa [RingHom.comp_apply] using hc
  calc
    q8I (q8I (q8I (q8I w))) = q8C (q8I (q8I w)) := hI _
    _ = q8C (q8C w) := by rw [hI w]
    _ = w := hC w

theorem q8J_fourth_apply (w : K3) :
    q8J (q8J (q8J (q8J w))) = w := by
  have hJ (v : K3) : q8J (q8J v) = q8C v := by
    exact congrArg (fun h : K3 →+* K3 => h v) q8J_sq_eq_q8C
  have hC (v : K3) : q8C (q8C v) = v := by
    have hc := congrArg (fun h : K3 →+* K3 => h v) q8C_sq_eq_id
    simpa [RingHom.comp_apply] using hc
  calc
    q8J (q8J (q8J (q8J w))) = q8C (q8J (q8J w)) := hJ _
    _ = q8C (q8C w) := by rw [hJ w]
    _ = w := hC w

theorem q8I_bijective : Function.Bijective q8I := by
  constructor
  · intro a b hab
    calc
      a = q8I (q8I (q8I (q8I a))) := (q8I_fourth_apply a).symm
      _ = q8I (q8I (q8I (q8I b))) := by rw [hab]
      _ = b := q8I_fourth_apply b
  · intro w
    refine ⟨q8I (q8I (q8I w)), ?_⟩
    exact q8I_fourth_apply w

theorem q8J_bijective : Function.Bijective q8J := by
  constructor
  · intro a b hab
    calc
      a = q8J (q8J (q8J (q8J a))) := (q8J_fourth_apply a).symm
      _ = q8J (q8J (q8J (q8J b))) := by rw [hab]
      _ = b := q8J_fourth_apply b
  · intro w
    refine ⟨q8J (q8J (q8J w)), ?_⟩
    exact q8J_fourth_apply w

noncomputable def q8IEquiv : K3 ≃+* K3 := RingEquiv.ofBijective q8I q8I_bijective
noncomputable def q8JEquiv : K3 ≃+* K3 := RingEquiv.ofBijective q8J q8J_bijective

theorem q8I_JCandidate :
    q8I q8JTopCandidate = deningerQ8RootNumberNegOneIThenJ
      deningerQ8RootNumberNegOneTopX deningerQ8RootNumberNegOneTopY
        deningerQ8RootNumberNegOneTopRoot := by
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  unfold q8JTopCandidate deningerQ8RootNumberNegOneJLift
  rw [map_div₀, map_mul, map_mul, q8I_topX, q8I_topY, q8I_root]
  change (-deningerQ8RootNumberNegOneTopX) * deningerQ8RootNumberNegOneTopY *
    q8I deningerQ8RootNumberNegOneTopRInField / q8ITopCandidate = _
  rw [q8I_topRInField]
  unfold q8ITopCandidate deningerQ8RootNumberNegOneILift
    deningerQ8RootNumberNegOneIThenJ
  have hS : deningerQ8RootNumberNegOneTopSInField =
      deningerQ8RootNumberNegOneS deningerQ8RootNumberNegOneTopY := by rfl
  have hs : deningerQ8RootNumberNegOneS deningerQ8RootNumberNegOneTopY ≠ 0 := by
    simpa [hS] using q8TopSInField_ne_zero
  field_simp [q8TopX_ne_zero, q8TopY_ne_zero, hs, q8TopRoot_ne_zero]

theorem q8J_ICandidate :
    q8J q8ITopCandidate = deningerQ8RootNumberNegOneJThenI
      deningerQ8RootNumberNegOneTopX deningerQ8RootNumberNegOneTopY
        deningerQ8RootNumberNegOneTopRoot := by
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  unfold q8ITopCandidate deningerQ8RootNumberNegOneILift
  rw [map_div₀, map_mul, map_mul, q8J_topX, q8J_root]
  change q8J ((2 : ℚ) : K3) * deningerQ8RootNumberNegOneTopX *
    q8J deningerQ8RootNumberNegOneTopSInField / q8JTopCandidate = _
  rw [q8J_rat, q8J_topSInField]
  unfold q8JTopCandidate deningerQ8RootNumberNegOneJLift
    deningerQ8RootNumberNegOneJThenI
  have hR : deningerQ8RootNumberNegOneTopRInField =
      deningerQ8RootNumberNegOneR deningerQ8RootNumberNegOneTopX := by rfl
  have hr : deningerQ8RootNumberNegOneR deningerQ8RootNumberNegOneTopX ≠ 0 := by
    simpa [hR] using deningerQ8RootNumberNegOne_topRInField_ne_zero
  field_simp [q8TopX_ne_zero, q8TopY_ne_zero, hr, q8TopRoot_ne_zero]
  ring

theorem q8C_rat (q : ℚ) : q8C (q : K3) = q := by
  change q8C (algebraMap ℚ K3 q) = algebraMap ℚ K3 q
  exact q8C.map_rat_algebraMap q

theorem q8C_topX :
    q8C deningerQ8RootNumberNegOneTopX = deningerQ8RootNumberNegOneTopX := by
  unfold deningerQ8RootNumberNegOneTopX
  rw [q8C_of]

theorem q8C_topY :
    q8C deningerQ8RootNumberNegOneTopY = deningerQ8RootNumberNegOneTopY := by
  unfold deningerQ8RootNumberNegOneTopY
  rw [q8C_of]

theorem q8C_JThenI :
    q8C (deningerQ8RootNumberNegOneJThenI
      deningerQ8RootNumberNegOneTopX deningerQ8RootNumberNegOneTopY
        deningerQ8RootNumberNegOneTopRoot) =
      -deningerQ8RootNumberNegOneJThenI
        deningerQ8RootNumberNegOneTopX deningerQ8RootNumberNegOneTopY
          deningerQ8RootNumberNegOneTopRoot := by
  unfold deningerQ8RootNumberNegOneJThenI
    deningerQ8RootNumberNegOneSConj deningerQ8RootNumberNegOneR
  simp only [map_div₀, map_mul, map_add, map_sub, q8C_topY, q8C_root,
    q8C_topX]
  have h2 : q8C (2 : K3) = 2 := by
    change q8C ((2 : ℚ) : K3) = (2 : K3)
    exact q8C_rat 2
  have h5 : q8C (5 : K3) = 5 := by
    change q8C ((5 : ℚ) : K3) = (5 : K3)
    exact q8C_rat 5
  have h6 : q8C (6 : K3) = 6 := by
    change q8C ((6 : ℚ) : K3) = (6 : K3)
    exact q8C_rat 6
  have h41 : q8C (41 : K3) = 41 := by
    change q8C ((41 : ℚ) : K3) = (41 : K3)
    exact q8C_rat 41
  rw [h2, h5, h6, h41]
  ring

/-- The literal lifts satisfy the quaternion anti-commutation relation. -/
theorem q8I_comp_q8J_eq_q8C_comp_q8J_comp_q8I :
    q8I.comp q8J = q8C.comp (q8J.comp q8I) := by
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  apply q8End_eq_of_topRoot
  change q8I (q8J deningerQ8RootNumberNegOneTopRoot) =
    q8C (q8J (q8I deningerQ8RootNumberNegOneTopRoot))
  rw [q8J_root, q8I_JCandidate, q8I_root, q8J_ICandidate, q8C_JThenI]
  exact deningerQ8RootNumberNegOne_lifted_composites_anticommute
    deningerQ8RootNumberNegOne_topX_sq
    deningerQ8RootNumberNegOne_topY_sq q8TopRoot_radical_relation

end

end RHTower
