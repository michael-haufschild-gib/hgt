import GaloisForLFunctions.RHTower.SerreQ8RootNumberNegOnePolynomial
import GaloisForLFunctions.RHTower.DeningerQ8RootNumberNegOneAutomorphisms

/-!
# Explicit quaternionic automorphisms of Serre's actual field

For the source-authenticated Serre radical field, the two base flips lift to

`I(z) = 12 * sqrt(5) * sqrt(41) / z`,
`J(z) = 6 * sqrt(41) * (5 + sqrt(5)) / z`.

Their squares are the central sign change and their literal anti-commutation
relation is proved in this leaf.  The construction preserves the exact
published radical and has no root-number assumption.  It is the algebraic
input required before a real global Artin epsilon-factor calculation can even
be stated faithfully in Lean.
-/

open Polynomial

namespace RHTower

noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => SerreQ8TopField

def serreQ8TopX : K3 :=
  (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2)

def serreQ8TopY : K3 := deningerQ8RootNumberNegOneSecondQuadraticRoot

def serreQ8IBase : K2 →+* K3 :=
  (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial).comp q8FirstConjugationSecond

def serreQ8JBase : K2 →+* K3 :=
  (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial).comp
    deningerQ8RootNumberNegOneSecondConjugation

theorem serreQ8IBase_topX : serreQ8IBase
    (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2) = -serreQ8TopX := by
  unfold serreQ8IBase serreQ8TopX
  change AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
    (q8FirstConjugationSecond
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
        deningerQ8RootNumberNegOneFirstQuadraticRoot)) = _
  rw [q8FirstConjugationSecond_of]
  change AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
    (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
      (q8FirstConjugation deningerQ8RootNumberNegOneFirstQuadraticRoot)) = _
  rw [q8FirstConjugation_root, map_neg, map_neg]

theorem serreQ8IBase_topY :
    serreQ8IBase deningerQ8RootNumberNegOneSecondQuadraticRoot = serreQ8TopY := by
  unfold serreQ8IBase serreQ8TopY
  change AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
    (q8FirstConjugationSecond deningerQ8RootNumberNegOneSecondQuadraticRoot) = _
  rw [q8FirstConjugationSecond_root]

theorem serreQ8JBase_topX : serreQ8JBase
    (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2) = serreQ8TopX := by
  unfold serreQ8JBase serreQ8TopX
  change AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
    (deningerQ8RootNumberNegOneSecondConjugation
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
        deningerQ8RootNumberNegOneFirstQuadraticRoot)) = _
  rw [deningerQ8RootNumberNegOne_secondConjugation_of]

theorem serreQ8JBase_topY :
    serreQ8JBase deningerQ8RootNumberNegOneSecondQuadraticRoot = -serreQ8TopY := by
  unfold serreQ8JBase serreQ8TopY
  change AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
    (deningerQ8RootNumberNegOneSecondConjugation
      deningerQ8RootNumberNegOneSecondQuadraticRoot) = _
  rw [deningerQ8RootNumberNegOne_secondConjugation_root, map_neg]

theorem serreQ8IBase_rat (q : ℚ) : serreQ8IBase (q : K2) = q := by
  change serreQ8IBase (algebraMap ℚ K2 q) = algebraMap ℚ K3 q
  exact serreQ8IBase.map_rat_algebraMap q

theorem serreQ8JBase_rat (q : ℚ) : serreQ8JBase (q : K2) = q := by
  change serreQ8JBase (algebraMap ℚ K2 q) = algebraMap ℚ K3 q
  exact serreQ8JBase.map_rat_algebraMap q

theorem serreQ8IBase_topR : serreQ8IBase (serreQ8TopR : K2) = 5 - serreQ8TopX := by
  unfold serreQ8TopR
  rw [map_add]
  change serreQ8IBase (5 + (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2)) = _
  rw [map_add, serreQ8IBase_topX]
  change serreQ8IBase ((5 : ℚ) : K2) - serreQ8TopX = _
  rw [serreQ8IBase_rat]
  norm_num

theorem serreQ8IBase_topS : serreQ8IBase serreQ8TopS =
    41 - serreQ8TopX * serreQ8TopY := by
  unfold serreQ8TopS
  change serreQ8IBase ((41 : K2) +
    (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2) *
      deningerQ8RootNumberNegOneSecondQuadraticRoot) = _
  rw [map_add, map_mul, serreQ8IBase_topX, serreQ8IBase_topY]
  change serreQ8IBase ((41 : ℚ) : K2) +
    (-serreQ8TopX) * serreQ8TopY = _
  rw [serreQ8IBase_rat]
  ring

theorem serreQ8JBase_topR : serreQ8JBase (serreQ8TopR : K2) = 5 + serreQ8TopX := by
  unfold serreQ8TopR
  rw [map_add]
  change serreQ8JBase (5 + (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2)) = _
  rw [map_add, serreQ8JBase_topX]
  change serreQ8JBase ((5 : ℚ) : K2) + serreQ8TopX = _
  rw [serreQ8JBase_rat]
  norm_num

theorem serreQ8JBase_topS : serreQ8JBase serreQ8TopS =
    41 - serreQ8TopX * serreQ8TopY := by
  unfold serreQ8TopS
  change serreQ8JBase ((41 : K2) +
    (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2) *
      deningerQ8RootNumberNegOneSecondQuadraticRoot) = _
  rw [map_add, map_mul, serreQ8JBase_topX, serreQ8JBase_topY]
  change serreQ8JBase ((41 : ℚ) : K2) +
    serreQ8TopX * (-serreQ8TopY) = _
  rw [serreQ8JBase_rat]
  ring

theorem serreQ8IBase_topRadicand : serreQ8IBase serreQ8TopRadicand =
    (5 - serreQ8TopX) * (41 - serreQ8TopX * serreQ8TopY) := by
  unfold serreQ8TopRadicand
  rw [map_mul, serreQ8IBase_topR, serreQ8IBase_topS]

theorem serreQ8JBase_topRadicand : serreQ8JBase serreQ8TopRadicand =
    (5 + serreQ8TopX) * (41 - serreQ8TopX * serreQ8TopY) := by
  unfold serreQ8TopRadicand
  rw [map_mul, serreQ8JBase_topR, serreQ8JBase_topS]

theorem serreQ8TopX_sq : serreQ8TopX ^ (2 : ℕ) = 5 := by
  unfold serreQ8TopX
  rw [← map_pow]
  change AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
    ((AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
      deningerQ8RootNumberNegOneFirstQuadraticRoot) ^ (2 : ℕ)) = 5
  rw [← map_pow]
  rw [deningerQ8RootNumberNegOneFirstQuadraticRoot_sq]
  rw [show AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
    (5 : K1) = (5 : K2) by
    exact (map_natCast
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial) 5).symm]
  exact (map_natCast (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial) 5).symm

theorem serreQ8TopY_sq : serreQ8TopY ^ (2 : ℕ) = 41 := by
  unfold serreQ8TopY
  rw [← map_pow, deningerQ8RootNumberNegOneSecondQuadraticRoot_sq]
  exact (map_natCast (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial) 41).symm

theorem serreQ8TopRoot_relation :
    serreQ8TopRoot ^ (2 : ℕ) = (5 + serreQ8TopX) * (41 + serreQ8TopX * serreQ8TopY) := by
  rw [serreQ8TopRoot_sq]
  change AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
    ((serreQ8TopR : K2) * serreQ8TopS) = _
  unfold serreQ8TopR serreQ8TopS serreQ8TopX serreQ8TopY
  simp only [map_mul, map_add]
  have h5 : AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial (5 : K1)) =
        (5 : K3) := by
    rw [show AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
      (5 : K1) = (5 : K2) by
      exact (map_natCast
        (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial) 5).symm]
    exact (map_natCast (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial) 5).symm
  have h41 : AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial (41 : K1)) =
        (41 : K3) := by
    rw [show AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
      (41 : K1) = (41 : K2) by
      exact (map_natCast
        (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial) 41).symm]
    exact (map_natCast (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial) 41).symm
  rw [h5, h41]

def serreQ8ITopCandidate : K3 := 12 * serreQ8TopX * serreQ8TopY / serreQ8TopRoot
def serreQ8JTopCandidate : K3 := 6 * serreQ8TopY * (5 + serreQ8TopX) / serreQ8TopRoot

def serreQ8TopRInField : K3 := 5 + serreQ8TopX
def serreQ8TopSInField : K3 := 41 + serreQ8TopX * serreQ8TopY
def serreQ8TopSConjInField : K3 := 41 - serreQ8TopX * serreQ8TopY

theorem serreQ8TopRInField_ne_zero : serreQ8TopRInField ≠ 0 := by
  intro h
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  have hx : serreQ8TopX = -5 := by
    dsimp [serreQ8TopRInField] at h
    linear_combination h
  have hs := serreQ8TopX_sq
  rw [hx] at hs
  norm_num at hs

theorem serreQ8_topSInField_mul_conj :
    serreQ8TopSInField * serreQ8TopSConjInField = 1476 := by
  unfold serreQ8TopSInField serreQ8TopSConjInField
  calc
    (41 + serreQ8TopX * serreQ8TopY) * (41 - serreQ8TopX * serreQ8TopY) =
        41 ^ (2 : ℕ) - serreQ8TopX ^ (2 : ℕ) * serreQ8TopY ^ (2 : ℕ) := by ring
    _ = 1476 := by rw [serreQ8TopX_sq, serreQ8TopY_sq]; norm_num

theorem serreQ8TopSInField_ne_zero : serreQ8TopSInField ≠ 0 := by
  intro h
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  have hs := serreQ8_topSInField_mul_conj
  rw [h] at hs
  norm_num at hs

theorem serreQ8TopRoot_ne_zero : serreQ8TopRoot ≠ 0 := by
  intro h
  have hz := serreQ8TopRoot_relation
  rw [h] at hz
  rw [← show serreQ8TopRInField = 5 + serreQ8TopX by rfl,
    ← show serreQ8TopSInField = 41 + serreQ8TopX * serreQ8TopY by rfl] at hz
  have hzero : serreQ8TopRInField * serreQ8TopSInField = 0 := by
    simpa using hz
  rcases mul_eq_zero.mp hzero with hr | hs
  · exact serreQ8TopRInField_ne_zero hr
  · exact serreQ8TopSInField_ne_zero hs

theorem serreQ8_iCandidate_sq :
    serreQ8ITopCandidate ^ (2 : ℕ) =
      (5 - serreQ8TopX) * (41 - serreQ8TopX * serreQ8TopY) := by
  unfold serreQ8ITopCandidate
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  field_simp [serreQ8TopRoot_ne_zero]
  rw [serreQ8TopRoot_relation]
  have hx4 : serreQ8TopX ^ (4 : ℕ) = 25 := by
    calc serreQ8TopX ^ (4 : ℕ) = (serreQ8TopX ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = 25 := by rw [serreQ8TopX_sq]; norm_num
  ring_nf
  simp only [hx4, serreQ8TopX_sq, serreQ8TopY_sq]
  ring

theorem serreQ8_jCandidate_sq :
    serreQ8JTopCandidate ^ (2 : ℕ) =
      (5 + serreQ8TopX) * (41 - serreQ8TopX * serreQ8TopY) := by
  unfold serreQ8JTopCandidate
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  field_simp [serreQ8TopRoot_ne_zero]
  rw [serreQ8TopRoot_relation]
  have hx3 : serreQ8TopX ^ (3 : ℕ) = 5 * serreQ8TopX := by
    calc serreQ8TopX ^ (3 : ℕ) = serreQ8TopX * serreQ8TopX ^ (2 : ℕ) := by ring
      _ = 5 * serreQ8TopX := by rw [serreQ8TopX_sq]; ring
  have hx4 : serreQ8TopX ^ (4 : ℕ) = 25 := by
    calc serreQ8TopX ^ (4 : ℕ) = (serreQ8TopX ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = 25 := by rw [serreQ8TopX_sq]; norm_num
  ring_nf
  simp only [hx4, hx3, serreQ8TopX_sq, serreQ8TopY_sq]
  ring

def serreQ8I : K3 →+* K3 :=
  AdjoinRoot.lift serreQ8IBase serreQ8ITopCandidate (by
    change (X ^ (2 : ℕ) - C serreQ8TopRadicand).eval₂ serreQ8IBase serreQ8ITopCandidate = 0
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    change serreQ8ITopCandidate ^ (2 : ℕ) - serreQ8IBase serreQ8TopRadicand = 0
    rw [serreQ8_iCandidate_sq, serreQ8IBase_topRadicand]
    ring)

def serreQ8J : K3 →+* K3 :=
  AdjoinRoot.lift serreQ8JBase serreQ8JTopCandidate (by
    change (X ^ (2 : ℕ) - C serreQ8TopRadicand).eval₂ serreQ8JBase serreQ8JTopCandidate = 0
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    change serreQ8JTopCandidate ^ (2 : ℕ) - serreQ8JBase serreQ8TopRadicand = 0
    rw [serreQ8_jCandidate_sq, serreQ8JBase_topRadicand]
    ring)

theorem serreQ8I_root : serreQ8I serreQ8TopRoot = serreQ8ITopCandidate := by
  unfold serreQ8I
  exact AdjoinRoot.lift_root _

theorem serreQ8J_root : serreQ8J serreQ8TopRoot = serreQ8JTopCandidate := by
  unfold serreQ8J
  exact AdjoinRoot.lift_root _

theorem serreQ8I_of (a : K2) :
    serreQ8I (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial a) = serreQ8IBase a := by
  unfold serreQ8I
  exact AdjoinRoot.lift_of _

theorem serreQ8J_of (a : K2) :
    serreQ8J (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial a) = serreQ8JBase a := by
  unfold serreQ8J
  exact AdjoinRoot.lift_of _

theorem serreQ8I_topX : serreQ8I serreQ8TopX = -serreQ8TopX := by
  unfold serreQ8TopX
  rw [serreQ8I_of]
  exact serreQ8IBase_topX

theorem serreQ8I_topY : serreQ8I serreQ8TopY = serreQ8TopY := by
  unfold serreQ8TopY
  rw [serreQ8I_of]
  exact serreQ8IBase_topY

theorem serreQ8J_topX : serreQ8J serreQ8TopX = serreQ8TopX := by
  unfold serreQ8TopX
  rw [serreQ8J_of]
  exact serreQ8JBase_topX

theorem serreQ8J_topY : serreQ8J serreQ8TopY = -serreQ8TopY := by
  unfold serreQ8TopY
  rw [serreQ8J_of]
  exact serreQ8JBase_topY

theorem serreQ8I_rat (q : ℚ) : serreQ8I (q : K3) = q := by
  change serreQ8I (algebraMap ℚ K3 q) = algebraMap ℚ K3 q
  exact serreQ8I.map_rat_algebraMap q

theorem serreQ8J_rat (q : ℚ) : serreQ8J (q : K3) = q := by
  change serreQ8J (algebraMap ℚ K3 q) = algebraMap ℚ K3 q
  exact serreQ8J.map_rat_algebraMap q

theorem serreQ8TopX_ne_zero : serreQ8TopX ≠ 0 := by
  intro h
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  have hs := serreQ8TopX_sq
  rw [h] at hs
  norm_num at hs

theorem serreQ8TopY_ne_zero : serreQ8TopY ≠ 0 := by
  intro h
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  have hs := serreQ8TopY_sq
  rw [h] at hs
  norm_num at hs

theorem serreQ8I_candidate : serreQ8I serreQ8ITopCandidate = -serreQ8TopRoot := by
  unfold serreQ8ITopCandidate
  rw [map_div₀, map_mul, map_mul, serreQ8I_topX, serreQ8I_topY, serreQ8I_root]
  change serreQ8I ((12 : ℚ) : K3) * (-serreQ8TopX) * serreQ8TopY /
      serreQ8ITopCandidate = _
  rw [serreQ8I_rat]
  unfold serreQ8ITopCandidate
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  field_simp [serreQ8TopX_ne_zero, serreQ8TopY_ne_zero, serreQ8TopRoot_ne_zero]
  ring

theorem serreQ8J_candidate : serreQ8J serreQ8JTopCandidate = -serreQ8TopRoot := by
  unfold serreQ8JTopCandidate
  rw [map_div₀, map_mul, map_mul, map_add, serreQ8J_topY, serreQ8J_topX,
    serreQ8J_root]
  change serreQ8J ((6 : ℚ) : K3) * (-serreQ8TopY) *
      (serreQ8J ((5 : ℚ) : K3) + serreQ8TopX) / serreQ8JTopCandidate = _
  rw [serreQ8J_rat, serreQ8J_rat]
  unfold serreQ8JTopCandidate
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  have hr : (5 + serreQ8TopX : K3) ≠ 0 := by
    simpa [serreQ8TopRInField] using serreQ8TopRInField_ne_zero
  field_simp [serreQ8TopY_ne_zero, hr, serreQ8TopRoot_ne_zero]
  ring

theorem serreQ8End_eq_of_base_root (f g : K3 →+* K3)
    (hbase : f.comp (algebraMap K2 K3) = g.comp (algebraMap K2 K3))
    (hroot : f serreQ8TopRoot = g serreQ8TopRoot) : f = g := by
  apply RingHom.ext
  intro w
  refine AdjoinRoot.induction_on serreQ8ThirdQuadraticPolynomial w ?_
  intro p
  rw [← AdjoinRoot.aeval_eq p]
  simp only [Polynomial.aeval_def, Polynomial.hom_eval₂, hbase]
  change Polynomial.eval₂ (g.comp (algebraMap K2 K3))
    (f serreQ8TopRoot) p =
      Polynomial.eval₂ (g.comp (algebraMap K2 K3)) (g serreQ8TopRoot) p
  rw [hroot]

def serreQ8C : K3 →+* K3 :=
  AdjoinRoot.lift (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial) (-serreQ8TopRoot) (by
    change (X ^ (2 : ℕ) - C serreQ8TopRadicand).eval₂
      (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial) (-serreQ8TopRoot) = 0
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, neg_sq, serreQ8TopRoot_sq]
    ring)

theorem serreQ8C_root : serreQ8C serreQ8TopRoot = -serreQ8TopRoot := by
  unfold serreQ8C
  exact AdjoinRoot.lift_root _

theorem serreQ8C_of (a : K2) :
    serreQ8C (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial a) =
      AdjoinRoot.of serreQ8ThirdQuadraticPolynomial a := by
  unfold serreQ8C
  exact AdjoinRoot.lift_of _

theorem serreQ8I_sq_of (a : K2) :
    serreQ8I (serreQ8I (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial a)) =
      AdjoinRoot.of serreQ8ThirdQuadraticPolynomial a := by
  rw [serreQ8I_of]
  change serreQ8I (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
    (q8FirstConjugationSecond a)) = _
  rw [serreQ8I_of]
  change AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
    (q8FirstConjugationSecond (q8FirstConjugationSecond a)) = _
  rw [q8FirstConjugationSecond_involutive]

theorem serreQ8J_sq_of (a : K2) :
    serreQ8J (serreQ8J (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial a)) =
      AdjoinRoot.of serreQ8ThirdQuadraticPolynomial a := by
  rw [serreQ8J_of]
  change serreQ8J (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
    (deningerQ8RootNumberNegOneSecondConjugation a)) = _
  rw [serreQ8J_of]
  change AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
    (deningerQ8RootNumberNegOneSecondConjugation
      (deningerQ8RootNumberNegOneSecondConjugation a)) = _
  rw [deningerQ8RootNumberNegOne_secondConjugation_involutive]

theorem serreQ8I_sq_eq_C : serreQ8I.comp serreQ8I = serreQ8C := by
  apply serreQ8End_eq_of_base_root
  · apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply]
    rw [AdjoinRoot.algebraMap_eq]
    rw [serreQ8I_sq_of, serreQ8C_of]
  · rw [RingHom.comp_apply, serreQ8I_root, serreQ8I_candidate, serreQ8C_root]

theorem serreQ8J_sq_eq_C : serreQ8J.comp serreQ8J = serreQ8C := by
  apply serreQ8End_eq_of_base_root
  · apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply]
    rw [AdjoinRoot.algebraMap_eq]
    rw [serreQ8J_sq_of, serreQ8C_of]
  · rw [RingHom.comp_apply, serreQ8J_root, serreQ8J_candidate, serreQ8C_root]

theorem serreQ8C_sq_eq_id : serreQ8C.comp serreQ8C = RingHom.id K3 := by
  apply serreQ8End_eq_of_base_root
  · apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply]
    rw [AdjoinRoot.algebraMap_eq, serreQ8C_of, serreQ8C_of]
    rfl
  · rw [RingHom.comp_apply, serreQ8C_root, map_neg, serreQ8C_root]
    simp

theorem serreQ8_base_flips_commute (a : K2) :
    q8FirstConjugationSecond (deningerQ8RootNumberNegOneSecondConjugation a) =
      deningerQ8RootNumberNegOneSecondConjugation (q8FirstConjugationSecond a) := by
  obtain ⟨u, v, huv⟩ := deningerQ8RootNumberNegOneSecondQuadratic_normal_form a
  rw [huv, deningerQ8RootNumberNegOne_secondConjugation_normal]
  rw [sub_eq_add_neg, ← neg_mul, ← map_neg]
  change q8FirstConjugationSecond
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial u +
        AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial (-v) *
          deningerQ8RootNumberNegOneSecondQuadraticRoot) =
    deningerQ8RootNumberNegOneSecondConjugation
      (q8FirstConjugationSecond
        (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial u +
          AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial v *
            deningerQ8RootNumberNegOneSecondQuadraticRoot))
  rw [q8FirstConjugationSecond_normal, q8FirstConjugationSecond_normal]
  change q8FirstConjugationToSecond u + q8FirstConjugationToSecond (-v) *
      deningerQ8RootNumberNegOneSecondQuadraticRoot =
    deningerQ8RootNumberNegOneSecondConjugation
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
        (q8FirstConjugation u) +
        AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
          (q8FirstConjugation v) * deningerQ8RootNumberNegOneSecondQuadraticRoot)
  rw [deningerQ8RootNumberNegOne_secondConjugation_normal]
  unfold q8FirstConjugationToSecond
  simp only [RingHom.comp_apply]
  rw [map_neg]
  rw [map_neg]
  ring

theorem serreQ8C_topX : serreQ8C serreQ8TopX = serreQ8TopX := by
  unfold serreQ8TopX at *
  rw [serreQ8C_of]

theorem serreQ8C_topY : serreQ8C serreQ8TopY = serreQ8TopY := by
  unfold serreQ8TopY at *
  rw [serreQ8C_of]

theorem serreQ8C_rat (q : ℚ) : serreQ8C (q : K3) = q := by
  change serreQ8C (algebraMap ℚ K3 q) = algebraMap ℚ K3 q
  exact serreQ8C.map_rat_algebraMap q

theorem serreQ8C_iCandidate : serreQ8C serreQ8ITopCandidate = -serreQ8ITopCandidate := by
  unfold serreQ8ITopCandidate
  rw [map_div₀, map_mul, map_mul, serreQ8C_topX, serreQ8C_topY, serreQ8C_root]
  change serreQ8C ((12 : ℚ) : K3) * serreQ8TopX * serreQ8TopY / (-serreQ8TopRoot) = _
  rw [serreQ8C_rat]
  ring

theorem serreQ8C_jCandidate : serreQ8C serreQ8JTopCandidate = -serreQ8JTopCandidate := by
  unfold serreQ8JTopCandidate
  rw [map_div₀, map_mul, map_mul, map_add, serreQ8C_topY, serreQ8C_topX, serreQ8C_root]
  change serreQ8C ((6 : ℚ) : K3) * serreQ8TopY *
    (serreQ8C ((5 : ℚ) : K3) + serreQ8TopX) / (-serreQ8TopRoot) = _
  rw [serreQ8C_rat, serreQ8C_rat]
  ring

theorem serreQ8I_jCandidate :
    serreQ8I serreQ8JTopCandidate =
      6 * serreQ8TopY * (5 - serreQ8TopX) / serreQ8ITopCandidate := by
  unfold serreQ8JTopCandidate
  rw [map_div₀, map_mul, map_mul, map_add, serreQ8I_topY, serreQ8I_topX,
    serreQ8I_root]
  change serreQ8I ((6 : ℚ) : K3) * serreQ8TopY *
    (serreQ8I ((5 : ℚ) : K3) - serreQ8TopX) / serreQ8ITopCandidate = _
  rw [serreQ8I_rat, serreQ8I_rat]
  norm_num

theorem serreQ8J_iCandidate :
    serreQ8J serreQ8ITopCandidate =
      -12 * serreQ8TopX * serreQ8TopY / serreQ8JTopCandidate := by
  unfold serreQ8ITopCandidate
  rw [map_div₀, map_mul, map_mul, serreQ8J_topX, serreQ8J_topY, serreQ8J_root]
  change serreQ8J ((12 : ℚ) : K3) * serreQ8TopX * (-serreQ8TopY) /
    serreQ8JTopCandidate = _
  rw [serreQ8J_rat]
  ring

theorem serreQ8_composite_root_relation :
    serreQ8I (serreQ8J serreQ8TopRoot) =
      serreQ8C (serreQ8J (serreQ8I serreQ8TopRoot)) := by
  rw [serreQ8J_root, serreQ8I_jCandidate, serreQ8I_root, serreQ8J_iCandidate,
    map_div₀, map_mul, map_mul, serreQ8C_topX, serreQ8C_topY,
    serreQ8C_jCandidate]
  have hnegTwelve : serreQ8C (-12 : K3) = -12 := by
    rw [show (-12 : K3) = -((12 : ℚ) : K3) by norm_num]
    rw [map_neg, serreQ8C_rat]
  rw [hnegTwelve]
  have hsign : (-12 : K3) * serreQ8TopX * serreQ8TopY / -serreQ8JTopCandidate =
      12 * serreQ8TopX * serreQ8TopY / serreQ8JTopCandidate := by
    rw [show (-12 : K3) * serreQ8TopX * serreQ8TopY =
      -(12 * serreQ8TopX * serreQ8TopY) by ring, neg_div_neg_eq]
  rw [hsign]
  change 6 * serreQ8TopY * (5 - serreQ8TopX) / serreQ8ITopCandidate =
    12 * serreQ8TopX * serreQ8TopY / serreQ8JTopCandidate
  unfold serreQ8ITopCandidate serreQ8JTopCandidate
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  have hR : (5 + serreQ8TopX : K3) ≠ 0 := by
    simpa [serreQ8TopRInField] using serreQ8TopRInField_ne_zero
  field_simp [serreQ8TopX_ne_zero, serreQ8TopY_ne_zero, serreQ8TopRInField_ne_zero,
    serreQ8TopRoot_ne_zero, hR]
  calc
    6 ^ (2 : ℕ) * (5 - serreQ8TopX) * (5 + serreQ8TopX) =
        36 * (25 - serreQ8TopX ^ (2 : ℕ)) := by ring
    _ = serreQ8TopX ^ (2 : ℕ) * 12 ^ (2 : ℕ) := by
      rw [serreQ8TopX_sq]
      norm_num

theorem serreQ8I_comp_J_eq_C_comp_J_comp_I :
    serreQ8I.comp serreQ8J = serreQ8C.comp (serreQ8J.comp serreQ8I) := by
  apply serreQ8End_eq_of_base_root
  · apply RingHom.ext
    intro a
    change serreQ8I (serreQ8J (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial a)) =
      serreQ8C (serreQ8J (serreQ8I
        (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial a)))
    rw [serreQ8J_of]
    change serreQ8I (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
      (deningerQ8RootNumberNegOneSecondConjugation a)) = _
    rw [serreQ8I_of]
    change AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
      (q8FirstConjugationSecond (deningerQ8RootNumberNegOneSecondConjugation a)) = _
    rw [serreQ8I_of]
    change AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
      (q8FirstConjugationSecond (deningerQ8RootNumberNegOneSecondConjugation a)) =
        serreQ8C (serreQ8J (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
          (q8FirstConjugationSecond a)))
    rw [serreQ8J_of]
    change AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
      (q8FirstConjugationSecond (deningerQ8RootNumberNegOneSecondConjugation a)) =
        serreQ8C (AdjoinRoot.of serreQ8ThirdQuadraticPolynomial
          (deningerQ8RootNumberNegOneSecondConjugation (q8FirstConjugationSecond a)))
    rw [serreQ8C_of, serreQ8_base_flips_commute]
  · exact serreQ8_composite_root_relation

end

end RHTower
