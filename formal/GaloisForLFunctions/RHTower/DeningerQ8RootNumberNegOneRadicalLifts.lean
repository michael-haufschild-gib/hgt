import GaloisForLFunctions.RHTower.DeningerQ8RootNumberNegOneRadicalCertificate

/-!
# Radical-coordinate lifts for the root-number-minus-one Q8 witness

For the literal radical used in the documented root-number-minus-one witness,
this module proves the algebra needed to lift the two quadratic conjugations
through the top radical.  The two lifted coordinates square to the conjugate
radicands and their two composites are negatives of one another.  This is the
coordinate-level quaternion relation needed by the eventual `AdjoinRoot`
construction.

It does not construct field automorphisms, prove that the resulting extension
is normal, identify its Galois group, or formalize its epsilon factor.  Those
are separate arithmetic gates.
-/

namespace RHTower

noncomputable section

def deningerQ8RootNumberNegOneR {R : Type*} [Field R] (x : R) : R := 5 + x
def deningerQ8RootNumberNegOneS {R : Type*} [Field R] (y : R) : R := 41 + 6 * y
def deningerQ8RootNumberNegOneRConj {R : Type*} [Field R] (x : R) : R := 5 - x
def deningerQ8RootNumberNegOneSConj {R : Type*} [Field R] (y : R) : R := 41 - 6 * y

/-- Candidate lift of the `√5` conjugation through the top radical. -/
def deningerQ8RootNumberNegOneILift {R : Type*} [Field R] (x y z : R) : R :=
  2 * x * deningerQ8RootNumberNegOneS y / z

/-- Candidate lift of the `√41` conjugation through the top radical. -/
def deningerQ8RootNumberNegOneJLift {R : Type*} [Field R] (x y z : R) : R :=
  x * y * deningerQ8RootNumberNegOneR x / z

def deningerQ8RootNumberNegOneIThenJ {R : Type*} [Field R] (x y z : R) : R :=
  -(y * deningerQ8RootNumberNegOneRConj x * z) /
    (2 * deningerQ8RootNumberNegOneS y)

def deningerQ8RootNumberNegOneJThenI {R : Type*} [Field R] (x y z : R) : R :=
  2 * deningerQ8RootNumberNegOneSConj y * z /
    (y * deningerQ8RootNumberNegOneR x)

theorem deningerQ8RootNumberNegOne_r_ne_zero
    {R : Type*} [Field R] [CharZero R] {x : R}
    (hx : x ^ (2 : ℕ) = 5) : deningerQ8RootNumberNegOneR x ≠ 0 := by
  intro hr
  have hxv : x = -5 := by
    dsimp [deningerQ8RootNumberNegOneR] at hr
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hr)
  rw [hxv] at hx
  norm_num at hx

theorem deningerQ8RootNumberNegOne_s_ne_zero
    {R : Type*} [Field R] [CharZero R] {y : R}
    (hy : y ^ (2 : ℕ) = 41) : deningerQ8RootNumberNegOneS y ≠ 0 := by
  intro hs
  have hrel : 6 * y = -41 := by
    dsimp [deningerQ8RootNumberNegOneS] at hs
    linear_combination hs
  have hsq : (6 * y) ^ (2 : ℕ) = (-41 : R) ^ (2 : ℕ) := by rw [hrel]
  rw [mul_pow, hy] at hsq
  norm_num at hsq

theorem deningerQ8RootNumberNegOne_z_ne_zero
    {R : Type*} [Field R] [CharZero R] {x y z : R}
    (hx : x ^ (2 : ℕ) = 5) (hy : y ^ (2 : ℕ) = 41)
    (hz : z ^ (2 : ℕ) = deningerQ8RootNumberNegOneR x * deningerQ8RootNumberNegOneS y) :
    z ≠ 0 := by
  intro hz0
  rw [hz0] at hz
  have hprod : deningerQ8RootNumberNegOneR x * deningerQ8RootNumberNegOneS y = 0 := by
    simpa using hz.symm
  rcases mul_eq_zero.mp hprod with hr | hs
  · exact deningerQ8RootNumberNegOne_r_ne_zero hx hr
  · exact deningerQ8RootNumberNegOne_s_ne_zero hy hs

theorem deningerQ8RootNumberNegOne_y_ne_zero
    {R : Type*} [Field R] [CharZero R] {y : R}
    (hy : y ^ (2 : ℕ) = 41) : y ≠ 0 := by
  intro hy0
  rw [hy0] at hy
  norm_num at hy

theorem deningerQ8RootNumberNegOne_r_mul_rConj
    {R : Type*} [Field R] [CharZero R] {x : R}
    (hx : x ^ (2 : ℕ) = 5) :
    deningerQ8RootNumberNegOneR x * deningerQ8RootNumberNegOneRConj x = 20 := by
  dsimp [deningerQ8RootNumberNegOneR, deningerQ8RootNumberNegOneRConj]
  calc
    (5 + x) * (5 - x) = 25 - x ^ (2 : ℕ) := by ring
    _ = 20 := by rw [hx]; norm_num

theorem deningerQ8RootNumberNegOne_s_mul_sConj
    {R : Type*} [Field R] [CharZero R] {y : R}
    (hy : y ^ (2 : ℕ) = 41) :
    deningerQ8RootNumberNegOneS y * deningerQ8RootNumberNegOneSConj y = 205 := by
  dsimp [deningerQ8RootNumberNegOneS, deningerQ8RootNumberNegOneSConj]
  calc
    (41 + 6 * y) * (41 - 6 * y) = 1681 - 36 * y ^ (2 : ℕ) := by ring
    _ = 205 := by rw [hy]; norm_num

/-- The lifted `√5` conjugation lands on its exact conjugate radicand. -/
theorem deningerQ8RootNumberNegOne_iLift_sq
    {R : Type*} [Field R] [CharZero R] {x y z : R}
    (hx : x ^ (2 : ℕ) = 5) (hy : y ^ (2 : ℕ) = 41)
    (hz : z ^ (2 : ℕ) = deningerQ8RootNumberNegOneR x * deningerQ8RootNumberNegOneS y) :
    (deningerQ8RootNumberNegOneILift x y z) ^ (2 : ℕ) =
      deningerQ8RootNumberNegOneRConj x * deningerQ8RootNumberNegOneS y := by
  have hz0 := deningerQ8RootNumberNegOne_z_ne_zero hx hy hz
  unfold deningerQ8RootNumberNegOneILift
  dsimp [deningerQ8RootNumberNegOneR, deningerQ8RootNumberNegOneS,
    deningerQ8RootNumberNegOneRConj] at hz ⊢
  rw [div_pow, hz]
  rw [show (2 * x * (41 + 6 * y)) ^ (2 : ℕ) =
    4 * x ^ (2 : ℕ) * (41 + 6 * y) ^ (2 : ℕ) by ring, hx]
  have hr : (5 + x) ≠ 0 := deningerQ8RootNumberNegOne_r_ne_zero hx
  have hs : (41 + 6 * y) ≠ 0 := deningerQ8RootNumberNegOne_s_ne_zero hy
  have hcancel :
      (20 * (41 + 6 * y) ^ (2 : ℕ)) / ((5 + x) * (41 + 6 * y)) =
        (20 * (41 + 6 * y)) / (5 + x) := by
    field_simp [hr, hs]
  have hfourfive : (4 : R) * 5 = 20 := by norm_num
  rw [hfourfive]
  rw [hcancel]
  apply (div_eq_iff hr).2
  have hrr : (5 - x) * (5 + x) = 20 := by
    calc
      (5 - x) * (5 + x) = 25 - x ^ (2 : ℕ) := by ring
      _ = 20 := by rw [hx]; norm_num
  calc
    20 * (41 + 6 * y) = ((5 - x) * (5 + x)) * (41 + 6 * y) := by rw [hrr]
    _ = (5 - x) * (41 + 6 * y) * (5 + x) := by ring

/-- The lifted `√41` conjugation lands on its exact conjugate radicand. -/
theorem deningerQ8RootNumberNegOne_jLift_sq
    {R : Type*} [Field R] [CharZero R] {x y z : R}
    (hx : x ^ (2 : ℕ) = 5) (hy : y ^ (2 : ℕ) = 41)
    (hz : z ^ (2 : ℕ) = deningerQ8RootNumberNegOneR x * deningerQ8RootNumberNegOneS y) :
    (deningerQ8RootNumberNegOneJLift x y z) ^ (2 : ℕ) =
      deningerQ8RootNumberNegOneR x * deningerQ8RootNumberNegOneSConj y := by
  have hr : (5 + x) ≠ 0 := deningerQ8RootNumberNegOne_r_ne_zero hx
  have hs : (41 + 6 * y) ≠ 0 := deningerQ8RootNumberNegOne_s_ne_zero hy
  unfold deningerQ8RootNumberNegOneJLift
  dsimp [deningerQ8RootNumberNegOneR, deningerQ8RootNumberNegOneS,
    deningerQ8RootNumberNegOneSConj] at hz ⊢
  rw [div_pow, hz]
  rw [show (x * y * (5 + x)) ^ (2 : ℕ) = x ^ (2 : ℕ) * y ^ (2 : ℕ) * (5 + x) ^ (2 : ℕ) by ring, hx, hy]
  have hcancel :
      (205 * (5 + x) ^ (2 : ℕ)) / ((5 + x) * (41 + 6 * y)) =
        (205 * (5 + x)) / (41 + 6 * y) := by
    field_simp [hr, hs]
  norm_num
  rw [hcancel]
  apply (div_eq_iff hs).2
  have hss : (41 + 6 * y) * (41 - 6 * y) = 205 := by
    exact deningerQ8RootNumberNegOne_s_mul_sConj hy
  calc
    205 * (5 + x) = (5 + x) * ((41 + 6 * y) * (41 - 6 * y)) := by rw [hss]; ring
    _ = (5 + x) * (41 - 6 * y) * (41 + 6 * y) := by ring

/-- The two lifted conjugation composites anti-commute on the top radical. -/
theorem deningerQ8RootNumberNegOne_lifted_composites_anticommute
    {R : Type*} [Field R] [CharZero R] {x y z : R}
    (hx : x ^ (2 : ℕ) = 5) (hy : y ^ (2 : ℕ) = 41)
    (_hz : z ^ (2 : ℕ) = deningerQ8RootNumberNegOneR x * deningerQ8RootNumberNegOneS y) :
    deningerQ8RootNumberNegOneIThenJ x y z =
      -deningerQ8RootNumberNegOneJThenI x y z := by
  have hy0 : y ≠ 0 := deningerQ8RootNumberNegOne_y_ne_zero hy
  have hr : deningerQ8RootNumberNegOneR x ≠ 0 := deningerQ8RootNumberNegOne_r_ne_zero hx
  have hs : deningerQ8RootNumberNegOneS y ≠ 0 := deningerQ8RootNumberNegOne_s_ne_zero hy
  have hrr : deningerQ8RootNumberNegOneR x * deningerQ8RootNumberNegOneRConj x = 20 :=
    deningerQ8RootNumberNegOne_r_mul_rConj hx
  have hss : deningerQ8RootNumberNegOneS y * deningerQ8RootNumberNegOneSConj y = 205 :=
    deningerQ8RootNumberNegOne_s_mul_sConj hy
  unfold deningerQ8RootNumberNegOneIThenJ deningerQ8RootNumberNegOneJThenI
  field_simp [hy0, hr, hs]
  rw [hy]
  have hrr' : deningerQ8RootNumberNegOneRConj x * deningerQ8RootNumberNegOneR x = 20 := by
    rw [mul_comm]
    exact hrr
  calc
    -(41 * deningerQ8RootNumberNegOneRConj x * z * deningerQ8RootNumberNegOneR x) =
        -(z * 41 * (deningerQ8RootNumberNegOneRConj x * deningerQ8RootNumberNegOneR x)) := by
      ring
    _ = -(z * 41 * 20) := by rw [hrr']
    _ = -(z * 4 * 205) := by norm_num; ring
    _ = -(z * 2 ^ (2 : ℕ) *
        (deningerQ8RootNumberNegOneS y * deningerQ8RootNumberNegOneSConj y)) := by
      rw [hss]
      norm_num
    _ = -(z * 2 ^ (2 : ℕ) * deningerQ8RootNumberNegOneS y *
        deningerQ8RootNumberNegOneSConj y) := by ring

end

end RHTower
