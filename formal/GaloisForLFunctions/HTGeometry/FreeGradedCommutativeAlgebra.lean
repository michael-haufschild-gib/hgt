import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

/-!
# Free graded-commutative algebras on generators of mixed degree

The free graded-commutative algebra on a family of generators with assigned degrees is the free
associative algebra modulo the Koszul commutation relations: two generators commute up to the sign
`(-1)^{|x||y|}`, and a generator of odd degree squares to zero.

For generators all of degree one this is the exterior algebra; for generators all of even degree it
is the polynomial algebra.  Mixed degrees are what a Sullivan tower needs, since killing a class in
degree `n + 1` requires a new generator of degree `n`.

* `DeningerFreeGCA` : the algebra, as a quotient of the free associative algebra.
* `deningerGCAι`, `deningerGCA_comm`, `deningerGCA_sq_zero` : the generators and their relations.
* `deningerGCALift`, `deningerGCA_hom_ext` : the universal property.
* `deningerGCA_anticomm_degreeOne`, `deningerGCA_comm_of_even` : the degree-one and even cases.
-/

namespace HTGeometry

section Definition

variable (k G : Type*) [CommRing k]

/-- The Koszul relations defining a free graded-commutative algebra: generators commute up to the
sign of their degrees, and odd generators square to zero. -/
inductive DeningerGCARel (deg : G → ℕ) : FreeAlgebra k G → FreeAlgebra k G → Prop
  | comm (x y : G) :
      DeningerGCARel deg (FreeAlgebra.ι k x * FreeAlgebra.ι k y)
        (((-1 : k) ^ (deg x * deg y)) • (FreeAlgebra.ι k y * FreeAlgebra.ι k x))
  | sq (x : G) (h : Odd (deg x)) :
      DeningerGCARel deg (FreeAlgebra.ι k x * FreeAlgebra.ι k x) 0

/-- **The free graded-commutative algebra** on generators of assigned degrees. -/
abbrev DeningerFreeGCA (deg : G → ℕ) : Type _ :=
  RingQuot (DeningerGCARel k G deg)

variable {G}

/-- The quotient map onto the free graded-commutative algebra. -/
def deningerGCAmk (deg : G → ℕ) : FreeAlgebra k G →ₐ[k] DeningerFreeGCA k G deg :=
  RingQuot.mkAlgHom k (DeningerGCARel k G deg)

/-- The generators of the free graded-commutative algebra. -/
def deningerGCAι (deg : G → ℕ) (x : G) : DeningerFreeGCA k G deg :=
  deningerGCAmk k deg (FreeAlgebra.ι k x)

/-- **The Koszul commutation relation.** -/
theorem deningerGCA_comm (deg : G → ℕ) (x y : G) :
    deningerGCAι k deg x * deningerGCAι k deg y =
      ((-1 : k) ^ (deg x * deg y)) • (deningerGCAι k deg y * deningerGCAι k deg x) := by
  have h := RingQuot.mkAlgHom_rel (S := k) (DeningerGCARel.comm (k := k) (deg := deg) x y)
  simpa [deningerGCAι, deningerGCAmk] using h

/-- **An odd generator squares to zero.** -/
theorem deningerGCA_sq_zero (deg : G → ℕ) {x : G} (h : Odd (deg x)) :
    deningerGCAι k deg x * deningerGCAι k deg x = 0 := by
  have hrel := RingQuot.mkAlgHom_rel (S := k) (DeningerGCARel.sq (k := k) (deg := deg) x h)
  simpa [deningerGCAι, deningerGCAmk] using hrel

/-- **Degree-one generators anticommute**, so the degree-one part behaves like an exterior
algebra. -/
theorem deningerGCA_anticomm_degreeOne (deg : G → ℕ) {x y : G}
    (hx : deg x = 1) (hy : deg y = 1) :
    deningerGCAι k deg x * deningerGCAι k deg y =
      -(deningerGCAι k deg y * deningerGCAι k deg x) := by
  rw [deningerGCA_comm, hx, hy, mul_one, pow_one]
  exact neg_one_smul k (deningerGCAι k deg y * deningerGCAι k deg x)

/-- **Even generators commute with every generator.** -/
theorem deningerGCA_comm_of_even (deg : G → ℕ) {x : G} (hx : Even (deg x)) (y : G) :
    deningerGCAι k deg x * deningerGCAι k deg y =
      deningerGCAι k deg y * deningerGCAι k deg x := by
  rw [deningerGCA_comm]
  obtain ⟨m, hm⟩ := hx
  have hpow : ((-1 : k) ^ (deg x * deg y)) = 1 := by
    rw [hm, show (m + m) * deg y = 2 * (m * deg y) by ring, pow_mul]
    simp
  rw [hpow, one_smul]

end Definition

section UniversalProperty

variable {k G A : Type*} [CommRing k] [Ring A] [Algebra k A] {deg : G → ℕ}

/-- **The universal property.**  A family of elements of an algebra satisfying the Koszul relations
extends uniquely to an algebra map out of the free graded-commutative algebra. -/
def deningerGCALift (f : G → A)
    (hcomm : ∀ x y, f x * f y = ((-1 : k) ^ (deg x * deg y)) • (f y * f x))
    (hsq : ∀ x, Odd (deg x) → f x * f x = 0) :
    DeningerFreeGCA k G deg →ₐ[k] A :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k f, by
    rintro _ _ (⟨x, y⟩ | ⟨x, hx⟩)
    · rw [map_mul, map_smul, map_mul, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
      exact hcomm x y
    · rw [map_mul, map_zero, FreeAlgebra.lift_ι_apply]
      exact hsq x hx⟩

@[simp]
theorem deningerGCALift_ι (f : G → A)
    (hcomm : ∀ x y, f x * f y = ((-1 : k) ^ (deg x * deg y)) • (f y * f x))
    (hsq : ∀ x, Odd (deg x) → f x * f x = 0) (x : G) :
    deningerGCALift f hcomm hsq (deningerGCAι k deg x) = f x := by
  simp [deningerGCALift, deningerGCAι, deningerGCAmk]

/-- **Uniqueness in the universal property.**  Two algebra maps agreeing on the generators are
equal. -/
theorem deningerGCA_hom_ext {F G' : DeningerFreeGCA k G deg →ₐ[k] A}
    (h : ∀ x : G, F (deningerGCAι k deg x) = G' (deningerGCAι k deg x)) : F = G' := by
  refine RingQuot.ringQuot_ext' k F G' ?_
  refine FreeAlgebra.hom_ext ?_
  funext x
  exact h x

end UniversalProperty

section Involute

variable (k : Type*) {G : Type*} [CommRing k] (deg : G → ℕ)

theorem deningerGCAInvolute_comm (x y : G) :
    (((-1 : k) ^ deg x) • deningerGCAι k deg x) * (((-1 : k) ^ deg y) • deningerGCAι k deg y) =
      ((-1 : k) ^ (deg x * deg y)) •
        ((((-1 : k) ^ deg y) • deningerGCAι k deg y) *
          (((-1 : k) ^ deg x) • deningerGCAι k deg x)) := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm, deningerGCA_comm k deg x y, smul_smul, smul_smul]
  congr 1
  ring

theorem deningerGCAInvolute_sq (x : G) (hx : Odd (deg x)) :
    (((-1 : k) ^ deg x) • deningerGCAι k deg x) * (((-1 : k) ^ deg x) • deningerGCAι k deg x)
      = 0 := by
  rw [smul_mul_smul_comm, deningerGCA_sq_zero k deg hx, smul_zero]

/-- **The grading involution** of a free graded-commutative algebra: the algebra map multiplying
each generator by the sign of its degree. -/
def deningerGCAInvolute : DeningerFreeGCA k G deg →ₐ[k] DeningerFreeGCA k G deg :=
  deningerGCALift (fun x => ((-1 : k) ^ deg x) • deningerGCAι k deg x)
    (deningerGCAInvolute_comm k deg) (deningerGCAInvolute_sq k deg)

@[simp]
theorem deningerGCAInvolute_ι (x : G) :
    deningerGCAInvolute k deg (deningerGCAι k deg x) =
      ((-1 : k) ^ deg x) • deningerGCAι k deg x :=
  deningerGCALift_ι _ _ _ x

/-- **The grading involution is an involution.** -/
@[simp]
theorem deningerGCAInvolute_involute (z : DeningerFreeGCA k G deg) :
    deningerGCAInvolute k deg (deningerGCAInvolute k deg z) = z := by
  have h : (deningerGCAInvolute k deg).comp (deningerGCAInvolute k deg) =
      AlgHom.id k (DeningerFreeGCA k G deg) := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [AlgHom.comp_apply, deningerGCAInvolute_ι, map_smul, deningerGCAInvolute_ι, smul_smul,
      ← pow_add, AlgHom.id_apply]
    rw [show deg x + deg x = 2 * deg x by ring, pow_mul]
    simp
  exact AlgHom.congr_fun h z

/-- **Degree-one generators are negated by the involution**, matching the exterior algebra. -/
theorem deningerGCAInvolute_ι_degreeOne {x : G} (hx : deg x = 1) :
    deningerGCAInvolute k deg (deningerGCAι k deg x) = -deningerGCAι k deg x := by
  rw [deningerGCAInvolute_ι, hx, pow_one]
  exact neg_one_smul k (deningerGCAι k deg x)

/-- **Even generators are fixed by the involution.** -/
theorem deningerGCAInvolute_ι_of_even {x : G} (hx : Even (deg x)) :
    deningerGCAInvolute k deg (deningerGCAι k deg x) = deningerGCAι k deg x := by
  rw [deningerGCAInvolute_ι]
  obtain ⟨m, hm⟩ := hx
  rw [hm, show m + m = 2 * m by ring, pow_mul]
  simp

end Involute

section OddExtension

variable (k : Type*) (G : Type*) [CommRing k] (deg : G → ℕ)

/-- The square-zero odd extension of a free graded-commutative algebra: `ε` anticommutes with odd
elements and squares to zero, so the product is `(a, b) (a', b') = (a a', σ a * b' + b * a')` for
the grading involution `σ`. -/
def DeningerGCAOddExt : Type _ :=
  DeningerFreeGCA k G deg × DeningerFreeGCA k G deg

namespace DeningerGCAOddExt

variable {k G deg}

instance : AddCommGroup (DeningerGCAOddExt k G deg) :=
  inferInstanceAs (AddCommGroup (DeningerFreeGCA k G deg × DeningerFreeGCA k G deg))

instance : Module k (DeningerGCAOddExt k G deg) :=
  inferInstanceAs (Module k (DeningerFreeGCA k G deg × DeningerFreeGCA k G deg))

/-- The even part of an element of the odd extension. -/
def even (x : DeningerGCAOddExt k G deg) : DeningerFreeGCA k G deg := x.1

/-- The odd part of an element of the odd extension. -/
def odd (x : DeningerGCAOddExt k G deg) : DeningerFreeGCA k G deg := x.2

/-- Construct an element of the odd extension from its two parts. -/
def mk (a b : DeningerFreeGCA k G deg) : DeningerGCAOddExt k G deg := (a, b)

@[simp] theorem even_mk (a b : DeningerFreeGCA k G deg) : even (mk a b) = a := rfl
@[simp] theorem odd_mk (a b : DeningerFreeGCA k G deg) : odd (mk a b) = b := rfl

@[ext]
theorem ext {x y : DeningerGCAOddExt k G deg} (h1 : even x = even y) (h2 : odd x = odd y) :
    x = y :=
  Prod.ext h1 h2

@[simp] theorem even_zero : even (0 : DeningerGCAOddExt k G deg) = 0 := rfl
@[simp] theorem odd_zero : odd (0 : DeningerGCAOddExt k G deg) = 0 := rfl
@[simp] theorem even_add (x y : DeningerGCAOddExt k G deg) :
    even (x + y) = even x + even y := rfl
@[simp] theorem odd_add (x y : DeningerGCAOddExt k G deg) : odd (x + y) = odd x + odd y := rfl
@[simp] theorem even_smul (c : k) (x : DeningerGCAOddExt k G deg) :
    even (c • x) = c • even x := rfl
@[simp] theorem odd_smul (c : k) (x : DeningerGCAOddExt k G deg) :
    odd (c • x) = c • odd x := rfl

instance : One (DeningerGCAOddExt k G deg) := ⟨mk 1 0⟩

instance : Mul (DeningerGCAOddExt k G deg) :=
  ⟨fun x y => mk (even x * even y)
    (deningerGCAInvolute k deg (even x) * odd y + odd x * even y)⟩

@[simp] theorem even_one : even (1 : DeningerGCAOddExt k G deg) = 1 := rfl
@[simp] theorem odd_one : odd (1 : DeningerGCAOddExt k G deg) = 0 := rfl

@[simp]
theorem even_mul (x y : DeningerGCAOddExt k G deg) : even (x * y) = even x * even y := rfl

@[simp]
theorem odd_mul (x y : DeningerGCAOddExt k G deg) :
    odd (x * y) = deningerGCAInvolute k deg (even x) * odd y + odd x * even y := rfl

instance : Ring (DeningerGCAOddExt k G deg) :=
  { (inferInstance : AddCommGroup (DeningerGCAOddExt k G deg)) with
    mul := (· * ·)
    one := 1
    mul_assoc := fun x y z => by
      ext
      · exact mul_assoc _ _ _
      · show deningerGCAInvolute k deg (even x * even y) * odd z +
            (deningerGCAInvolute k deg (even x) * odd y + odd x * even y) * even z =
          deningerGCAInvolute k deg (even x) *
              (deningerGCAInvolute k deg (even y) * odd z + odd y * even z) +
            odd x * (even y * even z)
        rw [map_mul]
        noncomm_ring
    one_mul := fun x => by
      ext
      · exact one_mul _
      · show deningerGCAInvolute k deg 1 * odd x + 0 * even x = odd x
        rw [map_one]
        noncomm_ring
    mul_one := fun x => by
      ext
      · exact mul_one _
      · show deningerGCAInvolute k deg (even x) * 0 + odd x * 1 = odd x
        noncomm_ring
    left_distrib := fun x y z => by
      ext
      · exact mul_add _ _ _
      · show deningerGCAInvolute k deg (even x) * (odd y + odd z) +
            odd x * (even y + even z) =
          deningerGCAInvolute k deg (even x) * odd y + odd x * even y +
            (deningerGCAInvolute k deg (even x) * odd z + odd x * even z)
        noncomm_ring
    right_distrib := fun x y z => by
      ext
      · exact add_mul _ _ _
      · show deningerGCAInvolute k deg (even x + even y) * odd z +
            (odd x + odd y) * even z =
          deningerGCAInvolute k deg (even x) * odd z + odd x * even z +
            (deningerGCAInvolute k deg (even y) * odd z + odd y * even z)
        rw [map_add]
        noncomm_ring
    zero_mul := fun x => by
      ext
      · exact zero_mul _
      · show deningerGCAInvolute k deg 0 * odd x + 0 * even x = 0
        rw [map_zero]
        noncomm_ring
    mul_zero := fun x => by
      ext
      · exact mul_zero _
      · show deningerGCAInvolute k deg (even x) * 0 + odd x * 0 = 0
        simp }

instance : Algebra k (DeningerGCAOddExt k G deg) where
  algebraMap :=
    { toFun := fun c => mk (algebraMap k (DeningerFreeGCA k G deg) c) 0
      map_one' := by ext <;> simp
      map_mul' := fun c d => by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun c d => by ext <;> simp }
  commutes' c x := by
    ext
    · exact Algebra.commutes c (even x)
    · simp [Algebra.commutes, AlgHom.commutes]
  smul_def' c x := by
    ext
    · exact Algebra.smul_def c (even x)
    · show c • odd x =
        deningerGCAInvolute k deg (algebraMap k (DeningerFreeGCA k G deg) c) * odd x +
          0 * even x
      rw [AlgHom.commutes, zero_mul, add_zero, Algebra.smul_def]

/-- The even part is an algebra map to the free graded-commutative algebra. -/
def evenHom : DeningerGCAOddExt k G deg →ₐ[k] DeningerFreeGCA k G deg where
  toFun := even
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The odd part, as a linear map. -/
def oddLinear : DeningerGCAOddExt k G deg →ₗ[k] DeningerFreeGCA k G deg where
  toFun := odd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end DeningerGCAOddExt

end OddExtension

section OddDerivation

variable {k G : Type*} [CommRing k] {deg : G → ℕ}

theorem deningerNegOnePow_two_mul (t : ℕ) : ((-1 : k)) ^ (2 * t) = 1 := by
  rw [pow_mul]
  simp

theorem deningerNegOnePow_sign_left (m n : ℕ) :
    ((-1 : k)) ^ m * ((-1 : k)) ^ (m * (n + 1)) = ((-1 : k)) ^ (m * n) := by
  rw [← pow_add, show m + m * (n + 1) = 2 * m + m * n by ring, pow_add,
    deningerNegOnePow_two_mul, one_mul]

theorem deningerNegOnePow_sign_right (m n : ℕ) :
    ((-1 : k)) ^ (m * n) * ((-1 : k)) ^ n * ((-1 : k)) ^ (n * (m + 1)) = 1 := by
  rw [← pow_add, ← pow_add, show m * n + n + n * (m + 1) = 2 * (m * n + n) by ring,
    deningerNegOnePow_two_mul]

variable (phi : G → DeningerFreeGCA k G deg)
variable (hphi : ∀ x y : G, deningerGCAι k deg x * phi y =
  ((-1 : k) ^ (deg x * (deg y + 1))) • (phi y * deningerGCAι k deg x))

include hphi in
theorem deningerGCAOddGen_comm (x y : G) :
    (DeningerGCAOddExt.mk (deningerGCAι k deg x) (phi x)) *
        (DeningerGCAOddExt.mk (deningerGCAι k deg y) (phi y)) =
      ((-1 : k) ^ (deg x * deg y)) •
        ((DeningerGCAOddExt.mk (deningerGCAι k deg y) (phi y)) *
          (DeningerGCAOddExt.mk (deningerGCAι k deg x) (phi x))) := by
  ext
  · exact deningerGCA_comm k deg x y
  · show deningerGCAInvolute k deg (deningerGCAι k deg x) * phi y +
        phi x * deningerGCAι k deg y =
      ((-1 : k) ^ (deg x * deg y)) •
        (deningerGCAInvolute k deg (deningerGCAι k deg y) * phi x +
          phi y * deningerGCAι k deg x)
    rw [deningerGCAInvolute_ι, deningerGCAInvolute_ι, smul_mul_assoc, smul_mul_assoc,
      hphi x y, hphi y x, smul_smul, smul_add, smul_smul, smul_smul,
      deningerNegOnePow_sign_left, deningerNegOnePow_sign_right, one_smul, add_comm]

include hphi in
theorem deningerGCAOddGen_sq (x : G) (hx : Odd (deg x)) :
    (DeningerGCAOddExt.mk (deningerGCAι k deg x) (phi x)) *
        (DeningerGCAOddExt.mk (deningerGCAι k deg x) (phi x)) = 0 := by
  ext
  · exact deningerGCA_sq_zero k deg hx
  · show deningerGCAInvolute k deg (deningerGCAι k deg x) * phi x +
        phi x * deningerGCAι k deg x = 0
    have hpow : ((-1 : k) ^ (deg x * (deg x + 1))) = 1 := by
      obtain ⟨m, hm⟩ := hx
      rw [hm, show (2 * m + 1) * (2 * m + 1 + 1) = 2 * ((2 * m + 1) * (m + 1)) by ring,
        deningerNegOnePow_two_mul]
    have hodd : ((-1 : k) ^ deg x) = -1 := by
      obtain ⟨m, hm⟩ := hx
      rw [hm, pow_add, pow_mul]
      simp
    rw [deningerGCAInvolute_ι, smul_mul_assoc, hphi x x, hpow, one_smul, hodd,
      neg_one_smul k (phi x * deningerGCAι k deg x)]
    exact neg_add_cancel _

include hphi in
/-- The algebra map into the square-zero odd extension determined by the generator values. -/
def deningerGCAOddDerivationHom :
    DeningerFreeGCA k G deg →ₐ[k] DeningerGCAOddExt k G deg :=
  deningerGCALift (fun x => DeningerGCAOddExt.mk (deningerGCAι k deg x) (phi x))
    (deningerGCAOddGen_comm phi hphi) (deningerGCAOddGen_sq phi hphi)

include hphi in
/-- **The odd derivation** of a free graded-commutative algebra determined by its values on the
generators, for generators of arbitrary degree. -/
def deningerGCAOddDerivation :
    DeningerFreeGCA k G deg →ₗ[k] DeningerFreeGCA k G deg :=
  (DeningerGCAOddExt.oddLinear).comp
    (deningerGCAOddDerivationHom phi hphi).toLinearMap

include hphi in
/-- The even part of the lift is the identity. -/
theorem deningerGCAOddDerivationHom_even (z : DeningerFreeGCA k G deg) :
    DeningerGCAOddExt.even (deningerGCAOddDerivationHom phi hphi z) = z := by
  have h : (DeningerGCAOddExt.evenHom).comp (deningerGCAOddDerivationHom phi hphi) =
      AlgHom.id k (DeningerFreeGCA k G deg) := by
    refine deningerGCA_hom_ext fun x => ?_
    show DeningerGCAOddExt.even
      (deningerGCAOddDerivationHom phi hphi (deningerGCAι k deg x)) = deningerGCAι k deg x
    rw [deningerGCAOddDerivationHom, deningerGCALift_ι]
    rfl
  exact AlgHom.congr_fun h z

include hphi in
@[simp]
theorem deningerGCAOddDerivation_ι (x : G) :
    deningerGCAOddDerivation phi hphi (deningerGCAι k deg x) = phi x := by
  show DeningerGCAOddExt.odd
    (deningerGCAOddDerivationHom phi hphi (deningerGCAι k deg x)) = phi x
  rw [deningerGCAOddDerivationHom, deningerGCALift_ι]
  rfl

include hphi in
/-- **The graded Leibniz rule** on a free graded-commutative algebra. -/
theorem deningerGCAOddDerivation_leibniz (z w : DeningerFreeGCA k G deg) :
    deningerGCAOddDerivation phi hphi (z * w) =
      deningerGCAInvolute k deg z * deningerGCAOddDerivation phi hphi w +
        deningerGCAOddDerivation phi hphi z * w := by
  have h : deningerGCAOddDerivationHom phi hphi (z * w) =
      deningerGCAOddDerivationHom phi hphi z * deningerGCAOddDerivationHom phi hphi w :=
    map_mul _ _ _
  have h2 := congrArg DeningerGCAOddExt.odd h
  rw [DeningerGCAOddExt.odd_mul, deningerGCAOddDerivationHom_even phi hphi z,
    deningerGCAOddDerivationHom_even phi hphi w] at h2
  exact h2

/-- **Induction on a free graded-commutative algebra**: a property holding on scalars and
generators and closed under sums and products holds everywhere. -/
theorem deningerGCA_induction {motive : DeningerFreeGCA k G deg → Prop}
    (algMap : ∀ r, motive (algebraMap k (DeningerFreeGCA k G deg) r))
    (gen : ∀ x, motive (deningerGCAι k deg x))
    (mul : ∀ a b, motive a → motive b → motive (a * b))
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (z : DeningerFreeGCA k G deg) : motive z := by
  obtain ⟨a, rfl⟩ := RingQuot.mkAlgHom_surjective k (DeningerGCARel k G deg) z
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes]
    exact algMap r
  | grade1 x => exact gen x
  | mul a b ha hb =>
    rw [map_mul]
    exact mul _ _ ha hb
  | add a b ha hb =>
    rw [map_add]
    exact add _ _ ha hb

include hphi in
@[simp]
theorem deningerGCAOddDerivation_algebraMap (r : k) :
    deningerGCAOddDerivation phi hphi (algebraMap k (DeningerFreeGCA k G deg) r) = 0 := by
  show DeningerGCAOddExt.odd
    (deningerGCAOddDerivationHom phi hphi (algebraMap k (DeningerFreeGCA k G deg) r)) = 0
  rw [AlgHom.commutes]
  rfl

variable (hinv : ∀ x : G, deningerGCAInvolute k deg (phi x) =
  ((-1 : k) ^ (deg x + 1)) • phi x)

include hphi hinv in
/-- **The derivation anticommutes with the grading involution**, provided each generator value
transforms as an element of degree one more than its generator. -/
theorem deningerGCAOddDerivation_involute (z : DeningerFreeGCA k G deg) :
    deningerGCAOddDerivation phi hphi (deningerGCAInvolute k deg z) =
      -deningerGCAInvolute k deg (deningerGCAOddDerivation phi hphi z) := by
  induction z using deningerGCA_induction with
  | algMap r => simp [AlgHom.commutes]
  | gen x =>
    have hs : ((-1 : k) ^ (deg x + 1)) = -((-1 : k) ^ deg x) := by
      rw [pow_succ]; ring
    rw [deningerGCAInvolute_ι, map_smul, deningerGCAOddDerivation_ι, hinv, hs]
    module
  | add a b ha hb => simp only [map_add, ha, hb, neg_add]
  | mul a b ha hb =>
    rw [map_mul, deningerGCAOddDerivation_leibniz, ha, hb,
      deningerGCAInvolute_involute, deningerGCAOddDerivation_leibniz, map_add, map_mul, map_mul,
      deningerGCAInvolute_involute,
      mul_neg a (deningerGCAInvolute k deg (deningerGCAOddDerivation phi hphi b)),
      neg_mul (deningerGCAInvolute k deg (deningerGCAOddDerivation phi hphi a))
        (deningerGCAInvolute k deg b)]
    abel

include hphi hinv in
/-- **The derivation squares to zero** as soon as it kills its own generator values. -/
theorem deningerGCAOddDerivation_comp_self
    (hkill : ∀ x : G, deningerGCAOddDerivation phi hphi (phi x) = 0)
    (z : DeningerFreeGCA k G deg) :
    deningerGCAOddDerivation phi hphi (deningerGCAOddDerivation phi hphi z) = 0 := by
  induction z using deningerGCA_induction with
  | algMap r => rw [deningerGCAOddDerivation_algebraMap, map_zero]
  | gen x => rw [deningerGCAOddDerivation_ι]; exact hkill x
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | mul a b ha hb =>
    rw [deningerGCAOddDerivation_leibniz, map_add, deningerGCAOddDerivation_leibniz,
      deningerGCAOddDerivation_leibniz, ha, hb,
      deningerGCAOddDerivation_involute phi hphi hinv a, deningerGCAInvolute_involute,
      mul_zero, zero_mul,
      neg_mul (deningerGCAInvolute k deg (deningerGCAOddDerivation phi hphi a))
        (deningerGCAOddDerivation phi hphi b)]
    abel

end OddDerivation

section Successor

variable {k G N : Type*} [CommRing k] (deg : G → ℕ) (degN : N → ℕ)

/-- The degree function of a stage extended by new generators. -/
abbrev deningerGCASuccDeg : G ⊕ N → ℕ :=
  Sum.elim deg degN

theorem deningerGCAInl_comm (x y : G) :
    deningerGCAι k (deningerGCASuccDeg deg degN) (Sum.inl x) *
        deningerGCAι k (deningerGCASuccDeg deg degN) (Sum.inl y) =
      ((-1 : k) ^ (deg x * deg y)) •
        (deningerGCAι k (deningerGCASuccDeg deg degN) (Sum.inl y) *
          deningerGCAι k (deningerGCASuccDeg deg degN) (Sum.inl x)) :=
  deningerGCA_comm k (deningerGCASuccDeg deg degN) (Sum.inl x) (Sum.inl y)

theorem deningerGCAInl_sq (x : G) (hx : Odd (deg x)) :
    deningerGCAι k (deningerGCASuccDeg deg degN) (Sum.inl x) *
      deningerGCAι k (deningerGCASuccDeg deg degN) (Sum.inl x) = 0 :=
  deningerGCA_sq_zero k (deningerGCASuccDeg deg degN) (x := Sum.inl x) hx

/-- **The inclusion of a stage into its successor**: the algebra map sending each old generator to
itself in the extended generator set. -/
def deningerGCAInl :
    DeningerFreeGCA k G deg →ₐ[k] DeningerFreeGCA k (G ⊕ N) (deningerGCASuccDeg deg degN) :=
  deningerGCALift (fun x => deningerGCAι k (deningerGCASuccDeg deg degN) (Sum.inl x))
    (deningerGCAInl_comm deg degN) (fun x hx => deningerGCAInl_sq deg degN x hx)

@[simp]
theorem deningerGCAInl_ι (x : G) :
    deningerGCAInl (N := N) deg degN (deningerGCAι k deg x) =
      deningerGCAι k (deningerGCASuccDeg deg degN) (Sum.inl x) :=
  deningerGCALift_ι _ _ _ x

/-- **Restricting a lift along the inclusion evaluates it on the old generators.**  A map out of
the extended algebra, precomposed with the inclusion of the previous stage, is determined on
generators by its values on the left summand. -/
theorem deningerGCALift_comp_inl {A : Type*} [Ring A] [Algebra k A]
    (f : G ⊕ N → A)
    (hcomm : ∀ u v, f u * f v =
      ((-1 : k) ^ (deningerGCASuccDeg deg degN u * deningerGCASuccDeg deg degN v)) • (f v * f u))
    (hsq : ∀ u, Odd (deningerGCASuccDeg deg degN u) → f u * f u = 0) (x : G) :
    deningerGCALift f hcomm hsq (deningerGCAInl (N := N) deg degN (deningerGCAι k deg x)) =
      f (Sum.inl x) := by
  rw [deningerGCAInl_ι, deningerGCALift_ι]

/-- **The inclusion commutes with the grading involution.** -/
theorem deningerGCAInvolute_inl (z : DeningerFreeGCA k G deg) :
    deningerGCAInvolute k (deningerGCASuccDeg deg degN)
        (deningerGCAInl (N := N) deg degN z) =
      deningerGCAInl (N := N) deg degN (deningerGCAInvolute k deg z) := by
  have h : (deningerGCAInvolute k (deningerGCASuccDeg deg degN)).comp
        (deningerGCAInl (N := N) deg degN) =
      (deningerGCAInl (N := N) deg degN).comp (deningerGCAInvolute k deg) := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, deningerGCAInl_ι, deningerGCAInvolute_ι,
      deningerGCAInvolute_ι, map_smul, deningerGCAInl_ι]
    rfl
  exact AlgHom.congr_fun h z

variable (phi : G → DeningerFreeGCA k G deg) (psi : N → DeningerFreeGCA k G deg)

/-- **The generator assignment of a successor stage** on the extended generator set: old generators
keep their differential and each new generator maps to the class it kills. -/
def deningerGCASuccPhi :
    G ⊕ N → DeningerFreeGCA k (G ⊕ N) (deningerGCASuccDeg deg degN) :=
  Sum.elim (fun x => deningerGCAInl deg degN (phi x))
    (fun n => deningerGCAInl deg degN (psi n))

@[simp]
theorem deningerGCASuccPhi_inl (x : G) :
    deningerGCASuccPhi deg degN phi psi (Sum.inl x) = deningerGCAInl deg degN (phi x) := rfl

@[simp]
theorem deningerGCASuccPhi_inr (n : N) :
    deningerGCASuccPhi deg degN phi psi (Sum.inr n) = deningerGCAInl deg degN (psi n) := rfl

variable (hphi : ∀ x y : G, deningerGCAι k deg x * phi y =
    ((-1 : k) ^ (deg x * (deg y + 1))) • (phi y * deningerGCAι k deg x))
variable (hphi' : ∀ u v : G ⊕ N,
    deningerGCAι k (deningerGCASuccDeg deg degN) u * deningerGCASuccPhi deg degN phi psi v =
      ((-1 : k) ^ (deningerGCASuccDeg deg degN u * (deningerGCASuccDeg deg degN v + 1))) •
        (deningerGCASuccPhi deg degN phi psi v *
          deningerGCAι k (deningerGCASuccDeg deg degN) u))

include hphi' in
/-- **The successor differential sends each new generator to the class it kills.** -/
theorem deningerGCASuccDerivation_new (n : N) :
    deningerGCAOddDerivation (deningerGCASuccPhi deg degN phi psi) hphi'
        (deningerGCAι k (deningerGCASuccDeg deg degN) (Sum.inr n)) =
      deningerGCAInl deg degN (psi n) := by
  rw [deningerGCAOddDerivation_ι, deningerGCASuccPhi_inr]

include hphi hphi' in
/-- **The successor differential restricts to the stage differential** on the image of the old
algebra, so the successor stage is a differential extension of its predecessor. -/
theorem deningerGCASuccDerivation_inl (z : DeningerFreeGCA k G deg) :
    deningerGCAOddDerivation (deningerGCASuccPhi deg degN phi psi) hphi'
        (deningerGCAInl deg degN z) =
      deningerGCAInl deg degN (deningerGCAOddDerivation phi hphi z) := by
  induction z using deningerGCA_induction with
  | algMap r =>
    rw [AlgHom.commutes, deningerGCAOddDerivation_algebraMap,
      deningerGCAOddDerivation_algebraMap, map_zero]
  | gen x =>
    rw [deningerGCAInl_ι, deningerGCAOddDerivation_ι, deningerGCAOddDerivation_ι,
      deningerGCASuccPhi_inl]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb =>
    rw [map_mul, deningerGCAOddDerivation_leibniz, ha, hb,
      deningerGCAOddDerivation_leibniz, map_add, map_mul, map_mul, deningerGCAInvolute_inl]

variable (hinv : ∀ x : G, deningerGCAInvolute k deg (phi x) =
    ((-1 : k) ^ (deg x + 1)) • phi x)
variable (hpsiInv : ∀ n : N, deningerGCAInvolute k deg (psi n) =
    ((-1 : k) ^ (degN n + 1)) • psi n)

include hinv hpsiInv in
/-- The successor generator values transform as elements of degree one more than their
generators. -/
theorem deningerGCASuccPhi_involute (u : G ⊕ N) :
    deningerGCAInvolute k (deningerGCASuccDeg deg degN)
        (deningerGCASuccPhi deg degN phi psi u) =
      ((-1 : k) ^ (deningerGCASuccDeg deg degN u + 1)) •
        deningerGCASuccPhi deg degN phi psi u := by
  cases u with
  | inl x =>
    rw [deningerGCASuccPhi_inl, deningerGCAInvolute_inl, hinv, map_smul]
    rfl
  | inr n =>
    rw [deningerGCASuccPhi_inr, deningerGCAInvolute_inl, hpsiInv, map_smul]
    rfl

variable (hkill : ∀ x : G, deningerGCAOddDerivation phi hphi (phi x) = 0)
variable (hpsiKill : ∀ n : N, deningerGCAOddDerivation phi hphi (psi n) = 0)

include hphi hphi' hkill hpsiKill in
/-- The successor differential kills its own generator values, given that the stage differential
does and that the attached classes are cocycles. -/
theorem deningerGCASuccPhi_kill (u : G ⊕ N) :
    deningerGCAOddDerivation (deningerGCASuccPhi deg degN phi psi) hphi'
      (deningerGCASuccPhi deg degN phi psi u) = 0 := by
  cases u with
  | inl x =>
    rw [deningerGCASuccPhi_inl,
      deningerGCASuccDerivation_inl deg degN phi psi hphi hphi', hkill, map_zero]
  | inr n =>
    rw [deningerGCASuccPhi_inr,
      deningerGCASuccDerivation_inl deg degN phi psi hphi hphi', hpsiKill, map_zero]

include hphi hphi' hinv hpsiInv hkill hpsiKill in
/-- **The successor differential squares to zero**, so the successor of a stage is again a stage
over the free graded-commutative algebra on mixed degrees. -/
theorem deningerGCASuccDerivation_comp_self
    (z : DeningerFreeGCA k (G ⊕ N) (deningerGCASuccDeg deg degN)) :
    deningerGCAOddDerivation (deningerGCASuccPhi deg degN phi psi) hphi'
        (deningerGCAOddDerivation (deningerGCASuccPhi deg degN phi psi) hphi' z) = 0 :=
  deningerGCAOddDerivation_comp_self _ hphi'
    (deningerGCASuccPhi_involute deg degN phi psi hinv hpsiInv)
    (deningerGCASuccPhi_kill deg degN phi psi hphi hphi' hkill hpsiKill) z

end Successor

section AnticommSum

variable {A : Type*} [Ring A] {ι : Type*}

/-- **A sum of pairwise anticommuting square-zero elements squares to zero.**  This is the
computation that makes an arbitrary vector, and not only a basis element, square to zero in an
exterior-type algebra. -/
theorem deningerAnticommSum_sq_zero (S : Finset ι) (a : ι → A)
    (hsq : ∀ i, a i * a i = 0) (hanti : ∀ i j, a i * a j = -(a j * a i)) :
    (∑ i ∈ S, a i) * (∑ i ∈ S, a i) = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
    have hcross : a x * (∑ i ∈ S, a i) + (∑ i ∈ S, a i) * a x = 0 := by
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hanti x j, neg_add_cancel]
    have expand : (a x + ∑ i ∈ S, a i) * (a x + ∑ i ∈ S, a i) =
        a x * a x + (a x * (∑ i ∈ S, a i) + (∑ i ∈ S, a i) * a x) +
          (∑ i ∈ S, a i) * (∑ i ∈ S, a i) := by
      noncomm_ring
    rw [Finset.sum_insert hx, expand, hsq, hcross, ih]
    simp

variable {k : Type*} [CommRing k] [Algebra k A]

/-- **A scalar combination of pairwise anticommuting square-zero elements squares to zero.** -/
theorem deningerAnticommSmulSum_sq_zero (S : Finset ι) (c : ι → k) (a : ι → A)
    (hsq : ∀ i, a i * a i = 0) (hanti : ∀ i j, a i * a j = -(a j * a i)) :
    (∑ i ∈ S, c i • a i) * (∑ i ∈ S, c i • a i) = 0 := by
  refine deningerAnticommSum_sq_zero S (fun i => c i • a i) (fun i => ?_) (fun i j => ?_)
  · rw [smul_mul_smul_comm, hsq, smul_zero]
  · rw [smul_mul_smul_comm, smul_mul_smul_comm, hanti i j, smul_neg, mul_comm (c j) (c i)]

end AnticommSum

section Commutation

variable {k G : Type*} [CommRing k] {deg : G → ℕ}

/-- **An odd generator moves past any element at the cost of the grading involution.**  This is the
free algebra's substitute for a grading: the involution records exactly the sign an odd generator
picks up. -/
theorem deningerGCA_ι_mul_of_odd {w : G} (hw : Odd (deg w)) (a : DeningerFreeGCA k G deg) :
    deningerGCAι k deg w * a = deningerGCAInvolute k deg a * deningerGCAι k deg w := by
  induction a using deningerGCA_induction with
  | algMap r =>
    rw [AlgHom.commutes]
    exact (Algebra.commutes r _).symm
  | gen x =>
    rw [deningerGCA_comm, deningerGCAInvolute_ι, smul_mul_assoc, pow_mul, hw.neg_one_pow]
  | mul a b ha hb =>
    rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc, map_mul]
  | add a b ha hb =>
    rw [mul_add, ha, hb, map_add, add_mul]

/-- **An even generator is central.** -/
theorem deningerGCA_ι_mul_of_even {w : G} (hw : Even (deg w)) (a : DeningerFreeGCA k G deg) :
    deningerGCAι k deg w * a = a * deningerGCAι k deg w := by
  induction a using deningerGCA_induction with
  | algMap r => exact (Algebra.commutes r _).symm
  | gen x =>
    rw [deningerGCA_comm, pow_mul, hw.neg_one_pow, one_pow, one_smul]
  | mul a b ha hb =>
    rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]
  | add a b ha hb =>
    rw [mul_add, ha, hb, add_mul]

/-- **A generator graded-commutes with any element of pure parity.**  An element whose image under
the grading involution is `(-1)^p` times itself behaves exactly like a homogeneous element of degree
`p` when a generator is moved past it. -/
theorem deningerGCA_ι_mul_of_involute (w : G) (a : DeningerFreeGCA k G deg) (p : ℕ)
    (ha : deningerGCAInvolute k deg a = ((-1 : k) ^ p) • a) :
    deningerGCAι k deg w * a =
      ((-1 : k) ^ (deg w * p)) • (a * deningerGCAι k deg w) := by
  rcases Nat.even_or_odd (deg w) with hw | hw
  · rw [deningerGCA_ι_mul_of_even hw, pow_mul, hw.neg_one_pow, one_pow, one_smul]
  · rw [deningerGCA_ι_mul_of_odd hw, ha, smul_mul_assoc, pow_mul, hw.neg_one_pow]

/-- **Admissibility of a generator assignment is a consequence of its parity.**  If the value of the
assignment on each generator transforms as an element of one degree higher, then it automatically
graded-commutes with every generator.  So the admissibility hypothesis of a Sullivan stage carries
no information beyond the parity hypothesis. -/
theorem deningerGCA_hphi_of_hinv (deg : G → ℕ) (psi : G → DeningerFreeGCA k G deg)
    (hinv : ∀ x : G, deningerGCAInvolute k deg (psi x) = ((-1 : k) ^ (deg x + 1)) • psi x) :
    ∀ x y : G, deningerGCAι k deg x * psi y =
      ((-1 : k) ^ (deg x * (deg y + 1))) • (psi y * deningerGCAι k deg x) :=
  fun x y => deningerGCA_ι_mul_of_involute x (psi y) (deg y + 1) (hinv y)

end Commutation

section Parity

variable {k G : Type*} [CommRing k] {deg : G → ℕ}

variable [Invertible (2 : k)]

/-- **The part of an element fixed by the grading involution.** -/
noncomputable def deningerGCAEvenPart (k : Type*) [CommRing k] [Invertible (2 : k)] {G : Type*}
    (deg : G → ℕ) (z : DeningerFreeGCA k G deg) : DeningerFreeGCA k G deg :=
  (⅟(2 : k)) • (z + deningerGCAInvolute k deg z)

/-- **The part of an element negated by the grading involution.** -/
noncomputable def deningerGCAOddPart (k : Type*) [CommRing k] [Invertible (2 : k)] {G : Type*}
    (deg : G → ℕ) (z : DeningerFreeGCA k G deg) : DeningerFreeGCA k G deg :=
  (⅟(2 : k)) • (z - deningerGCAInvolute k deg z)

/-- **Every element is the sum of its even and odd parts.**  With `2` invertible the grading
involution splits the algebra, so the parity hypothesis in statements about pure-parity elements
costs nothing. -/
theorem deningerGCAEvenPart_add_oddPart (z : DeningerFreeGCA k G deg) :
    deningerGCAEvenPart k deg z + deningerGCAOddPart k deg z = z := by
  rw [deningerGCAEvenPart, deningerGCAOddPart, ← smul_add]
  have h : (z + deningerGCAInvolute k deg z) + (z - deningerGCAInvolute k deg z) = (2 : k) • z := by
    rw [two_smul]
    abel
  rw [h, smul_smul, invOf_mul_self, one_smul]

/-- **The even part is fixed by the involution.** -/
theorem deningerGCAInvolute_evenPart (z : DeningerFreeGCA k G deg) :
    deningerGCAInvolute k deg (deningerGCAEvenPart k deg z) = deningerGCAEvenPart k deg z := by
  rw [deningerGCAEvenPart, map_smul, map_add, deningerGCAInvolute_involute, add_comm]

/-- **The odd part is negated by the involution.** -/
theorem deningerGCAInvolute_oddPart (z : DeningerFreeGCA k G deg) :
    deningerGCAInvolute k deg (deningerGCAOddPart k deg z) = -deningerGCAOddPart k deg z := by
  rw [deningerGCAOddPart, map_smul, map_sub, deningerGCAInvolute_involute]
  module

/-- The even part has the parity of an element of even degree. -/
theorem deningerGCAEvenPart_parity (z : DeningerFreeGCA k G deg) :
    deningerGCAInvolute k deg (deningerGCAEvenPart k deg z) =
      ((-1 : k) ^ (1 + 1)) • deningerGCAEvenPart k deg z := by
  rw [deningerGCAInvolute_evenPart]
  norm_num

/-- The odd part has the parity of an element of odd degree. -/
theorem deningerGCAOddPart_parity (z : DeningerFreeGCA k G deg) :
    deningerGCAInvolute k deg (deningerGCAOddPart k deg z) =
      ((-1 : k) ^ (0 + 1)) • deningerGCAOddPart k deg z := by
  rw [deningerGCAInvolute_oddPart, zero_add, pow_one]
  module

/-- **The even part of a cocycle is a cocycle.** -/
theorem deningerGCAOddDerivation_evenPart (phi : G → DeningerFreeGCA k G deg)
    (hphi : ∀ x y : G, deningerGCAι k deg x * phi y =
      ((-1 : k) ^ (deg x * (deg y + 1))) • (phi y * deningerGCAι k deg x))
    (hinv : ∀ x : G, deningerGCAInvolute k deg (phi x) = ((-1 : k) ^ (deg x + 1)) • phi x)
    {z : DeningerFreeGCA k G deg} (hz : deningerGCAOddDerivation phi hphi z = 0) :
    deningerGCAOddDerivation phi hphi (deningerGCAEvenPart k deg z) = 0 := by
  rw [deningerGCAEvenPart, map_smul, map_add, hz,
    deningerGCAOddDerivation_involute phi hphi hinv z, hz, map_zero, neg_zero, add_zero, smul_zero]

/-- **The odd part of a cocycle is a cocycle.** -/
theorem deningerGCAOddDerivation_oddPart (phi : G → DeningerFreeGCA k G deg)
    (hphi : ∀ x y : G, deningerGCAι k deg x * phi y =
      ((-1 : k) ^ (deg x * (deg y + 1))) • (phi y * deningerGCAι k deg x))
    (hinv : ∀ x : G, deningerGCAInvolute k deg (phi x) = ((-1 : k) ^ (deg x + 1)) • phi x)
    {z : DeningerFreeGCA k G deg} (hz : deningerGCAOddDerivation phi hphi z = 0) :
    deningerGCAOddDerivation phi hphi (deningerGCAOddPart k deg z) = 0 := by
  rw [deningerGCAOddPart, map_smul, map_sub, hz,
    deningerGCAOddDerivation_involute phi hphi hinv z, hz, map_zero, neg_zero, sub_zero, smul_zero]

end Parity

section GeneratorFunctor

variable {k : Type*} [CommRing k]

/-- **The free graded-commutative algebra is functorial in the generator set.**  A degree-preserving
map of generator sets induces an algebra map, because the Koszul relations are determined by the
degrees. -/
def deningerGCAGenAlg (k : Type*) [CommRing k] {G G' : Type*} (deg : G → ℕ) (deg' : G' → ℕ)
    (θ : G → G') (hdeg : ∀ x : G, deg' (θ x) = deg x) :
    DeningerFreeGCA k G deg →ₐ[k] DeningerFreeGCA k G' deg' :=
  deningerGCALift (fun x => deningerGCAι k deg' (θ x))
    (fun x y => by rw [deningerGCA_comm, hdeg, hdeg])
    (fun x hx => deningerGCA_sq_zero k deg' (by rw [hdeg]; exact hx))

@[simp]
theorem deningerGCAGenAlg_ι {G G' : Type*} (deg : G → ℕ) (deg' : G' → ℕ) (θ : G → G')
    (hdeg : ∀ x : G, deg' (θ x) = deg x) (x : G) :
    deningerGCAGenAlg k deg deg' θ hdeg (deningerGCAι k deg x) = deningerGCAι k deg' (θ x) :=
  deningerGCALift_ι _ _ _ x

/-- **A degree-preserving map of generator sets intertwines the grading involutions.** -/
theorem deningerGCAGenAlg_involute {G G' : Type*} (deg : G → ℕ) (deg' : G' → ℕ) (θ : G → G')
    (hdeg : ∀ x : G, deg' (θ x) = deg x) (z : DeningerFreeGCA k G deg) :
    deningerGCAGenAlg k deg deg' θ hdeg (deningerGCAInvolute k deg z) =
      deningerGCAInvolute k deg' (deningerGCAGenAlg k deg deg' θ hdeg z) := by
  have h : (deningerGCAGenAlg k deg deg' θ hdeg).comp (deningerGCAInvolute k deg) =
      (deningerGCAInvolute k deg').comp (deningerGCAGenAlg k deg deg' θ hdeg) := by
    refine deningerGCA_hom_ext fun x => ?_
    simp only [AlgHom.comp_apply, deningerGCAInvolute_ι, map_smul, deningerGCAGenAlg_ι, hdeg]
  exact AlgHom.congr_fun h z

/-- **The identity map of generators induces the identity.** -/
theorem deningerGCAGenAlg_id {G : Type*} (deg : G → ℕ) (hdeg : ∀ x : G, deg x = deg x)
    (z : DeningerFreeGCA k G deg) :
    deningerGCAGenAlg k deg deg (fun x => x) hdeg z = z := by
  have h : deningerGCAGenAlg k deg deg (fun x => x) hdeg =
      AlgHom.id k (DeningerFreeGCA k G deg) := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [deningerGCAGenAlg_ι, AlgHom.id_apply]
  exact AlgHom.congr_fun h z

/-- **Composition of generator maps induces composition of algebra maps.** -/
theorem deningerGCAGenAlg_comp {G G' G'' : Type*} (deg : G → ℕ) (deg' : G' → ℕ) (deg'' : G'' → ℕ)
    (θ : G → G') (θ' : G' → G'') (h1 : ∀ x : G, deg' (θ x) = deg x)
    (h2 : ∀ y : G', deg'' (θ' y) = deg' y) (h3 : ∀ x : G, deg'' (θ' (θ x)) = deg x)
    (z : DeningerFreeGCA k G deg) :
    deningerGCAGenAlg k deg' deg'' θ' h2 (deningerGCAGenAlg k deg deg' θ h1 z) =
      deningerGCAGenAlg k deg deg'' (fun x => θ' (θ x)) h3 z := by
  have h : (deningerGCAGenAlg k deg' deg'' θ' h2).comp (deningerGCAGenAlg k deg deg' θ h1) =
      deningerGCAGenAlg k deg deg'' (fun x => θ' (θ x)) h3 := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [AlgHom.comp_apply, deningerGCAGenAlg_ι, deningerGCAGenAlg_ι, deningerGCAGenAlg_ι]
  exact AlgHom.congr_fun h z

/-- **A pointwise-identity map of generators induces the identity.** -/
theorem deningerGCAGenAlg_eq_id {G : Type*} (deg : G → ℕ) (θ : G → G)
    (hdeg : ∀ x : G, deg (θ x) = deg x) (hθ : ∀ x : G, θ x = x) (z : DeningerFreeGCA k G deg) :
    deningerGCAGenAlg k deg deg θ hdeg z = z := by
  have h : deningerGCAGenAlg k deg deg θ hdeg = AlgHom.id k (DeningerFreeGCA k G deg) := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [deningerGCAGenAlg_ι, hθ, AlgHom.id_apply]
  exact AlgHom.congr_fun h z

/-- **A pointwise composite of generator maps induces the composite algebra map.** -/
theorem deningerGCAGenAlg_eq_comp {G G' G'' : Type*} (deg : G → ℕ) (deg' : G' → ℕ)
    (deg'' : G'' → ℕ) (θ : G → G') (θ' : G' → G'') (η : G → G'')
    (h1 : ∀ x : G, deg' (θ x) = deg x) (h2 : ∀ y : G', deg'' (θ' y) = deg' y)
    (h3 : ∀ x : G, deg'' (η x) = deg x) (hη : ∀ x : G, η x = θ' (θ x))
    (z : DeningerFreeGCA k G deg) :
    deningerGCAGenAlg k deg deg'' η h3 z =
      deningerGCAGenAlg k deg' deg'' θ' h2 (deningerGCAGenAlg k deg deg' θ h1 z) := by
  have h : deningerGCAGenAlg k deg deg'' η h3 =
      (deningerGCAGenAlg k deg' deg'' θ' h2).comp (deningerGCAGenAlg k deg deg' θ h1) := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [AlgHom.comp_apply, deningerGCAGenAlg_ι, deningerGCAGenAlg_ι, deningerGCAGenAlg_ι, hη]
  exact AlgHom.congr_fun h z

/-- **The functorial map on an extended generator set restricts along the inclusion.**  Extending a
degree-preserving map of generator sets by a map of the attached generators gives a map commuting
with the two inclusions. -/
theorem deningerGCAGenAlg_comp_inl {G N G' N' : Type*} (deg : G → ℕ) (degN : N → ℕ)
    (deg' : G' → ℕ) (degN' : N' → ℕ) (θ : G → G') (θN : N → N')
    (hdeg : ∀ u : G ⊕ N, deningerGCASuccDeg deg' degN'
      (Sum.elim (fun x => Sum.inl (θ x)) (fun n => Sum.inr (θN n)) u) =
        deningerGCASuccDeg deg degN u)
    (hdeg0 : ∀ x : G, deg' (θ x) = deg x) (z : DeningerFreeGCA k G deg) :
    deningerGCAGenAlg k (deningerGCASuccDeg deg degN) (deningerGCASuccDeg deg' degN')
        (Sum.elim (fun x => Sum.inl (θ x)) (fun n => Sum.inr (θN n))) hdeg
        (deningerGCAInl deg degN z) =
      deningerGCAInl deg' degN' (deningerGCAGenAlg k deg deg' θ hdeg0 z) := by
  have h : (deningerGCAGenAlg k (deningerGCASuccDeg deg degN) (deningerGCASuccDeg deg' degN')
        (Sum.elim (fun x => Sum.inl (θ x)) (fun n => Sum.inr (θN n))) hdeg).comp
        (deningerGCAInl deg degN) =
      (deningerGCAInl deg' degN').comp (deningerGCAGenAlg k deg deg' θ hdeg0) := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, deningerGCAInl_ι, deningerGCAGenAlg_ι,
      deningerGCAGenAlg_ι, deningerGCAInl_ι]
    rfl
  exact AlgHom.congr_fun h z

end GeneratorFunctor

section Retraction

variable {k G N : Type*} [CommRing k] (deg : G → ℕ) (degN : N → ℕ)

/-- The generator values of the retraction onto the old generators: an old generator is kept and a
new one is sent to zero. -/
def deningerGCARetrGen (deg : G → ℕ) (_degN : N → ℕ) : G ⊕ N → DeningerFreeGCA k G deg :=
  Sum.elim (fun x => deningerGCAι k deg x) fun _ => 0

theorem deningerGCARetrGen_comm (u v : G ⊕ N) :
    deningerGCARetrGen deg (k := k) degN u * deningerGCARetrGen deg degN v =
      ((-1 : k) ^ (deningerGCASuccDeg deg degN u * deningerGCASuccDeg deg degN v)) •
        (deningerGCARetrGen deg degN v * deningerGCARetrGen deg degN u) := by
  cases u with
  | inl x =>
    cases v with
    | inl y =>
      show deningerGCAι k deg x * deningerGCAι k deg y =
        ((-1 : k) ^ (deg x * deg y)) • (deningerGCAι k deg y * deningerGCAι k deg x)
      exact deningerGCA_comm k deg x y
    | inr n =>
      show deningerGCAι k deg x * 0 = _ • ((0 : DeningerFreeGCA k G deg) * deningerGCAι k deg x)
      rw [mul_zero, zero_mul, smul_zero]
  | inr n =>
    show (0 : DeningerFreeGCA k G deg) * deningerGCARetrGen deg degN v =
      _ • (deningerGCARetrGen deg degN v * 0)
    rw [zero_mul, mul_zero, smul_zero]

theorem deningerGCARetrGen_sq (u : G ⊕ N) (hu : Odd (deningerGCASuccDeg deg degN u)) :
    deningerGCARetrGen deg (k := k) degN u * deningerGCARetrGen deg degN u = 0 := by
  cases u with
  | inl x =>
    have hx : Odd (deg x) := hu
    exact deningerGCA_sq_zero k deg hx
  | inr n =>
    show (0 : DeningerFreeGCA k G deg) * 0 = 0
    rw [mul_zero]

/-- **The retraction of an extended free graded-commutative algebra onto the old one.** -/
def deningerGCARetr : DeningerFreeGCA k (G ⊕ N) (deningerGCASuccDeg deg degN) →ₐ[k]
    DeningerFreeGCA k G deg :=
  deningerGCALift (deningerGCARetrGen deg degN) (deningerGCARetrGen_comm deg degN)
    (deningerGCARetrGen_sq deg degN)

@[simp]
theorem deningerGCARetr_ι (u : G ⊕ N) :
    deningerGCARetr deg degN (deningerGCAι k (deningerGCASuccDeg deg degN) u) =
      deningerGCARetrGen deg degN u :=
  deningerGCALift_ι _ _ _ u

/-- **The retraction is a left inverse of the inclusion**, so the old algebra is a retract of the
extended one. -/
theorem deningerGCARetr_comp_inl (z : DeningerFreeGCA k G deg) :
    deningerGCARetr deg degN (deningerGCAInl (N := N) deg degN z) = z := by
  have h : (deningerGCARetr deg degN).comp (deningerGCAInl (N := N) deg degN) =
      AlgHom.id k (DeningerFreeGCA k G deg) := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [AlgHom.comp_apply, AlgHom.id_apply]
    exact deningerGCALift_comp_inl _ _ _ _ _ x
  exact AlgHom.congr_fun h z

/-- The ideal generated by the new generators. -/
def deningerGCANewIdeal :
    Ideal (DeningerFreeGCA k (G ⊕ N) (deningerGCASuccDeg deg degN)) :=
  Ideal.span (Set.range fun n : N =>
    deningerGCAι k (deningerGCASuccDeg deg degN) (Sum.inr n))

theorem deningerGCA_ι_inr_mem_newIdeal (n : N) :
    deningerGCAι k (deningerGCASuccDeg deg degN) (Sum.inr n) ∈
      deningerGCANewIdeal (k := k) deg degN :=
  Ideal.subset_span ⟨n, rfl⟩

/-- **The ideal generated by the new generators is two-sided.**  A new generator moves past any
element at the cost of the grading involution, so a right multiple of a member is again a left
multiple of a new generator. -/
theorem deningerGCANewIdeal_mul_mem
    {i : DeningerFreeGCA k (G ⊕ N) (deningerGCASuccDeg deg degN)}
    (hi : i ∈ deningerGCANewIdeal (k := k) deg degN)
    (a : DeningerFreeGCA k (G ⊕ N) (deningerGCASuccDeg deg degN)) :
    i * a ∈ deningerGCANewIdeal (k := k) deg degN := by
  induction hi using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    rcases Nat.even_or_odd (deningerGCASuccDeg deg degN (Sum.inr n)) with he | ho
    · rw [deningerGCA_ι_mul_of_even he]
      exact Ideal.mul_mem_left _ _ (deningerGCA_ι_inr_mem_newIdeal deg degN n)
    · rw [deningerGCA_ι_mul_of_odd ho]
      exact Ideal.mul_mem_left _ _ (deningerGCA_ι_inr_mem_newIdeal deg degN n)
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/-- **Every element differs from its retraction by an element of the ideal of new generators.** -/
theorem deningerGCA_sub_inl_retr_mem
    (z : DeningerFreeGCA k (G ⊕ N) (deningerGCASuccDeg deg degN)) :
    z - deningerGCAInl deg degN (deningerGCARetr deg degN z) ∈
      deningerGCANewIdeal (k := k) deg degN := by
  induction z using deningerGCA_induction with
  | algMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, sub_self]
    exact Submodule.zero_mem _
  | gen u =>
    cases u with
    | inl x =>
      rw [deningerGCARetr_ι]
      show deningerGCAι k (deningerGCASuccDeg deg degN) (Sum.inl x) -
        deningerGCAInl deg degN (deningerGCAι k deg x) ∈ _
      rw [deningerGCAInl_ι, sub_self]
      exact Submodule.zero_mem _
    | inr n =>
      rw [deningerGCARetr_ι]
      show deningerGCAι k (deningerGCASuccDeg deg degN) (Sum.inr n) -
        deningerGCAInl deg degN (0 : DeningerFreeGCA k G deg) ∈ _
      rw [map_zero, sub_zero]
      exact deningerGCA_ι_inr_mem_newIdeal deg degN n
  | add a b ha hb =>
    have h : a + b - deningerGCAInl deg degN (deningerGCARetr deg degN (a + b)) =
        (a - deningerGCAInl deg degN (deningerGCARetr deg degN a)) +
          (b - deningerGCAInl deg degN (deningerGCARetr deg degN b)) := by
      rw [map_add, map_add]
      abel
    rw [h]
    exact Submodule.add_mem _ ha hb
  | mul a b ha hb =>
    have h : a * b - deningerGCAInl deg degN (deningerGCARetr deg degN (a * b)) =
        (a - deningerGCAInl deg degN (deningerGCARetr deg degN a)) * b +
          deningerGCAInl deg degN (deningerGCARetr deg degN a) *
            (b - deningerGCAInl deg degN (deningerGCARetr deg degN b)) := by
      rw [map_mul, map_mul, sub_mul, mul_sub]
      abel
    rw [h]
    exact Submodule.add_mem _ (deningerGCANewIdeal_mul_mem deg degN ha b)
      (Ideal.mul_mem_left _ _ hb)

/-- **The extension is free over the old algebra**: an element is killed by the retraction exactly
when it lies in the ideal generated by the new generators.  This is the sense in which the extension
is `P ⊗ Λ(W)`: the augmentation ideal of the retraction is generated by the new generators. -/
theorem deningerGCARetr_eq_zero_iff
    (z : DeningerFreeGCA k (G ⊕ N) (deningerGCASuccDeg deg degN)) :
    deningerGCARetr deg degN z = 0 ↔ z ∈ deningerGCANewIdeal (k := k) deg degN := by
  constructor
  · intro hz
    have h := deningerGCA_sub_inl_retr_mem (k := k) deg degN z
    rw [hz, map_zero, sub_zero] at h
    exact h
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      rw [deningerGCARetr_ι]
      rfl
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [smul_eq_mul, map_mul, hx, mul_zero]

end Retraction

section Weight

variable {k G : Type*} [CommRing k] {deg : G → ℕ}

theorem deningerGCAWeight_comm (deg : G → ℕ) (t : k) (x y : G) :
    ((t ^ deg x) • deningerGCAι k deg x) * ((t ^ deg y) • deningerGCAι k deg y) =
      ((-1 : k) ^ (deg x * deg y)) •
        (((t ^ deg y) • deningerGCAι k deg y) * ((t ^ deg x) • deningerGCAι k deg x)) := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm, deningerGCA_comm k deg x y, smul_smul, smul_smul]
  congr 1
  ring

theorem deningerGCAWeight_sq (deg : G → ℕ) (t : k) (x : G) (hx : Odd (deg x)) :
    ((t ^ deg x) • deningerGCAι k deg x) * ((t ^ deg x) • deningerGCAι k deg x) = 0 := by
  rw [smul_mul_smul_comm, deningerGCA_sq_zero k deg hx, smul_zero]

/-- **The weight action.**  Scaling each generator by `t` to the power of its degree is an algebra
map, because the Koszul relations are homogeneous.  It is the grading of the algebra in the form of
an action: an element is homogeneous of weight `n` exactly when the action scales it by `t^n`. -/
def deningerGCAWeight (k : Type*) [CommRing k] {G : Type*} (deg : G → ℕ) (t : k) :
    DeningerFreeGCA k G deg →ₐ[k] DeningerFreeGCA k G deg :=
  deningerGCALift (fun x => (t ^ deg x) • deningerGCAι k deg x) (deningerGCAWeight_comm deg t)
    (fun x hx => deningerGCAWeight_sq deg t x hx)

@[simp]
theorem deningerGCAWeight_ι (t : k) (x : G) :
    deningerGCAWeight k deg t (deningerGCAι k deg x) = (t ^ deg x) • deningerGCAι k deg x :=
  deningerGCALift_ι _ _ _ x

/-- **The weight action at `1` is the identity.** -/
theorem deningerGCAWeight_one (z : DeningerFreeGCA k G deg) :
    deningerGCAWeight k deg 1 z = z := by
  have h : deningerGCAWeight k deg (1 : k) = AlgHom.id k (DeningerFreeGCA k G deg) := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [deningerGCAWeight_ι, one_pow, one_smul, AlgHom.id_apply]
  exact AlgHom.congr_fun h z

/-- **The weight action at `-1` is the grading involution.**  Every statement about the parity of an
element is a statement about its weight. -/
theorem deningerGCAWeight_neg_one (z : DeningerFreeGCA k G deg) :
    deningerGCAWeight k deg (-1 : k) z = deningerGCAInvolute k deg z := by
  have h : deningerGCAWeight k deg (-1 : k) = deningerGCAInvolute k deg := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [deningerGCAWeight_ι, deningerGCAInvolute_ι]
  exact AlgHom.congr_fun h z

/-- **The weight action is multiplicative in the parameter.** -/
theorem deningerGCAWeight_mul (s t : k) (z : DeningerFreeGCA k G deg) :
    deningerGCAWeight k deg s (deningerGCAWeight k deg t z) =
      deningerGCAWeight k deg (s * t) z := by
  have h : (deningerGCAWeight k deg s).comp (deningerGCAWeight k deg t) =
      deningerGCAWeight k deg (s * t) := by
    refine deningerGCA_hom_ext fun x => ?_
    rw [AlgHom.comp_apply, deningerGCAWeight_ι, map_smul, deningerGCAWeight_ι, smul_smul,
      deningerGCAWeight_ι, mul_pow]
    congr 1
    ring
  exact AlgHom.congr_fun h z

/-- **The weight action commutes with the grading involution.** -/
theorem deningerGCAWeight_involute (t : k) (z : DeningerFreeGCA k G deg) :
    deningerGCAWeight k deg t (deningerGCAInvolute k deg z) =
      deningerGCAInvolute k deg (deningerGCAWeight k deg t z) := by
  rw [← deningerGCAWeight_neg_one, deningerGCAWeight_mul, ← deningerGCAWeight_neg_one,
    deningerGCAWeight_mul, mul_comm]

/-- **Homogeneity of weight `n`**: the weight action scales the element by `t^n`. -/
def DeningerGCAHomogeneous (k : Type*) [CommRing k] {G : Type*} (deg : G → ℕ) (n : ℕ)
    (z : DeningerFreeGCA k G deg) : Prop :=
  ∀ t : k, deningerGCAWeight k deg t z = (t ^ n) • z

/-- **A generator is homogeneous of its own degree.** -/
theorem deningerGCAHomogeneous_ι (x : G) :
    DeningerGCAHomogeneous k deg (deg x) (deningerGCAι k deg x) :=
  fun t => deningerGCAWeight_ι t x

theorem deningerGCAHomogeneous_algebraMap (r : k) :
    DeningerGCAHomogeneous k deg 0 (algebraMap k (DeningerFreeGCA k G deg) r) := by
  intro t
  rw [AlgHom.commutes, pow_zero, one_smul]

theorem deningerGCAHomogeneous_zero (n : ℕ) :
    DeningerGCAHomogeneous k deg n (0 : DeningerFreeGCA k G deg) := by
  intro t
  rw [map_zero, smul_zero]

theorem deningerGCAHomogeneous_add {n : ℕ} {z w : DeningerFreeGCA k G deg}
    (hz : DeningerGCAHomogeneous k deg n z) (hw : DeningerGCAHomogeneous k deg n w) :
    DeningerGCAHomogeneous k deg n (z + w) := by
  intro t
  rw [map_add, hz t, hw t, smul_add]

theorem deningerGCAHomogeneous_smul {n : ℕ} (c : k) {z : DeningerFreeGCA k G deg}
    (hz : DeningerGCAHomogeneous k deg n z) : DeningerGCAHomogeneous k deg n (c • z) := by
  intro t
  rw [map_smul, hz t, smul_comm]

/-- **Weights add under multiplication.** -/
theorem deningerGCAHomogeneous_mul {m n : ℕ} {z w : DeningerFreeGCA k G deg}
    (hz : DeningerGCAHomogeneous k deg m z) (hw : DeningerGCAHomogeneous k deg n w) :
    DeningerGCAHomogeneous k deg (m + n) (z * w) := by
  intro t
  rw [map_mul, hz t, hw t, smul_mul_smul_comm, pow_add]

/-- **A homogeneous element has the parity of its weight.**  This is what makes every statement
proved for elements of pure parity a statement about homogeneous elements. -/
theorem deningerGCAHomogeneous_involute {n : ℕ} {z : DeningerFreeGCA k G deg}
    (hz : DeningerGCAHomogeneous k deg n z) :
    deningerGCAInvolute k deg z = ((-1 : k) ^ n) • z := by
  rw [← deningerGCAWeight_neg_one]
  exact hz (-1)

variable (phi : G → DeningerFreeGCA k G deg)
variable (hphi : ∀ x y : G, deningerGCAι k deg x * phi y =
  ((-1 : k) ^ (deg x * (deg y + 1))) • (phi y * deningerGCAι k deg x))

/-- **The differential raises weight by one**, in the form of the weight action: the action
transported through the derivation picks up one factor of the parameter. -/
theorem deningerGCAWeight_oddDerivation
    (hhom : ∀ x : G, DeningerGCAHomogeneous k deg (deg x + 1) (phi x)) (t : k)
    (z : DeningerFreeGCA k G deg) :
    deningerGCAWeight k deg t (deningerGCAOddDerivation phi hphi z) =
      t • deningerGCAOddDerivation phi hphi (deningerGCAWeight k deg t z) := by
  induction z using deningerGCA_induction with
  | algMap r =>
    rw [deningerGCAOddDerivation_algebraMap, map_zero, AlgHom.commutes,
      deningerGCAOddDerivation_algebraMap, smul_zero]
  | gen x =>
    rw [deningerGCAOddDerivation_ι, hhom x t, deningerGCAWeight_ι, map_smul,
      deningerGCAOddDerivation_ι, smul_smul, pow_succ]
    congr 1
    ring
  | add a b ha hb => simp only [map_add, ha, hb, smul_add]
  | mul a b ha hb =>
    rw [deningerGCAOddDerivation_leibniz, map_add, map_mul, map_mul, ha, hb,
      deningerGCAWeight_involute, map_mul, deningerGCAOddDerivation_leibniz, smul_add,
      mul_smul_comm, smul_mul_assoc]

/-- **The differential of a homogeneous element is homogeneous of one weight higher.** -/
theorem deningerGCAHomogeneous_oddDerivation
    (hhom : ∀ x : G, DeningerGCAHomogeneous k deg (deg x + 1) (phi x)) {n : ℕ}
    {z : DeningerFreeGCA k G deg} (hz : DeningerGCAHomogeneous k deg n z) :
    DeningerGCAHomogeneous k deg (n + 1) (deningerGCAOddDerivation phi hphi z) := by
  intro t
  rw [deningerGCAWeight_oddDerivation phi hphi hhom t z, hz t, map_smul, smul_smul, pow_succ]
  congr 1
  ring

/-- **A degree-preserving map of generator sets intertwines the weight actions.** -/
theorem deningerGCAGenAlg_weight {G' : Type*} (deg' : G' → ℕ) (θ : G → G')
    (hdeg : ∀ x : G, deg' (θ x) = deg x) (t : k) (z : DeningerFreeGCA k G deg) :
    deningerGCAGenAlg k deg deg' θ hdeg (deningerGCAWeight k deg t z) =
      deningerGCAWeight k deg' t (deningerGCAGenAlg k deg deg' θ hdeg z) := by
  have h : (deningerGCAGenAlg k deg deg' θ hdeg).comp (deningerGCAWeight k deg t) =
      (deningerGCAWeight k deg' t).comp (deningerGCAGenAlg k deg deg' θ hdeg) := by
    refine deningerGCA_hom_ext fun x => ?_
    simp only [AlgHom.comp_apply, deningerGCAWeight_ι, map_smul, deningerGCAGenAlg_ι, hdeg]
  exact AlgHom.congr_fun h z

/-- **A degree-preserving map of generator sets preserves homogeneity and its weight.** -/
theorem deningerGCAGenAlg_homogeneous {G' : Type*} (deg' : G' → ℕ) (θ : G → G')
    (hdeg : ∀ x : G, deg' (θ x) = deg x) {n : ℕ} {z : DeningerFreeGCA k G deg}
    (hz : DeningerGCAHomogeneous k deg n z) :
    DeningerGCAHomogeneous k deg' n (deningerGCAGenAlg k deg deg' θ hdeg z) := by
  intro t
  rw [← deningerGCAGenAlg_weight, hz t, map_smul]

/-- The homogeneous elements. -/
def deningerGCAHomogeneousSet (k : Type*) [CommRing k] {G : Type*} (deg : G → ℕ) :
    Set (DeningerFreeGCA k G deg) :=
  {z | ∃ n : ℕ, DeningerGCAHomogeneous k deg n z}

theorem deningerGCA_span_homogeneous_mul_mem
    {b : DeningerFreeGCA k G deg} (hb : b ∈ Submodule.span k (deningerGCAHomogeneousSet k deg)) :
    ∀ a ∈ Submodule.span k (deningerGCAHomogeneousSet k deg),
      a * b ∈ Submodule.span k (deningerGCAHomogeneousSet k deg) := by
  induction hb using Submodule.span_induction with
  | mem y hy =>
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm⟩ := hx
      obtain ⟨n, hn⟩ := hy
      exact Submodule.subset_span ⟨m + n, deningerGCAHomogeneous_mul hm hn⟩
    | zero =>
      rw [zero_mul]
      exact Submodule.zero_mem _
    | add u v _ _ hu hv =>
      rw [add_mul]
      exact Submodule.add_mem _ hu hv
    | smul c u _ hu =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c hu
  | zero =>
    intro a _
    rw [mul_zero]
    exact Submodule.zero_mem _
  | add u v _ _ hu hv =>
    intro a ha
    rw [mul_add]
    exact Submodule.add_mem _ (hu a ha) (hv a ha)
  | smul c u _ hu =>
    intro a ha
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c (hu a ha)

/-- **The homogeneous elements span the algebra.**  Generators and scalars are homogeneous and
weights add under multiplication, so the span of the homogeneous elements is a subalgebra containing
the generators. -/
theorem deningerGCA_span_homogeneous_eq_top :
    Submodule.span k (deningerGCAHomogeneousSet k deg) = ⊤ := by
  have h : ∀ z : DeningerFreeGCA k G deg,
      z ∈ Submodule.span k (deningerGCAHomogeneousSet k deg) := by
    intro z
    induction z using deningerGCA_induction with
    | algMap r => exact Submodule.subset_span ⟨0, deningerGCAHomogeneous_algebraMap r⟩
    | gen x => exact Submodule.subset_span ⟨deg x, deningerGCAHomogeneous_ι x⟩
    | mul a b ha hb => exact deningerGCA_span_homogeneous_mul_mem hb a ha
    | add a b ha hb => exact Submodule.add_mem _ ha hb
  exact eq_top_iff.2 fun z _ => h z

/-- **Every element has homogeneous components.**  The indexed form of the spanning statement: an
element is the sum of a family whose `i`-th member is homogeneous of weight `i` and which vanishes
beyond a bound. -/
theorem deningerGCA_exists_homogeneous_components (z : DeningerFreeGCA k G deg) :
    ∃ (m : ℕ) (f : ℕ → DeningerFreeGCA k G deg),
      (∀ i, DeningerGCAHomogeneous k deg i (f i)) ∧ (∀ i, m ≤ i → f i = 0) ∧
        z = ∑ i ∈ Finset.range m, f i := by
  classical
  have hz : z ∈ Submodule.span k (deningerGCAHomogeneousSet k deg) := by
    rw [deningerGCA_span_homogeneous_eq_top]
    trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, hn⟩ := hx
    refine ⟨n + 1, fun i => if i = n then x else 0, ?_, ?_, ?_⟩
    · intro i
      by_cases h : i = n
      · subst h
        simpa using hn
      · simpa [h] using deningerGCAHomogeneous_zero (k := k) (deg := deg) i
    · intro i hi
      have hne : i ≠ n := by omega
      simp [hne]
    · simp
  | zero =>
    exact ⟨0, fun _ => 0, fun i => deningerGCAHomogeneous_zero i, fun _ _ => rfl, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨m₁, f, hf, hf0, rfl⟩ := ha
    obtain ⟨m₂, g, hg, hg0, rfl⟩ := hb
    refine ⟨max m₁ m₂, fun i => f i + g i,
      fun i => deningerGCAHomogeneous_add (hf i) (hg i), ?_, ?_⟩
    · intro i hi
      show f i + g i = 0
      rw [hf0 i (le_trans (le_max_left _ _) hi), hg0 i (le_trans (le_max_right _ _) hi), add_zero]
    · rw [Finset.sum_add_distrib]
      congr 1
      · refine Finset.sum_subset (fun i hi => ?_) (fun i _ hi => hf0 i ?_)
        · exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) (le_max_left m₁ m₂))
        · exact not_lt.1 fun hlt => hi (Finset.mem_range.2 hlt)
      · refine Finset.sum_subset (fun i hi => ?_) (fun i _ hi => hg0 i ?_)
        · exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) (le_max_right m₁ m₂))
        · exact not_lt.1 fun hlt => hi (Finset.mem_range.2 hlt)
  | smul c a _ ha =>
    obtain ⟨m, f, hf, hf0, rfl⟩ := ha
    refine ⟨m, fun i => c • f i, fun i => deningerGCAHomogeneous_smul c (hf i), ?_, ?_⟩
    · intro i hi
      show c • f i = 0
      rw [hf0 i hi, smul_zero]
    · rw [Finset.smul_sum]

/-- **Every element is a finite sum of homogeneous elements.** -/
theorem deningerGCA_exists_homogeneous_list (z : DeningerFreeGCA k G deg) :
    ∃ l : List (DeningerFreeGCA k G deg),
      (∀ w ∈ l, ∃ n : ℕ, DeningerGCAHomogeneous k deg n w) ∧ z = l.sum := by
  have hz : z ∈ Submodule.span k (deningerGCAHomogeneousSet k deg) := by
    rw [deningerGCA_span_homogeneous_eq_top]
    trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    refine ⟨[x], ?_, by simp⟩
    intro w hw
    rw [List.mem_singleton.1 hw]
    exact hx
  | zero => exact ⟨[], by simp, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨l₁, hl₁, rfl⟩ := ha
    obtain ⟨l₂, hl₂, rfl⟩ := hb
    refine ⟨l₁ ++ l₂, ?_, by rw [List.sum_append]⟩
    intro w hw
    rcases List.mem_append.1 hw with h | h
    · exact hl₁ w h
    · exact hl₂ w h
  | smul c a _ ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    refine ⟨l.map (fun w => c • w), ?_, ?_⟩
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
      obtain ⟨n, hn⟩ := hl v hv
      exact ⟨n, deningerGCAHomogeneous_smul c hn⟩
    · rw [← List.smul_sum]

end Weight

end HTGeometry
