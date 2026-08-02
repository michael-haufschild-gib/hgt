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

end HTGeometry
