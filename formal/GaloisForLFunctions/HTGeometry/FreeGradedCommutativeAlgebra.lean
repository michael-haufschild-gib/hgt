import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.Tactic.NoncommRing

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

end HTGeometry
