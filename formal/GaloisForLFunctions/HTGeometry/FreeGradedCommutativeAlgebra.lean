import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot

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

end HTGeometry
