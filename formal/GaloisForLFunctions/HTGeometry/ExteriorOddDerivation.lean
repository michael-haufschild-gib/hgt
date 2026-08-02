import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Odd derivations of an exterior algebra

An exterior algebra carries a grading involution, the algebra map negating the generators.  A
degree-raising odd derivation is a linear map obeying the graded Leibniz rule
`D (x * y) = σ x * D y + D x * y` for that involution.

Such a derivation is produced from its values on the generators whenever those values are central
and involution-invariant, by lifting the generators into the square-zero odd extension
`Λ(U) ⊕ ε Λ(U)`, in which `ε` anticommutes with odd elements and squares to zero.  The derivation
anticommutes with the involution, and squares to zero as soon as it kills the chosen generator
values.

* `deningerExteriorInvolute` : the grading involution.
* `DeningerOddExt` : the square-zero odd extension.
* `deningerOddDerivation`, `deningerOddDerivation_leibniz` : the derivation and its Leibniz rule.
* `deningerOddDerivation_involute`, `deningerOddDerivation_comp_self` : anticommutation with the
  involution, and `D² = 0`.
-/

namespace HTGeometry

open ExteriorAlgebra

section Involute

variable (k U : Type*) [CommRing k] [AddCommGroup U] [Module k U]

/-- The grading involution of an exterior algebra: the algebra map negating every generator. -/
def deningerExteriorInvolute : ExteriorAlgebra k U →ₐ[k] ExteriorAlgebra k U :=
  ExteriorAlgebra.lift k ⟨-(ExteriorAlgebra.ι k), fun m => by simp⟩

variable {k U}

@[simp]
theorem deningerExteriorInvolute_ι (u : U) :
    deningerExteriorInvolute k U (ι k u) = -ι k u := by
  rw [deningerExteriorInvolute, ExteriorAlgebra.lift_ι_apply]
  rfl

@[simp]
theorem deningerExteriorInvolute_involute (x : ExteriorAlgebra k U) :
    deningerExteriorInvolute k U (deningerExteriorInvolute k U x) = x := by
  have h : (deningerExteriorInvolute k U).comp (deningerExteriorInvolute k U) =
      AlgHom.id k (ExteriorAlgebra k U) := by
    ext u
    simp
  exact AlgHom.congr_fun h x

end Involute

section OddExtension

variable (k U : Type*) [CommRing k] [AddCommGroup U] [Module k U]

/-- The square-zero odd extension `Λ(U) ⊕ ε Λ(U)`: `ε` anticommutes with odd elements and squares
to zero, so the product is `(a, b) (a', b') = (a a', σ a * b' + b * a')`. -/
def DeningerOddExt : Type _ :=
  ExteriorAlgebra k U × ExteriorAlgebra k U

namespace DeningerOddExt

variable {k U}

instance : AddCommGroup (DeningerOddExt k U) :=
  inferInstanceAs (AddCommGroup (ExteriorAlgebra k U × ExteriorAlgebra k U))

instance : Module k (DeningerOddExt k U) :=
  inferInstanceAs (Module k (ExteriorAlgebra k U × ExteriorAlgebra k U))

/-- The even part of an element of the odd extension. -/
def even (x : DeningerOddExt k U) : ExteriorAlgebra k U := x.1

/-- The odd part of an element of the odd extension. -/
def odd (x : DeningerOddExt k U) : ExteriorAlgebra k U := x.2

/-- Construct an element of the odd extension from its two parts. -/
def mk (a b : ExteriorAlgebra k U) : DeningerOddExt k U := (a, b)

@[simp] theorem even_mk (a b : ExteriorAlgebra k U) : even (mk a b) = a := rfl
@[simp] theorem odd_mk (a b : ExteriorAlgebra k U) : odd (mk a b) = b := rfl

@[ext]
theorem ext {x y : DeningerOddExt k U} (h1 : even x = even y) (h2 : odd x = odd y) : x = y :=
  Prod.ext h1 h2

@[simp] theorem even_zero : even (0 : DeningerOddExt k U) = 0 := rfl
@[simp] theorem odd_zero : odd (0 : DeningerOddExt k U) = 0 := rfl
@[simp] theorem even_add (x y : DeningerOddExt k U) : even (x + y) = even x + even y := rfl
@[simp] theorem odd_add (x y : DeningerOddExt k U) : odd (x + y) = odd x + odd y := rfl
@[simp] theorem even_neg (x : DeningerOddExt k U) : even (-x) = -even x := rfl
@[simp] theorem odd_neg (x : DeningerOddExt k U) : odd (-x) = -odd x := rfl
@[simp] theorem even_smul (c : k) (x : DeningerOddExt k U) : even (c • x) = c • even x := rfl
@[simp] theorem odd_smul (c : k) (x : DeningerOddExt k U) : odd (c • x) = c • odd x := rfl

instance : One (DeningerOddExt k U) := ⟨mk 1 0⟩

instance : Mul (DeningerOddExt k U) :=
  ⟨fun x y => mk (even x * even y)
    (deningerExteriorInvolute k U (even x) * odd y + odd x * even y)⟩

@[simp] theorem even_one : even (1 : DeningerOddExt k U) = 1 := rfl
@[simp] theorem odd_one : odd (1 : DeningerOddExt k U) = 0 := rfl

@[simp]
theorem even_mul (x y : DeningerOddExt k U) : even (x * y) = even x * even y := rfl

@[simp]
theorem odd_mul (x y : DeningerOddExt k U) :
    odd (x * y) = deningerExteriorInvolute k U (even x) * odd y + odd x * even y := rfl

instance : Ring (DeningerOddExt k U) :=
  { (inferInstance : AddCommGroup (DeningerOddExt k U)) with
    mul := (· * ·)
    one := 1
    mul_assoc := fun x y z => by
      ext
      · exact mul_assoc _ _ _
      · show deningerExteriorInvolute k U (even x * even y) * odd z +
            (deningerExteriorInvolute k U (even x) * odd y + odd x * even y) * even z =
          deningerExteriorInvolute k U (even x) *
              (deningerExteriorInvolute k U (even y) * odd z + odd y * even z) +
            odd x * (even y * even z)
        rw [map_mul]
        noncomm_ring
    one_mul := fun x => by
      ext
      · exact one_mul _
      · show deningerExteriorInvolute k U 1 * odd x + 0 * even x = odd x
        rw [map_one]
        noncomm_ring
    mul_one := fun x => by
      ext
      · exact mul_one _
      · show deningerExteriorInvolute k U (even x) * 0 + odd x * 1 = odd x
        noncomm_ring
    left_distrib := fun x y z => by
      ext
      · exact mul_add _ _ _
      · show deningerExteriorInvolute k U (even x) * (odd y + odd z) +
            odd x * (even y + even z) =
          deningerExteriorInvolute k U (even x) * odd y + odd x * even y +
            (deningerExteriorInvolute k U (even x) * odd z + odd x * even z)
        noncomm_ring
    right_distrib := fun x y z => by
      ext
      · exact add_mul _ _ _
      · show deningerExteriorInvolute k U (even x + even y) * odd z +
            (odd x + odd y) * even z =
          deningerExteriorInvolute k U (even x) * odd z + odd x * even z +
            (deningerExteriorInvolute k U (even y) * odd z + odd y * even z)
        rw [map_add]
        noncomm_ring
    zero_mul := fun x => by
      ext
      · exact zero_mul _
      · show deningerExteriorInvolute k U 0 * odd x + 0 * even x = 0
        rw [map_zero]
        noncomm_ring
    mul_zero := fun x => by
      ext
      · exact mul_zero _
      · show deningerExteriorInvolute k U (even x) * 0 + odd x * 0 = 0
        simp }

instance : Algebra k (DeningerOddExt k U) where
  algebraMap :=
    { toFun := fun c => mk (algebraMap k (ExteriorAlgebra k U) c) 0
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
    · simp [Algebra.smul_def, AlgHom.commutes]

/-- The even part is an algebra map to the exterior algebra. -/
def evenHom : DeningerOddExt k U →ₐ[k] ExteriorAlgebra k U where
  toFun := even
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The odd part, as a linear map. -/
def oddLinear : DeningerOddExt k U →ₗ[k] ExteriorAlgebra k U where
  toFun := odd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end DeningerOddExt

end OddExtension

section Derivation

variable {k U : Type*} [CommRing k] [AddCommGroup U] [Module k U]
variable (phi : U →ₗ[k] ExteriorAlgebra k U)

/-- The generator map into the square-zero odd extension. -/
def deningerOddExtGen : U →ₗ[k] DeningerOddExt k U where
  toFun u := DeningerOddExt.mk (ι k u) (phi u)
  map_add' u v := by
    ext
    · show ι k (u + v) = ι k u + ι k v
      exact map_add _ u v
    · show phi (u + v) = phi u + phi v
      exact map_add _ u v
  map_smul' c u := by
    ext
    · show ι k (c • u) = c • ι k u
      exact map_smul _ c u
    · show phi (c • u) = c • phi u
      exact map_smul _ c u

variable (hcomm : ∀ (u : U) (x : ExteriorAlgebra k U), Commute (phi u) x)

include hcomm in
theorem deningerOddExtGen_sq_zero (u : U) :
    deningerOddExtGen phi u * deningerOddExtGen phi u = 0 := by
  ext
  · show ι k u * ι k u = 0
    exact ExteriorAlgebra.ι_sq_zero u
  · show deningerExteriorInvolute k U (ι k u) * phi u + phi u * ι k u = 0
    rw [deningerExteriorInvolute_ι, neg_mul, (hcomm u (ι k u)).eq]
    abel

/-- The algebra map into the square-zero odd extension determined by the generator values. -/
noncomputable def deningerOddDerivationHom :
    ExteriorAlgebra k U →ₐ[k] DeningerOddExt k U :=
  ExteriorAlgebra.lift k ⟨deningerOddExtGen phi, deningerOddExtGen_sq_zero phi hcomm⟩

/-- **The odd derivation** of the exterior algebra determined by its values on the generators. -/
noncomputable def deningerOddDerivation :
    ExteriorAlgebra k U →ₗ[k] ExteriorAlgebra k U :=
  (DeningerOddExt.oddLinear).comp
    (deningerOddDerivationHom phi hcomm).toLinearMap

/-- The even part of the lift is the identity. -/
theorem deningerOddDerivationHom_even (x : ExteriorAlgebra k U) :
    DeningerOddExt.even (deningerOddDerivationHom phi hcomm x) = x := by
  have h : (DeningerOddExt.evenHom).comp (deningerOddDerivationHom phi hcomm) =
      AlgHom.id k (ExteriorAlgebra k U) := by
    ext u
    show DeningerOddExt.even (deningerOddDerivationHom phi hcomm (ι k u)) = ι k u
    rw [deningerOddDerivationHom, ExteriorAlgebra.lift_ι_apply]
    rfl
  exact AlgHom.congr_fun h x

@[simp]
theorem deningerOddDerivation_ι (u : U) :
    deningerOddDerivation phi hcomm (ι k u) = phi u := by
  show DeningerOddExt.odd (deningerOddDerivationHom phi hcomm (ι k u)) = phi u
  rw [deningerOddDerivationHom, ExteriorAlgebra.lift_ι_apply]
  rfl

@[simp]
theorem deningerOddDerivation_one : deningerOddDerivation phi hcomm 1 = 0 := by
  show DeningerOddExt.odd (deningerOddDerivationHom phi hcomm 1) = 0
  rw [map_one]
  rfl

@[simp]
theorem deningerOddDerivation_algebraMap (c : k) :
    deningerOddDerivation phi hcomm (algebraMap k (ExteriorAlgebra k U) c) = 0 := by
  show DeningerOddExt.odd (deningerOddDerivationHom phi hcomm
    (algebraMap k (ExteriorAlgebra k U) c)) = 0
  rw [AlgHom.commutes]
  rfl

/-- **The graded Leibniz rule.** -/
theorem deningerOddDerivation_leibniz (x y : ExteriorAlgebra k U) :
    deningerOddDerivation phi hcomm (x * y) =
      deningerExteriorInvolute k U x * deningerOddDerivation phi hcomm y +
        deningerOddDerivation phi hcomm x * y := by
  have h : deningerOddDerivationHom phi hcomm (x * y) =
      deningerOddDerivationHom phi hcomm x * deningerOddDerivationHom phi hcomm y := map_mul _ _ _
  have := congrArg DeningerOddExt.odd h
  rw [DeningerOddExt.odd_mul, deningerOddDerivationHom_even phi hcomm x,
    deningerOddDerivationHom_even phi hcomm y] at this
  exact this

variable (heven : ∀ u : U, deningerExteriorInvolute k U (phi u) = phi u)

include heven in
/-- **The derivation anticommutes with the grading involution.** -/
theorem deningerOddDerivation_involute (x : ExteriorAlgebra k U) :
    deningerOddDerivation phi hcomm (deningerExteriorInvolute k U x) =
      -deningerExteriorInvolute k U (deningerOddDerivation phi hcomm x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => simp [AlgHom.commutes]
  | ι u => simp [heven u]
  | add a b ha hb => simp only [map_add, ha, hb, neg_add]
  | mul a b ha hb =>
    rw [map_mul, deningerOddDerivation_leibniz, ha, hb,
      deningerExteriorInvolute_involute, deningerOddDerivation_leibniz]
    rw [map_add, map_mul, map_mul, deningerExteriorInvolute_involute]
    noncomm_ring

include heven in
/-- **The derivation squares to zero** as soon as it kills the generator values. -/
theorem deningerOddDerivation_comp_self
    (hkill : ∀ u : U, deningerOddDerivation phi hcomm (phi u) = 0)
    (x : ExteriorAlgebra k U) :
    deningerOddDerivation phi hcomm (deningerOddDerivation phi hcomm x) = 0 := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => simp
  | ι u => rw [deningerOddDerivation_ι]; exact hkill u
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | mul a b ha hb =>
    rw [deningerOddDerivation_leibniz, map_add, deningerOddDerivation_leibniz,
      deningerOddDerivation_leibniz, ha, hb,
      deningerOddDerivation_involute phi hcomm heven a,
      deningerExteriorInvolute_involute]
    noncomm_ring

end Derivation

end HTGeometry
