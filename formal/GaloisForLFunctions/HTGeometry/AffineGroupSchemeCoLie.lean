import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.DualNumber

/-!
# The co-Lie module and the Lie algebra of an affine group scheme

An affine commutative group scheme over a commutative ring `R` is `Spec A` for a commutative
`R`-bialgebra `A` (a Hopf algebra when the group law has inverses).  Its identity section is the
counit `ε : A → R`, whose kernel is the *augmentation ideal* `I_A`.  The *co-Lie module* is

`ω_A = I_A / I_A²`,

an `R`-module, and the *Lie algebra* is its `R`-linear dual

`Lie A = Hom_R(ω_A, R)`,

the tangent space of `Spec A` at the identity.  This file builds that layer:

* `AffineGroupScheme.augIdeal`, `AffineGroupScheme.coLie`;
* `AffineGroupScheme.d`, the universal differential at the identity, with its Leibniz rule
  `d (a * b) = ε a • d b + ε b • d a` and surjectivity;
* `AffineGroupScheme.PointDerivation`, the derivations of `A` at the identity;
* `AffineGroupScheme.pointDerivationEquiv : PointDerivation R A ≃ₗ[R] Lie A`, the universal
  property of `ω_A`.

mathlib has bialgebras, Hopf algebras and `Ideal.Cotangent`, but neither the co-Lie module nor the
Lie algebra of an affine group scheme.

This is the first layer of the group-scheme foundations required by Sections 2 and 3 of Suzuki,
*Duality invariance of Faltings heights, Hodge line bundles and global periods* (arXiv:2504.04993):
the objects `Lie 𝒜`, `Lie 𝒩` and `det Lie` appearing throughout are built from exactly this
module.
-/

namespace GaloisForLFunctions.HTGeometry.AffineGroupScheme

open Coalgebra Bialgebra Ideal
open scoped TensorProduct

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A]

/-- The augmentation ideal of a bialgebra: the kernel of the counit, i.e. the ideal of the identity
section of the affine group scheme `Spec A`. -/
def augIdeal : Ideal A := RingHom.ker (Bialgebra.counitAlgHom R A).toRingHom

variable {R A}

@[simp] theorem mem_augIdeal {a : A} : a ∈ augIdeal R A ↔ (counit a : R) = 0 := Iff.rfl

theorem sub_algebraMap_counit_mem (a : A) :
    a - algebraMap R A (counit a : R) ∈ augIdeal R A := by
  rw [mem_augIdeal, map_sub]
  simp

variable (R A)

/-- The **co-Lie module** `ω_A = I/I²` of the affine group scheme `Spec A`. -/
abbrev coLie : Type _ := (augIdeal R A).Cotangent

/-- The **Lie algebra** of the affine group scheme `Spec A`: the `R`-linear dual of `ω_A`. -/
abbrev lieAlg : Type _ := coLie R A →ₗ[R] R

/-- The `R`-linear projection of `A` onto its augmentation ideal, `a ↦ a - ε a`. -/
def toAug : A →ₗ[R] (augIdeal R A) where
  toFun a := ⟨a - algebraMap R A (counit a : R), sub_algebraMap_counit_mem a⟩
  map_add' a b := by
    apply Subtype.ext
    show a + b - algebraMap R A (counit (a + b) : R)
      = (a - algebraMap R A (counit a : R)) + (b - algebraMap R A (counit b : R))
    rw [map_add, map_add]
    ring
  map_smul' r a := by
    apply Subtype.ext
    rw [RingHom.id_apply, Submodule.coe_smul_of_tower]
    show r • a - algebraMap R A (counit (r • a) : R) = r • (a - algebraMap R A (counit a : R))
    rw [map_smul, smul_eq_mul, map_mul, smul_sub, Algebra.smul_def, Algebra.smul_def]

@[simp] theorem toAug_coe (a : A) :
    ((toAug R A a : augIdeal R A) : A) = a - algebraMap R A (counit a : R) := rfl

/-- The **universal differential at the identity**, `d : A → ω_A`. -/
def d : A →ₗ[R] coLie R A :=
  ((augIdeal R A).toCotangent.restrictScalars R).comp (toAug R A)

variable {R A}

@[simp] theorem d_apply (a : A) :
    d R A a = (augIdeal R A).toCotangent (toAug R A a) := rfl

theorem d_algebraMap (r : R) : d R A (algebraMap R A r) = 0 := by
  rw [d_apply]
  have h : toAug R A (algebraMap R A r) = 0 := by
    apply Subtype.ext
    rw [toAug_coe]
    simp
  rw [h, map_zero]

@[simp] theorem d_one : d R A 1 = 0 := by
  simpa using d_algebraMap (R := R) (A := A) 1

theorem coe_smul_aug (r : R) (x : (augIdeal R A)) :
    ((r • x : augIdeal R A) : A) = algebraMap R A r * (x : A) := by
  rw [Submodule.coe_smul_of_tower, Algebra.smul_def]

/-- **Leibniz rule for the differential at the identity.** -/
theorem d_mul (a b : A) :
    d R A (a * b) = (counit a : R) • d R A b + (counit b : R) • d R A a := by
  have hlin : ∀ (r : R) (x : (augIdeal R A)),
      r • (augIdeal R A).toCotangent x = (augIdeal R A).toCotangent (r • x) :=
    fun r x => (LinearMap.map_smul_of_tower _ r x).symm
  rw [d_apply, d_apply, d_apply, hlin, hlin, ← map_add]
  refine (Ideal.toCotangent_eq _).mpr ?_
  have hdiff : ((toAug R A (a * b) : augIdeal R A) : A)
      - (((counit a : R) • toAug R A b + (counit b : R) • toAug R A a : augIdeal R A) : A)
      = (a - algebraMap R A (counit a : R)) * (b - algebraMap R A (counit b : R)) := by
    rw [AddSubmonoid.coe_add, coe_smul_aug, coe_smul_aug, toAug_coe, toAug_coe, toAug_coe,
      Bialgebra.counit_mul, map_mul]
    ring
  rw [hdiff, pow_two]
  exact Ideal.mul_mem_mul (sub_algebraMap_counit_mem a) (sub_algebraMap_counit_mem b)

theorem d_surjective : Function.Surjective (d R A) := by
  intro x
  obtain ⟨y, rfl⟩ := (augIdeal R A).toCotangent_surjective x
  refine ⟨(y : A), ?_⟩
  rw [d_apply]
  congr 1
  apply Subtype.ext
  rw [toAug_coe]
  have hy : (counit (y : A) : R) = 0 := y.2
  rw [hy]
  simp


/-! ### Point derivations and the universal property of `ω_A` -/

variable (R A)

/-- The `R`-module of **derivations at the identity** of `Spec A`: `R`-linear forms `D` on `A`
satisfying the Leibniz rule `D (a b) = ε a · D b + ε b · D a`. -/
def pointDerivations : Submodule R (A →ₗ[R] R) where
  carrier := {D | ∀ a b : A, D (a * b) = (counit a : R) * D b + (counit b : R) * D a}
  add_mem' {D E} hD hE a b := by
    simp only [LinearMap.add_apply]
    rw [hD a b, hE a b]
    ring
  zero_mem' a b := by simp
  smul_mem' c D hD a b := by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    rw [hD a b]
    ring

variable {R A}

theorem mem_pointDerivations {D : A →ₗ[R] R} :
    D ∈ pointDerivations R A
      ↔ ∀ a b : A, D (a * b) = (counit a : R) * D b + (counit b : R) * D a := Iff.rfl

theorem PointDerivation.map_one {D : A →ₗ[R] R} (hD : D ∈ pointDerivations R A) : D 1 = 0 := by
  have h := hD 1 1
  rw [mul_one, Bialgebra.counit_one, one_mul] at h
  exact left_eq_add.mp h

theorem PointDerivation.map_algebraMap {D : A →ₗ[R] R} (hD : D ∈ pointDerivations R A) (r : R) :
    D (algebraMap R A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, PointDerivation.map_one hD, smul_zero]

/-- A point derivation kills products of elements of the augmentation ideal. -/
theorem PointDerivation.apply_mul_aug {D : A →ₗ[R] R} (hD : D ∈ pointDerivations R A)
    (x y : (augIdeal R A)) : D ((x : A) * (y : A)) = 0 := by
  have hx : (counit (x : A) : R) = 0 := x.2
  have hy : (counit (y : A) : R) = 0 := y.2
  rw [hD, hx, hy, zero_mul, zero_mul, add_zero]

/-- **The universal property of the co-Lie module**: derivations at the identity are exactly the
`R`-linear forms on `ω_A`, i.e. the Lie algebra of `Spec A`. -/
noncomputable def pointDerivationEquiv : (pointDerivations R A) ≃ₗ[R] lieAlg R A where
  toFun D := Ideal.Cotangent.lift
    (((D : A →ₗ[R] R).comp ((augIdeal R A).subtype.restrictScalars R)))
    (fun x y => PointDerivation.apply_mul_aug D.2 x y)
  map_add' D E := by
    ext x
    obtain ⟨y, rfl⟩ := (augIdeal R A).toCotangent_surjective x
    rfl
  map_smul' c D := by
    ext x
    obtain ⟨y, rfl⟩ := (augIdeal R A).toCotangent_surjective x
    rfl
  invFun φ := ⟨φ.comp (d R A), by
    intro a b
    simp only [LinearMap.comp_apply, d_mul, map_add, map_smul, smul_eq_mul]⟩
  left_inv D := by
    apply Subtype.ext
    ext a
    show D.1 ((toAug R A a : augIdeal R A) : A) = D.1 a
    rw [toAug_coe, map_sub, PointDerivation.map_algebraMap D.2, sub_zero]
  right_inv φ := by
    ext x
    obtain ⟨y, rfl⟩ := (augIdeal R A).toCotangent_surjective x
    show φ (d R A (y : A)) = φ ((augIdeal R A).toCotangent y)
    congr 1
    rw [d_apply]
    congr 1
    apply Subtype.ext
    rw [toAug_coe]
    have hy : (counit (y : A) : R) = 0 := y.2
    rw [hy]
    simp


/-! ### Functoriality of the co-Lie module -/

variable {B : Type*} [CommRing B] [Bialgebra R B]

theorem counit_bialgHom (f : A →ₐc[R] B) (a : A) : (counit (f a) : R) = counit a :=
  congrFun (congrArg (fun g : A →ₗ[R] R => (g : A → R)) (CoalgHomClass.counit_comp f)) a

theorem augIdeal_le_comap (f : A →ₐc[R] B) :
    augIdeal R A ≤ (augIdeal R B).comap (f : A →ₐ[R] B).toRingHom := by
  intro a ha
  rw [Ideal.mem_comap, mem_augIdeal]
  show (counit (f a) : R) = 0
  rw [counit_bialgHom f a]
  exact ha

/-- A morphism of bialgebras induces an `R`-linear map of co-Lie modules. -/
noncomputable def coLieMap (f : A →ₐc[R] B) : coLie R A →ₗ[R] coLie R B :=
  Ideal.mapCotangent (augIdeal R A) (augIdeal R B) (f : A →ₐ[R] B) (augIdeal_le_comap f)

@[simp] theorem coLieMap_d (f : A →ₐc[R] B) (a : A) :
    coLieMap f (d R A a) = d R B (f a) := by
  rw [d_apply, coLieMap, Ideal.mapCotangent_toCotangent, d_apply]
  congr 1
  apply Subtype.ext
  show (f : A →ₐ[R] B) ((toAug R A a : augIdeal R A) : A) = _
  rw [toAug_coe, toAug_coe, map_sub, AlgHom.commutes, counit_bialgHom f a]
  rfl

/-! ### Tangent vectors as maps to the dual numbers -/

open TrivSqZeroExt in
/-- The algebra map to the dual numbers attached to a derivation at the identity:
`a ↦ ε a + (D a) ε`. -/
def toDualNumber (D : A →ₗ[R] R) (hD : D ∈ pointDerivations R A) : A →ₐ[R] DualNumber R where
  toFun a := ((counit a : R), D a)
  map_one' := by
    ext
    · exact Bialgebra.counit_one
    · exact PointDerivation.map_one hD
  map_mul' a b := by
    ext
    · exact Bialgebra.counit_mul a b
    · show D (a * b) = (counit a : R) • D b + MulOpposite.op (counit b : R) • D a
      rw [hD a b]
      simp [smul_eq_mul, mul_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  commutes' r := by
    ext
    · show (counit (algebraMap R A r) : R) = r
      simp
    · show D (algebraMap R A r) = 0
      exact PointDerivation.map_algebraMap hD r

@[simp] theorem toDualNumber_fst (D : A →ₗ[R] R) (hD : D ∈ pointDerivations R A) (a : A) :
    (toDualNumber D hD a).fst = (counit a : R) := rfl

@[simp] theorem toDualNumber_snd (D : A →ₗ[R] R) (hD : D ∈ pointDerivations R A) (a : A) :
    (toDualNumber D hD a).snd = D a := rfl

/-- **Tangent vectors at the identity are the `R`-algebra maps to the dual numbers lifting the
counit.** -/
noncomputable def dualNumberEquiv :
    (pointDerivations R A) ≃ {f : A →ₐ[R] DualNumber R // ∀ a, (f a).fst = (counit a : R)} where
  toFun D := ⟨toDualNumber D.1 D.2, fun a => rfl⟩
  invFun f := ⟨{ toFun := fun a => (f.1 a).snd
                 map_add' := fun a b => by rw [map_add]; rfl
                 map_smul' := fun r a => by rw [map_smul]; rfl }, by
    intro a b
    show ((f.1) (a * b)).snd = (counit a : R) * ((f.1) b).snd + (counit b : R) * ((f.1) a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, f.2 a, f.2 b]
    simp [smul_eq_mul, mul_comm]⟩
  left_inv D := by apply Subtype.ext; rfl
  right_inv f := by
    apply Subtype.ext
    apply AlgHom.ext
    intro a
    apply TrivSqZeroExt.ext
    · exact (f.2 a).symm
    · rfl


/-! ### Primitive elements

The primitive elements of `A` are the Lie algebra of the Cartier dual of `Spec A`.  They live
inside the augmentation ideal. -/

variable (R A)

/-- The **primitive elements** of a bialgebra: `Δ x = x ⊗ 1 + 1 ⊗ x`. -/
def primitives : Submodule R A where
  carrier := {x : A | comul x = x ⊗ₜ[R] (1 : A) + (1 : A) ⊗ₜ[R] x}
  add_mem' {x y} hx hy := by
    show comul (x + y) = _
    rw [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  zero_mem' := by
    show comul (0 : A) = _
    simp
  smul_mem' c x hx := by
    show comul (c • x) = _
    rw [map_smul, hx, smul_add, TensorProduct.smul_tmul', TensorProduct.tmul_smul]

variable {R A}

theorem mem_primitives {x : A} :
    x ∈ primitives R A ↔ comul x = x ⊗ₜ[R] (1 : A) + (1 : A) ⊗ₜ[R] x := Iff.rfl

/-- A primitive element is killed by the counit. -/
theorem counit_eq_zero_of_mem_primitives {x : A} (hx : x ∈ primitives R A) :
    (counit x : R) = 0 := by
  have h := Coalgebra.rTensor_counit_comul (R := R) x
  rw [mem_primitives.mp hx, map_add] at h
  have h1 : (LinearMap.rTensor A (counit : A →ₗ[R] R)) (x ⊗ₜ[R] (1 : A))
      = (counit x : R) ⊗ₜ[R] (1 : A) := rfl
  have h2 : (LinearMap.rTensor A (counit : A →ₗ[R] R)) ((1 : A) ⊗ₜ[R] x)
      = (counit (1 : A) : R) ⊗ₜ[R] x := rfl
  rw [h1, h2, Bialgebra.counit_one] at h
  have h3 : (counit x : R) ⊗ₜ[R] (1 : A) = (0 : TensorProduct R R A) := by
    have := congrArg (fun y => y - (1 : R) ⊗ₜ[R] x) h
    simpa using this
  have h4 := congrArg (TensorProduct.lid R A) h3
  simp only [TensorProduct.lid_tmul, map_zero] at h4
  have h5 : algebraMap R A (counit x : R) = 0 := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact h4
  exact Bialgebra.algebraMap_injective (R := R) (A := A) (by rw [h5, map_zero])

theorem primitives_le_augIdeal :
    primitives R A ≤ (augIdeal R A).restrictScalars R := fun _ hx =>
  counit_eq_zero_of_mem_primitives hx


end GaloisForLFunctions.HTGeometry.AffineGroupScheme
