import Mathlib.Algebra.Group.PUnit
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The multiplicative core of the field with one element

This file formalizes the doctrine-independent core of `F₁` used by monoid schemes.
It does not assert that `F₁` is a ring, nor identify richer blueprint, band, semiring,
lambda-ring, generalized-ring, spectral, or analytic enhancements with this core.

The base object is the commutative monoid with zero `WithZero PUnit`, whose elements
are exactly `0` and `1`. Contracted scalar extension discards the absorbing-zero basis
vector, so it is the monoid algebra of the nonzero part `PUnit`.
-/

namespace GaloisForLFunctions.HTGeometry.FieldOneCore

/-- The two-element commutative monoid with zero forming the multiplicative core of `F₁`. -/
abbrev FieldOne := WithZero PUnit

/-- The unique monoid homomorphism from the one-element nonzero part of `F₁`. -/
def punitMonoidHom (A : Type*) [CommMonoidWithZero A] : PUnit →* A where
  toFun := fun _ => 1
  map_one' := rfl
  map_mul' := by
    intro _ _
    simp

/-- The canonical morphism from `F₁` to any commutative monoid with zero. -/
def fieldOneTo (A : Type*) [CommMonoidWithZero A] : FieldOne →*₀ A :=
  WithZero.lift' (punitMonoidHom A)

/-- `F₁` is initial among commutative monoids with zero. -/
theorem fieldOne_hom_unique {A : Type*} [CommMonoidWithZero A]
    (f : FieldOne →*₀ A) : f = fieldOneTo A := by
  apply WithZero.monoidWithZeroHom_ext
  ext x
  cases x
  change f (1 : FieldOne) = 1
  exact map_one f

/-- Every element of the multiplicative core is either zero or one. -/
theorem fieldOne_eq_zero_or_one (x : FieldOne) : x = 0 ∨ x = 1 := by
  induction x using WithZero.recZeroCoe with
  | zero => exact Or.inl rfl
  | coe x =>
      right
      congr

/-- Every nonzero element of `F₁` is a unit: the precise non-additive field property. -/
theorem fieldOne_isUnit_of_ne_zero {x : FieldOne} (hx : x ≠ 0) : IsUnit x := by
  rcases fieldOne_eq_zero_or_one x with h | h
  · exact False.elim (hx h)
  · simp [h]

/-! ## Contracted scalar extension -/

/-- Contracted scalar extension of `F₁` to `R`.

The absorbing-zero basis vector has already been killed, leaving the monoid algebra
of the one-element nonzero part. This is deliberately not `MonoidAlgebra R FieldOne`.
-/
abbrev ContractedBaseChange (R : Type*) [Semiring R] := MonoidAlgebra R PUnit

/-- Contracted scalar extension of `F₁` to any semiring `R` is canonically `R`. -/
noncomputable def contractedBaseChangeEquiv (R : Type*) [Semiring R] :
    ContractedBaseChange R ≃+* R :=
  MonoidAlgebra.uniqueRingEquiv PUnit

/-! ## Modules as pointed sets -/

/-- In every `F₁`-action, a nonzero scalar acts as the identity. -/
theorem fieldOne_nonzero_smul {M : Type*} [Zero M] [MulActionWithZero FieldOne M]
    {a : FieldOne} (ha : a ≠ 0) (m : M) : a • m = m := by
  rcases fieldOne_eq_zero_or_one a with h | h
  · exact False.elim (ha h)
  · simp [h]

/-- Every pointed type admits the forced `F₁`-action: zero kills and one fixes. -/
@[reducible] def fieldOneMulActionWithZero (M : Type*) [Zero M] :
    MulActionWithZero FieldOne M where
  smul a m := WithZero.recZeroCoe 0 (fun _ => m) a
  one_smul := by
    intro m
    rfl
  mul_smul := by
    intro a b m
    induction a using WithZero.recZeroCoe with
    | zero => rfl
    | coe a =>
        induction b using WithZero.recZeroCoe with
        | zero => rfl
        | coe b => rfl
  zero_smul := by
    intro m
    rfl
  smul_zero := by
    intro a
    induction a using WithZero.recZeroCoe <;> rfl

/-- Every basepoint-preserving map between `F₁`-modules is equivariant. -/
theorem ZeroHom.map_fieldOne_smul {M N : Type*} [Zero M] [Zero N]
    [MulActionWithZero FieldOne M] [MulActionWithZero FieldOne N]
    (f : ZeroHom M N) (a : FieldOne) (m : M) : f (a • m) = a • f m := by
  rcases fieldOne_eq_zero_or_one a with h | h
  · simp [h, map_zero f]
  · simp [h]

/-- Every equivariant function between `F₁`-modules preserves the basepoint. -/
theorem zero_preserving_of_fieldOne_equivariant {M N : Type*} [Zero M] [Zero N]
    [MulActionWithZero FieldOne M] [MulActionWithZero FieldOne N]
    (f : M → N) (hf : ∀ (a : FieldOne) (m : M), f (a • m) = a • f m) : f 0 = 0 := by
  simpa using hf (0 : FieldOne) (0 : M)

/-! ## Free modules and their automorphisms -/

/-- Free `F₁`-module on `I`: a copy of `I` plus a disjoint basepoint. -/
abbrev FreeFieldOneModule (I : Type*) := WithZero I

/-- Extend a function from generators to the unique basepoint-preserving map. -/
def freeFieldOneModuleLift {I M : Type*} [Zero M] (f : I → M) :
    ZeroHom (FreeFieldOneModule I) M where
  toFun := WithZero.recZeroCoe 0 f
  map_zero' := rfl

/-- Universal property of the free `F₁`-module. -/
def freeFieldOneModuleHomEquiv {I M : Type*} [Zero M] :
    (I → M) ≃ ZeroHom (FreeFieldOneModule I) M where
  toFun := freeFieldOneModuleLift
  invFun := fun f i => f (i : WithZero I)
  left_inv := by
    intro f
    rfl
  right_inv := by
    intro f
    ext x
    induction x using WithZero.recZeroCoe with
    | zero => exact (map_zero f).symm
    | coe x => rfl

/-- Group of pointed automorphisms of a free `F₁`-module. -/
def FreeFieldOneModuleAut (I : Type*) : Subgroup (Equiv.Perm (WithZero I)) where
  carrier := {e | e 0 = 0}
  one_mem' := rfl
  mul_mem' := by
    intro e f he hf
    change e (f 0) = 0
    rw [hf, he]
  inv_mem' := by
    intro e he
    change e.symm 0 = 0
    apply e.injective
    simpa using he.symm

/-- Extend a permutation of the basis by fixing the basepoint. -/
def permToFreeFieldOneModuleAut (I : Type*) :
    Equiv.Perm I →* FreeFieldOneModuleAut I where
  toFun σ := ⟨Equiv.optionCongr σ, rfl⟩
  map_one' := by
    apply Subtype.ext
    ext x
    cases x <;> rfl
  map_mul' := by
    intro σ τ
    apply Subtype.ext
    ext x
    cases x <;> rfl

/-- Restrict an equivalence fixing zero to the nonzero summands. -/
def unzeroEquivOfFixZero {I J : Type*} (e : WithZero I ≃ WithZero J)
    (he : e 0 = 0) : I ≃ J where
  toFun i := (e (i : WithZero I)).unzero (by
    intro h
    have : (i : WithZero I) = 0 := e.injective (by simpa [he] using h)
    exact WithZero.coe_ne_zero this)
  invFun j := (e.symm (j : WithZero J)).unzero (by
    intro h
    have he' : e.symm 0 = 0 := by
      apply e.injective
      simp [he]
    have : (j : WithZero J) = 0 := e.symm.injective (by simpa [he'] using h)
    exact WithZero.coe_ne_zero this)
  left_inv i := by
    apply WithZero.coe_injective
    simp
  right_inv j := by
    apply WithZero.coe_injective
    simp

/-- Extension by zero is a bijection onto all pointed automorphisms. -/
theorem permToFreeFieldOneModuleAut_bijective (I : Type*) :
    Function.Bijective (permToFreeFieldOneModuleAut I) := by
  constructor
  · intro σ τ h
    apply Equiv.ext
    intro i
    have h' := congrArg (fun e : FreeFieldOneModuleAut I =>
      (e.1 : WithZero I ≃ WithZero I) (i : WithZero I)) h
    exact WithZero.coe_injective h'
  · intro e
    let σ : Equiv.Perm I := unzeroEquivOfFixZero e.1 e.2
    refine ⟨σ, ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    intro x
    induction x using WithZero.recZeroCoe with
    | zero => exact e.2.symm
    | coe i =>
        change ((σ i : I) : WithZero I) = e.1 (i : WithZero I)
        dsimp [σ, unzeroEquivOfFixZero]
        exact WithZero.coe_unzero _

/-- `GL_I(F₁)` is canonically the permutation group of `I`. -/
noncomputable def freeFieldOneModuleAutMulEquiv (I : Type*) :
    Equiv.Perm I ≃* FreeFieldOneModuleAut I :=
  MulEquiv.ofBijective (permToFreeFieldOneModuleAut I)
    (permToFreeFieldOneModuleAut_bijective I)

/-! ## Module/Tits projective points -/

/-- Nonzero vectors of the free module are canonically its basis. -/
def nonzeroFreeFieldOneModuleEquiv (I : Type*) :
    {x : FreeFieldOneModule I // x ≠ 0} ≃ I where
  toFun x := x.1.unzero x.2
  invFun i := ⟨(i : WithZero I), WithZero.coe_ne_zero⟩
  left_inv x := by
    apply Subtype.ext
    exact WithZero.coe_unzero x.2
  right_inv i := by
    simp

/-- The number of nonzero free-module vectors equals the cardinality of the basis. -/
theorem card_nonzeroFreeFieldOneModule (I : Type*) :
    Nat.card {x : FreeFieldOneModule I // x ≠ 0} = Nat.card I :=
  Nat.card_congr (nonzeroFreeFieldOneModuleEquiv I)

/-- Under the module/Tits convention, `P^(n-1)(F₁)` has exactly `n` points. -/
theorem card_projectiveModulePoints (n : ℕ) :
    Nat.card {x : FreeFieldOneModule (Fin n) // x ≠ 0} = n := by
  rw [card_nonzeroFreeFieldOneModule]
  exact Nat.card_fin n

/-! ## The total-addition fork -/

/-- On a two-element semiring, `1 + 1` must be zero or one. -/
theorem twoElement_one_add_one {R : Type*} [Semiring R]
    (hR : ∀ x : R, x = 0 ∨ x = 1) :
    (1 : R) + 1 = 0 ∨ (1 : R) + 1 = 1 :=
  hR ((1 : R) + 1)

/-- The characteristic-two branch forces every element to be self-inverse. -/
theorem add_self_eq_zero_of_twoElement {R : Type*} [Semiring R]
    (hR : ∀ x : R, x = 0 ∨ x = 1) (hadd : 1 + 1 = (0 : R)) :
    ∀ x : R, x + x = 0 := by
  intro x
  rcases hR x with h | h
  · simp [h]
  · simpa [h] using hadd

/-- The Boolean branch forces idempotent addition. -/
theorem add_self_eq_self_of_twoElement {R : Type*} [Semiring R]
    (hR : ∀ x : R, x = 0 ∨ x = 1) (hadd : 1 + 1 = (1 : R)) :
    ∀ x : R, x + x = x := by
  intro x
  rcases hR x with h | h
  · simp [h]
  · simpa [h] using hadd

/-- Every total semiring addition on the two-element multiplicative core lies in one
of two branches: characteristic two or idempotent addition. -/
theorem twoElement_additiveFork {R : Type*} [Semiring R] [Nontrivial R]
    (hR : ∀ x : R, x = 0 ∨ x = 1) :
    (((1 : R) + 1 = 0) ∧ ∀ x : R, x + x = 0) ∨
      (((1 : R) + 1 = 1) ∧ ∀ x : R, x + x = x) := by
  rcases twoElement_one_add_one hR with h | h
  · exact Or.inl ⟨h, add_self_eq_zero_of_twoElement hR h⟩
  · exact Or.inr ⟨h, add_self_eq_self_of_twoElement hR h⟩

/-- The characteristic-two and Boolean branches cannot both hold in a nontrivial semiring. -/
theorem twoElement_additiveFork_disjoint {R : Type*} [Semiring R] [Nontrivial R] :
    ¬(((1 : R) + 1 = 0) ∧ (1 : R) + 1 = 1) := by
  rintro ⟨hzero, hone⟩
  exact zero_ne_one (hzero.symm.trans hone)

end GaloisForLFunctions.HTGeometry.FieldOneCore
