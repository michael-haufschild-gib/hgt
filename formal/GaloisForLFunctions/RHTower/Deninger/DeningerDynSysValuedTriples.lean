import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# The local ring of the closure of a point, and the `𝒪`-valued triples

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Definitions 13.2
(`t42nn`) and 14.1 (`t121`).

For a scheme `X` and points `x , y` with `y ∈ closure {x}`, the specialisation map
`𝒪_{X,y} → 𝒪_{X,x}` composed with the residue map of `x` has a prime kernel `𝔭`, and

`𝒪_{closure {x} , y} = 𝒪_{X,y} / 𝔭`

is the local ring at `y` of the reduced closure of `x`; it is a domain, and it still maps onto the
residue field `κ (y)` because `𝔭` lies in the maximal ideal of `𝒪_{X,y}`.

Deninger's `𝒪`-valued points of `W_rat (X)` are triples `(x , y , P_y)` with `P_y` a pointed
multiplicative map on this ring which is nonzero away from `0` and whose reduction modulo the
maximal ideal of `𝒪` depends only on the value at `y`.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

variable {X : Scheme.{u}} {x y : X}

/-- The prime of `𝒪_{X,y}` cutting out the closure of `x`. -/
def deningerClosureIdeal (h : x ⤳ y) : Ideal (X.presheaf.stalk y) :=
  RingHom.ker (((X.presheaf.stalkSpecializes h) ≫ X.residue x).hom)

instance deningerClosureIdeal_isPrime (h : x ⤳ y) : (deningerClosureIdeal h).IsPrime :=
  RingHom.ker_isPrime _

/-- The prime cutting out the closure of `x` lies in the maximal ideal of `𝒪_{X,y}`. -/
theorem deningerClosureIdeal_le_maximalIdeal (h : x ⤳ y) :
    deningerClosureIdeal h ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
  IsLocalRing.le_maximalIdeal (deningerClosureIdeal_isPrime h).ne_top

/-- **Deninger, §13.**  The local ring `𝒪_{closure {x} , y}` of the closure of `x` at a
specialisation `y`. -/
def DeningerClosureLocalRing (h : x ⤳ y) : Type u :=
  (X.presheaf.stalk y) ⧸ deningerClosureIdeal h

namespace DeningerClosureLocalRing

variable (h : x ⤳ y)

instance : CommRing (DeningerClosureLocalRing h) :=
  inferInstanceAs (CommRing ((X.presheaf.stalk y) ⧸ deningerClosureIdeal h))

instance : IsDomain (DeningerClosureLocalRing h) :=
  Ideal.Quotient.isDomain _

/-- The quotient map `𝒪_{X,y} → 𝒪_{closure {x} , y}`. -/
def mk : X.presheaf.stalk y →+* DeningerClosureLocalRing h :=
  Ideal.Quotient.mk (deningerClosureIdeal h)

theorem mk_surjective : Function.Surjective (mk h) :=
  Ideal.Quotient.mk_surjective

end DeningerClosureLocalRing

/-- The evaluation `𝒪_{closure {x} , y} → κ (y)`. -/
noncomputable def deningerClosureResidue (h : x ⤳ y) :
    DeningerClosureLocalRing h →+* X.residueField y :=
  Ideal.Quotient.lift (deningerClosureIdeal h) (X.residue y).hom (by
    intro a ha
    have hmem : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
      deningerClosureIdeal_le_maximalIdeal h ha
    exact (IsLocalRing.residue_eq_zero_iff (R := X.presheaf.stalk y) a).2 hmem)

@[simp] theorem deningerClosureResidue_mk (h : x ⤳ y) (a : X.presheaf.stalk y) :
    deningerClosureResidue h (DeningerClosureLocalRing.mk h a) = (X.residue y).hom a := rfl

/-! ## Definition 14.1: the `𝒪`-valued triples -/

/-- **Deninger, Definition 14.1 (`t121`).**  An `𝒪`-valued point of `W_rat (X)`: a point `x`, a
specialisation `y ∈ closure {x}`, and a pointed multiplicative map on the local ring of the closure
of `x` at `y` which is nonzero off `0` and whose residue depends only on the value at `y`. -/
structure DeningerValuedTriple (X : Scheme.{u}) (O : Type u) [CommRing O] [IsLocalRing O] where
  /-- The generic point. -/
  gen : X
  /-- The specialisation. -/
  spec : X
  /-- `spec` lies in the closure of `gen`. -/
  specializes : gen ⤳ spec
  /-- The pointed multiplicative map on `𝒪_{closure {gen} , spec}`. -/
  map : DeningerClosureLocalRing specializes →*₀ O
  /-- Condition 1): the map is nonzero off `0`. -/
  map_ne_zero : ∀ f : DeningerClosureLocalRing specializes, f ≠ 0 → map f ≠ 0
  /-- Condition 2): the residue of the value depends only on the value at `spec`. -/
  map_residue : ∀ f g : DeningerClosureLocalRing specializes,
    deningerClosureResidue specializes f = deningerClosureResidue specializes g →
    map f - map g ∈ IsLocalRing.maximalIdeal O

namespace DeningerValuedTriple

variable {O : Type u} [CommRing O] [IsLocalRing O]

/-- The zero set of the map of an `𝒪`-valued triple is exactly `{0}`. -/
theorem map_eq_zero_iff (P : DeningerValuedTriple X O) (f : DeningerClosureLocalRing P.specializes) :
    P.map f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    by_contra hne
    exact P.map_ne_zero f hne hf
  · rintro rfl
    exact map_zero P.map

/-- The values of the map outside the preimage of the maximal ideal are units. -/
theorem isUnit_map_of_residue_ne_zero (P : DeningerValuedTriple X O)
    {f : DeningerClosureLocalRing P.specializes}
    (hf : P.map f ∉ IsLocalRing.maximalIdeal O) : IsUnit (P.map f) :=
  IsLocalRing.notMem_maximalIdeal.1 hf

end DeningerValuedTriple

end

end RHTower

namespace RHTower

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

open Classical in
/-- **Deninger, §13.**  The extension by zero of a character of the units of a field: a pointed
multiplicative map on the whole field. -/
def deningerCharExtendByZero {k C : Type*} [Field k] [Field C] (χ : kˣ →* Cˣ) : k →*₀ C where
  toFun a := if h : a = 0 then 0 else (χ (Units.mk0 a h) : C)
  map_zero' := by simp
  map_one' := by
    rw [dif_neg (one_ne_zero (α := k))]
    have : Units.mk0 (1 : k) one_ne_zero = 1 := Units.ext rfl
    rw [this, map_one]
    rfl
  map_mul' a b := by
    by_cases ha : a = 0
    · subst ha; simp
    by_cases hb : b = 0
    · subst hb; simp
    rw [dif_neg ha, dif_neg hb, dif_neg (mul_ne_zero ha hb)]
    have hmk : Units.mk0 (a * b) (mul_ne_zero ha hb) = Units.mk0 a ha * Units.mk0 b hb :=
      Units.ext rfl
    rw [hmk, map_mul]
    rfl

@[simp] theorem deningerCharExtendByZero_apply_ne_zero {k C : Type*} [Field k] [Field C]
    (χ : kˣ →* Cˣ) {a : k} (h : a ≠ 0) :
    deningerCharExtendByZero χ a = (χ (Units.mk0 a h) : C) := dif_neg h

theorem deningerCharExtendByZero_eq_zero_iff {k C : Type*} [Field k] [Field C]
    (χ : kˣ →* Cˣ) (a : k) : deningerCharExtendByZero χ a = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra hne
    rw [deningerCharExtendByZero_apply_ne_zero χ hne] at h
    exact (χ (Units.mk0 a hne)).ne_zero h
  · rintro rfl
    exact map_zero _

/-- **Deninger, Definition 13.2 (`t42nn`).**  An `𝒪`-valued point of `W_rat (X)` in the character
description: a point `x`, a specialisation `y ∈ closure {x}`, a character of `κ (x)ˣ` with values
in the units of the fraction field of `𝒪`, and pointed multiplicative maps making Deninger's square
commute. -/
structure DeningerValuedCharTriple (X : Scheme.{u}) (O : Type u) [CommRing O] [IsDomain O]
    [IsLocalRing O] where
  /-- The generic point. -/
  gen : X
  /-- The specialisation. -/
  spec : X
  /-- `spec` lies in the closure of `gen`. -/
  specializes : gen ⤳ spec
  /-- The character of the residue field at the generic point. -/
  chr : (X.residueField gen)ˣ →* (FractionRing O)ˣ
  /-- The pointed multiplicative map on the local ring at the specialisation. -/
  localMap : X.presheaf.stalk spec →*₀ O
  /-- The induced pointed multiplicative map on the residue field at the specialisation. -/
  residueMap : X.residueField spec →*₀ IsLocalRing.ResidueField O
  /-- The lower square: the character recovers the local map after inverting. -/
  comm_gen : ∀ a : X.presheaf.stalk spec,
    algebraMap O (FractionRing O) (localMap a)
      = deningerCharExtendByZero chr
          ((X.residue gen).hom ((X.presheaf.stalkSpecializes specializes).hom a))
  /-- The upper square: the local map reduces to the residue map. -/
  comm_spec : ∀ a : X.presheaf.stalk spec,
    IsLocalRing.residue O (localMap a) = residueMap ((X.residue spec).hom a)

namespace DeningerValuedCharTriple

variable {X : Scheme.{u}} {O : Type u} [CommRing O] [IsDomain O] [IsLocalRing O]

/-- The local map of an `𝒪`-valued character triple vanishes exactly on the prime cutting out the
closure of the generic point. -/
theorem localMap_eq_zero_iff (P : DeningerValuedCharTriple X O)
    (a : X.presheaf.stalk P.spec) :
    P.localMap a = 0 ↔ a ∈ deningerClosureIdeal P.specializes := by
  have h := P.comm_gen a
  constructor
  · intro ha
    rw [ha, map_zero] at h
    have := (deningerCharExtendByZero_eq_zero_iff P.chr _).1 h.symm
    exact this
  · intro ha
    have hzero : (X.residue P.gen).hom
        ((X.presheaf.stalkSpecializes P.specializes).hom a) = 0 := ha
    rw [hzero, map_zero] at h
    exact (IsFractionRing.to_map_eq_zero_iff (R := O)).1 h

end DeningerValuedCharTriple

end

end RHTower
