import Mathlib.Algebra.Group.AddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Spherical field-one exponents as Weyl character multipliers

An additive character `ψ` on a commutative ring turns every exponent `r` into
the shifted character `x ↦ ψ (r * x)`.  Addition of exponents becomes
multiplication of characters.  This is the algebraic core of the correctly
typed comparison from a spherical stalk to analytic Weyl multipliers.

The construction preserves roots exactly and is faithful over a field for
every nontrivial character.  It also acts by invertible linear multiplication
operators on the full function space.  No topology, Schwartz preservation,
Haar measure, positivity, or RH statement is asserted in this module.
-/

namespace GaloisForLFunctions.HTGeometry.FieldOneCore

noncomputable section

variable {R C : Type*} [CommRing R] [CommRing C]

/-- Multiplicative representation of additive exponents by shifts of an
additive character. -/
def fieldOneWeylCharacterRepresentation (ψ : AddChar R C) :
    Multiplicative R →* AddChar R C where
  toFun r := AddChar.mulShift ψ r.toAdd
  map_one' := AddChar.mulShift_zero ψ
  map_mul' r s := (AddChar.mulShift_mul ψ r.toAdd s.toAdd).symm

@[simp]
theorem fieldOneWeylCharacterRepresentation_apply
    (ψ : AddChar R C) (r x : R) :
    fieldOneWeylCharacterRepresentation ψ (Multiplicative.ofAdd r) x =
      ψ (r * x) :=
  rfl

/-- The `n`-th power of the character at exponent `r` is the character at
the additive multiple `n • r`. -/
theorem fieldOneWeylCharacterRepresentation_pow
    (ψ : AddChar R C) (r : R) (n : ℕ) :
    (fieldOneWeylCharacterRepresentation ψ (Multiplicative.ofAdd r)) ^ n =
      fieldOneWeylCharacterRepresentation ψ
        (Multiplicative.ofAdd (n • r)) := by
  rw [← map_pow, ← ofAdd_nsmul]

/-- Any specified additive `n`-th root becomes a multiplicative `n`-th root
of the corresponding Weyl character. -/
theorem fieldOneWeylCharacterRepresentation_root
    (ψ : AddChar R C) {r h : R} {n : ℕ} (hr : n • r = h) :
    (fieldOneWeylCharacterRepresentation ψ (Multiplicative.ofAdd r)) ^ n =
      fieldOneWeylCharacterRepresentation ψ
        (Multiplicative.ofAdd h) := by
  rw [fieldOneWeylCharacterRepresentation_pow, hr]

/-- A nontrivial character separates two exponents whenever their difference
is a unit.  This is the semilocal diagonal-faithfulness mechanism. -/
theorem fieldOneWeylCharacterRepresentation_eq_of_sub_isUnit
    (ψ : AddChar R C) (hψ : ψ ≠ 1) {r s : R}
    (hrs : IsUnit (r - s))
    (h :
      fieldOneWeylCharacterRepresentation ψ (Multiplicative.ofAdd r) =
        fieldOneWeylCharacterRepresentation ψ (Multiplicative.ofAdd s)) :
    r = s := by
  have hrs_eq : AddChar.mulShift ψ r = AddChar.mulShift ψ s := h
  have hshift : AddChar.mulShift ψ (r - s) = 1 := by
    calc
      AddChar.mulShift ψ (r - s) =
          AddChar.mulShift ψ r * AddChar.mulShift ψ (-s) := by
            rw [sub_eq_add_neg, AddChar.mulShift_mul]
      _ = AddChar.mulShift ψ s * AddChar.mulShift ψ (-s) := by
        rw [hrs_eq]
      _ = AddChar.mulShift ψ (s + -s) :=
        AddChar.mulShift_mul ψ s (-s)
      _ = 1 := by simp
  exact False.elim
    (hψ ((AddChar.mulShift_unit_eq_one_iff ψ hrs).mp hshift))

/-- Over a field, every nontrivial additive character gives a faithful
representation of all additive exponents. -/
theorem fieldOneWeylCharacterRepresentation_injective_of_field
    {F : Type*} [Field F] (ψ : AddChar F C) (hψ : ψ ≠ 1) :
    Function.Injective (fieldOneWeylCharacterRepresentation ψ) := by
  intro r s h
  change r.toAdd = s.toAdd
  exact
    (AddChar.to_mulShift_inj_of_isPrimitive
      (AddChar.IsPrimitive.of_ne_one hψ)) h

/-- Weyl multiplication by the shifted character on the full function space.
Schwartz-space restriction is a separate analytic theorem. -/
def fieldOneWeylMultiplier
    (ψ : AddChar R C) (r : R) : (R → C) →ₗ[C] (R → C) where
  toFun f x := ψ (r * x) * f x
  map_add' f g := by
    funext x
    simp [mul_add]
  map_smul' c f := by
    funext x
    simp [mul_left_comm]

@[simp]
theorem fieldOneWeylMultiplier_apply
    (ψ : AddChar R C) (r : R) (f : R → C) (x : R) :
    fieldOneWeylMultiplier ψ r f x = ψ (r * x) * f x :=
  rfl

/-- Addition of exponents becomes composition of Weyl multipliers. -/
theorem fieldOneWeylMultiplier_add
    (ψ : AddChar R C) (r s : R) :
    (fieldOneWeylMultiplier ψ r).comp (fieldOneWeylMultiplier ψ s) =
      fieldOneWeylMultiplier ψ (r + s) := by
  ext f x
  simp [fieldOneWeylMultiplier_apply, AddChar.map_add_eq_mul,
    add_mul, mul_assoc]

@[simp]
theorem fieldOneWeylMultiplier_zero (ψ : AddChar R C) :
    fieldOneWeylMultiplier ψ 0 = LinearMap.id := by
  ext f x
  simp [fieldOneWeylMultiplier_apply]

/-- The multiplier at `-r` is a left inverse to the multiplier at `r`. -/
theorem fieldOneWeylMultiplier_neg_left
    (ψ : AddChar R C) (r : R) :
    (fieldOneWeylMultiplier ψ (-r)).comp
        (fieldOneWeylMultiplier ψ r) =
      LinearMap.id := by
  rw [fieldOneWeylMultiplier_add, neg_add_cancel,
    fieldOneWeylMultiplier_zero]

/-- The multiplier at `-r` is also a right inverse. -/
theorem fieldOneWeylMultiplier_neg_right
    (ψ : AddChar R C) (r : R) :
    (fieldOneWeylMultiplier ψ r).comp
        (fieldOneWeylMultiplier ψ (-r)) =
      LinearMap.id := by
  rw [fieldOneWeylMultiplier_add, add_neg_cancel,
    fieldOneWeylMultiplier_zero]

end

end GaloisForLFunctions.HTGeometry.FieldOneCore
