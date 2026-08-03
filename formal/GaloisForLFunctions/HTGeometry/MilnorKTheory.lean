import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Milnor `K`-theory of a field

The Milnor `K`-ring of a field `F` is the tensor algebra on the multiplicative group `Fˣ`, written
additively, modulo the Steinberg relation: the symbol `{a, 1 - a}` vanishes whenever both entries
are units.

Everything here is elementary, but none of it is in mathlib, and two cards in this tree name the
absence of Milnor `K`-theory as the reason their statements cannot be written down.

* `MilnorK` : the Milnor `K`-ring, as a quotient of the tensor algebra.
* `milnorSymbol` : the degree-one symbol `{a}`, additive in `a`.
* `milnorSymbol_mul_oneSub` : the Steinberg relation.
* `milnorSymbol_mul_neg_self` : `{a, -a} = 0`.
* `milnorSymbol_anticomm` : `{a, b} = -{b, a}`.
-/

namespace GaloisForLFunctions.HTGeometry

section MilnorK

variable (F : Type*) [Field F]

/-- The unit `1 - a`, available whenever `a ≠ 1`. -/
def oneSubUnit {F : Type*} [Field F] {a : Fˣ} (ha : (a : F) ≠ 1) : Fˣ :=
  Units.mk0 (1 - (a : F)) (sub_ne_zero.mpr (Ne.symm ha))

@[simp]
theorem oneSubUnit_val {F : Type*} [Field F] {a : Fˣ} (ha : (a : F) ≠ 1) :
    ((oneSubUnit ha : Fˣ) : F) = 1 - (a : F) := rfl

/-- **The Steinberg relation**: the product of the symbols of `a` and `1 - a` vanishes. -/
inductive MilnorKRel : TensorAlgebra ℤ (Additive Fˣ) → TensorAlgebra ℤ (Additive Fˣ) → Prop
  | steinberg (a : Fˣ) (ha : (a : F) ≠ 1) :
      MilnorKRel
        (TensorAlgebra.ι ℤ (Additive.ofMul a) *
          TensorAlgebra.ι ℤ (Additive.ofMul (oneSubUnit ha))) 0

/-- **The Milnor `K`-ring of a field.** -/
abbrev MilnorK : Type _ := RingQuot (MilnorKRel F)

/-- The quotient map onto the Milnor `K`-ring. -/
def milnorKMk : TensorAlgebra ℤ (Additive Fˣ) →ₐ[ℤ] MilnorK F :=
  RingQuot.mkAlgHom ℤ (MilnorKRel F)

variable {F}

/-- **The degree-one Milnor symbol** `{a}`. -/
def milnorSymbol (a : Fˣ) : MilnorK F :=
  milnorKMk F (TensorAlgebra.ι ℤ (Additive.ofMul a))

/-- **The symbol is additive**: `{ab} = {a} + {b}`. -/
@[simp]
theorem milnorSymbol_mul (a b : Fˣ) :
    milnorSymbol (a * b) = (milnorSymbol a : MilnorK F) + milnorSymbol b := by
  rw [milnorSymbol, milnorSymbol, milnorSymbol, ← map_add, ← map_add]
  rfl

/-- The symbol of `1` vanishes. -/
@[simp]
theorem milnorSymbol_one : (milnorSymbol 1 : MilnorK F) = 0 := by
  have h := milnorSymbol_mul (F := F) 1 1
  rw [one_mul] at h
  have h2 : (0 : MilnorK F) + milnorSymbol 1 = milnorSymbol 1 + milnorSymbol 1 := by
    rw [zero_add]
    exact h
  exact (add_right_cancel h2).symm

/-- The symbol of an inverse is the negative of the symbol. -/
@[simp]
theorem milnorSymbol_inv (a : Fˣ) : milnorSymbol a⁻¹ = -(milnorSymbol a : MilnorK F) := by
  have h := milnorSymbol_mul (F := F) a a⁻¹
  rw [mul_inv_cancel, milnorSymbol_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- **The Steinberg relation in the Milnor ring.** -/
theorem milnorSymbol_mul_oneSub {a : Fˣ} (ha : (a : F) ≠ 1) :
    (milnorSymbol a : MilnorK F) * milnorSymbol (oneSubUnit ha) = 0 := by
  have h := RingQuot.mkAlgHom_rel (S := ℤ) (MilnorKRel.steinberg (F := F) a ha)
  rw [milnorSymbol, milnorSymbol, milnorKMk, ← map_mul]
  rw [h, map_zero]

/-- **`{a, -a} = 0`.**  The unit identity `(-a)(1 - a⁻¹) = 1 - a` turns the symbol of `-a` into a
difference of two Steinberg entries, and both resulting products vanish. -/
theorem milnorSymbol_mul_neg_self (a : Fˣ) :
    (milnorSymbol a : MilnorK F) * milnorSymbol (-a) = 0 := by
  by_cases ha : (a : F) = 1
  · have h1 : a = 1 := Units.ext ha
    rw [h1, milnorSymbol_one, zero_mul]
  · have hainv : ((a⁻¹ : Fˣ) : F) ≠ 1 := fun h =>
      ha (congrArg Units.val (inv_eq_one.mp (Units.ext h)))
    have hane : (a : F) ≠ 0 := a.ne_zero
    have hunit : (-a : Fˣ) * oneSubUnit hainv = oneSubUnit ha := by
      refine Units.ext ?_
      rw [Units.val_mul, oneSubUnit_val, oneSubUnit_val, Units.val_neg,
        Units.val_inv_eq_inv_val, mul_sub, mul_one, neg_mul, mul_inv_cancel₀ hane]
      ring
    have hsym : (milnorSymbol (-a) : MilnorK F) =
        milnorSymbol (oneSubUnit ha) - milnorSymbol (oneSubUnit hainv) := by
      have h := congrArg (fun u : Fˣ => (milnorSymbol u : MilnorK F)) hunit
      simp only [milnorSymbol_mul] at h
      exact eq_sub_of_add_eq h
    rw [hsym, mul_sub, milnorSymbol_mul_oneSub ha]
    have hsecond : (milnorSymbol a : MilnorK F) * milnorSymbol (oneSubUnit hainv) = 0 := by
      have hinv : (milnorSymbol a : MilnorK F) = -milnorSymbol a⁻¹ := by
        rw [milnorSymbol_inv, neg_neg]
      calc (milnorSymbol a : MilnorK F) * milnorSymbol (oneSubUnit hainv)
          = -(milnorSymbol a⁻¹ * milnorSymbol (oneSubUnit hainv)) := by
            rw [hinv]
            exact neg_mul (milnorSymbol a⁻¹ : MilnorK F) (milnorSymbol (oneSubUnit hainv))
        _ = 0 := by rw [milnorSymbol_mul_oneSub hainv, neg_zero]
    rw [hsecond, sub_zero]

/-- **Anticommutativity of the Milnor symbol**: `{a, b} = -{b, a}`.  Expand `{ab, -(ab)} = 0` using
`-(ab) = (-a)b = a(-b)`; the diagonal terms are `{a, -a}` and `{b, -b}`, which vanish. -/
theorem milnorSymbol_anticomm (a b : Fˣ) :
    (milnorSymbol a : MilnorK F) * milnorSymbol b = -(milnorSymbol b * milnorSymbol a) := by
  have hab := milnorSymbol_mul_neg_self (F := F) (a * b)
  have hnegab : (-(a * b) : Fˣ) = (-a) * b := by
    refine Units.ext ?_
    simp [Units.val_mul, Units.val_neg]
  have hnegba : (-(a * b) : Fˣ) = a * (-b) := by
    refine Units.ext ?_
    simp [Units.val_mul, Units.val_neg]
  have ha := milnorSymbol_mul_neg_self (F := F) a
  have hb := milnorSymbol_mul_neg_self (F := F) b
  rw [milnorSymbol_mul] at hab
  have hexpand : (milnorSymbol a + milnorSymbol b : MilnorK F) * milnorSymbol (-(a * b)) =
      milnorSymbol a * milnorSymbol (-a) + milnorSymbol a * milnorSymbol b +
        (milnorSymbol b * milnorSymbol a + milnorSymbol b * milnorSymbol (-b)) := by
    rw [add_mul]
    congr 1
    · rw [hnegab, milnorSymbol_mul, mul_add]
    · rw [hnegba, milnorSymbol_mul, mul_add]
  rw [hexpand, ha, hb, zero_add, add_zero] at hab
  have hab' : milnorSymbol b * milnorSymbol a + (milnorSymbol a : MilnorK F) * milnorSymbol b = 0 := by
    rw [add_comm]
    exact hab
  exact eq_neg_of_add_eq_zero_right hab'

end MilnorK

end GaloisForLFunctions.HTGeometry
