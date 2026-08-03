import GaloisForLFunctions.HTGeometry.QuadraticallyClosedWittRing
import Mathlib.Tactic.NoncommRing

/-!
# One-dimensional forms in Milnor--Witt `K`-theory

Morel's element `⟨a⟩ = 1 + η[a]` is the class of the one-dimensional form `a`.  This file derives
its laws directly from the four defining relations: it is multiplicative, `⟨1⟩ = 1`, it is a unit,
`⟨a⟩ + ⟨-a⟩ = 1 + ⟨-1⟩`, and — the identity the geometric collapse rests on — **`⟨a²⟩ = 1`**.

The route runs through `[1] = 0` and `[a][-a] = 0`.  Twisted multiplicativity with a unit entry
gives `[1] + η[1][b] = 0` for every `b`; feeding `b = -1` into the hyperbolic relation leaves
`η[1] = 0`, hence `[1] = 0`.  Then the unit identity `(-a)(1 - a⁻¹) = 1 - a` makes `[a][-a]`
annihilated by `⟨1 - a⁻¹⟩`, which is a unit, so `[a][-a] = 0`.  Finally `η²[a][-a] = 0` expands to
`⟨-1⟩⟨a²⟩ = ⟨-1⟩`.

Over a quadratically closed field every unit is a square, so `⟨u⟩ = 1` and `η[u] = 0` for every
unit: `η` annihilates every symbol.  That is the algebraic reason the quadratic refinement carries
no information on such a field.

* `milnorWittEta_central` : `η` is central.
* `milnorWittSymbol_one`, `milnorWittForm_one` : `[1] = 0` and `⟨1⟩ = 1`.
* `milnorWittSymbol_mul_neg_self` : `[a][-a] = 0`.
* `milnorWittForm_add_neg` : `⟨a⟩ + ⟨-a⟩ = 1 + ⟨-1⟩`.
* `milnorWittForm_sq`, `milnorWittEta_symbol_sq` : `⟨a²⟩ = 1` and `η[a²] = 0`.
* `milnorWittEta_symbol_eq_zero` : over a quadratically closed field `η` kills every symbol.
-/

namespace GaloisForLFunctions.HTGeometry

section MilnorWittForms

variable {F : Type*} [Field F]

/-- **`η` is central in Milnor--Witt `K`-theory.**  It commutes with the symbols by the third
defining relation and with scalars because those are central, hence with every element. -/
theorem milnorWittEta_central (x : MilnorWittK F) :
    milnorWittEta F * x = x * milnorWittEta F := by
  obtain ⟨w, rfl⟩ := RingQuot.mkAlgHom_surjective ℤ (MilnorWittRel F) x
  induction w using FreeAlgebra.induction with
  | grade0 r =>
    rw [show (RingQuot.mkAlgHom ℤ (MilnorWittRel F)) (algebraMap ℤ _ r) =
        algebraMap ℤ (MilnorWittK F) r from AlgHom.commutes _ _]
    exact (Algebra.commutes r (milnorWittEta F)).symm
  | grade1 g =>
    cases g with
    | eta => rfl
    | sym u => exact (milnorWittEta_comm u).symm
  | mul a b ha hb =>
    rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]
  | add a b ha hb =>
    rw [map_add, mul_add, add_mul, ha, hb]

/-- Pulling `η` out to the left. -/
theorem milnorWittEta_mul_left (x y : MilnorWittK F) :
    x * (milnorWittEta F * y) = milnorWittEta F * (x * y) := by
  rw [← mul_assoc, ← milnorWittEta_central x, mul_assoc]

/-- Collecting the two `η`'s of a product of two `η`-multiples. -/
theorem milnorWittEta_mul_mul (x y : MilnorWittK F) :
    milnorWittEta F * x * (milnorWittEta F * y) =
      milnorWittEta F * (milnorWittEta F * x * y) := by
  calc milnorWittEta F * x * (milnorWittEta F * y)
      = milnorWittEta F * (x * (milnorWittEta F * y)) := mul_assoc _ _ _
    _ = milnorWittEta F * (milnorWittEta F * (x * y)) := by rw [milnorWittEta_mul_left]
    _ = milnorWittEta F * (milnorWittEta F * x * y) := by rw [mul_assoc]

/-- **The one-dimensional form `⟨a⟩ = 1 + η[a]`.** -/
def milnorWittForm (a : Fˣ) : MilnorWittK F := 1 + milnorWittEta F * milnorWittSymbol a

theorem milnorWittForm_def (a : Fˣ) :
    (milnorWittForm a : MilnorWittK F) = 1 + milnorWittEta F * milnorWittSymbol a := rfl

theorem milnorWittEta_mul_symbol (a : Fˣ) :
    milnorWittEta F * milnorWittSymbol a = (milnorWittForm a : MilnorWittK F) - 1 := by
  rw [milnorWittForm_def, add_sub_cancel_left]

/-- **The forms are multiplicative**: `⟨a⟩⟨b⟩ = ⟨ab⟩`.  This is twisted multiplicativity of the
symbol, rearranged. -/
theorem milnorWittForm_mul (a b : Fˣ) :
    (milnorWittForm a : MilnorWittK F) * milnorWittForm b = milnorWittForm (a * b) := by
  simp only [milnorWittForm_def, milnorWittSymbol_mul, mul_add, add_mul, one_mul, mul_one]
  rw [milnorWittEta_mul_mul]
  abel

/-- Twisted multiplicativity with a unit entry: `[1] + η[1][b] = 0` for every `b`. -/
theorem milnorWittSymbol_one_add (b : Fˣ) :
    (milnorWittSymbol (1 : Fˣ) : MilnorWittK F) +
      milnorWittEta F * milnorWittSymbol 1 * milnorWittSymbol b = 0 := by
  have h := milnorWittSymbol_mul (F := F) 1 b
  rw [one_mul] at h
  calc (milnorWittSymbol (1 : Fˣ) : MilnorWittK F) +
        milnorWittEta F * milnorWittSymbol 1 * milnorWittSymbol b
      = (milnorWittSymbol (1 : Fˣ) + milnorWittSymbol b +
          milnorWittEta F * milnorWittSymbol 1 * milnorWittSymbol b) - milnorWittSymbol b := by
        abel
    _ = milnorWittSymbol b - milnorWittSymbol b := by rw [← h]
    _ = 0 := sub_self _

/-- **`η[1] = 0`.**  The hyperbolic relation, multiplied by `[1]`, collapses to `η[1]` once the
`b = -1` instance of twisted multiplicativity is substituted. -/
theorem milnorWittEta_symbol_one : milnorWittEta F * milnorWittSymbol (1 : Fˣ) = 0 := by
  have hgen := milnorWittSymbol_one_add (F := F) (-1)
  have hE : milnorWittEta F * ((milnorWittSymbol (1 : Fˣ) : MilnorWittK F) +
      milnorWittEta F * milnorWittSymbol 1 * milnorWittSymbol (-1 : Fˣ)) = 0 := by
    rw [hgen, mul_zero]
  rw [mul_add] at hE
  have hhyp : (milnorWittSymbol (1 : Fˣ) : MilnorWittK F) *
      (milnorWittEta F * (milnorWittEta F * milnorWittSymbol (-1 : Fˣ) + 2)) = 0 := by
    rw [milnorWittEta_hyperbolic, mul_zero]
  have expand : (milnorWittSymbol (1 : Fˣ) : MilnorWittK F) *
      (milnorWittEta F * (milnorWittEta F * milnorWittSymbol (-1 : Fˣ) + 2)) =
      milnorWittEta F * (milnorWittEta F * milnorWittSymbol 1 * milnorWittSymbol (-1 : Fˣ)) +
        (milnorWittEta F * milnorWittSymbol 1 + milnorWittEta F * milnorWittSymbol 1) := by
    rw [milnorWittEta_mul_left, mul_add, milnorWittEta_mul_left, mul_add,
      ← mul_assoc (milnorWittEta F) (milnorWittSymbol (1 : Fˣ)) (milnorWittSymbol (-1 : Fˣ)),
      mul_two, mul_add]
  rw [expand] at hhyp
  have hfin : milnorWittEta F * milnorWittSymbol (1 : Fˣ) =
      (milnorWittEta F * (milnorWittEta F * milnorWittSymbol 1 * milnorWittSymbol (-1 : Fˣ)) +
          (milnorWittEta F * milnorWittSymbol 1 + milnorWittEta F * milnorWittSymbol 1)) -
        (milnorWittEta F * milnorWittSymbol 1 +
          milnorWittEta F *
            (milnorWittEta F * milnorWittSymbol 1 * milnorWittSymbol (-1 : Fˣ))) := by
    abel
  rw [hhyp, hE, sub_self] at hfin
  exact hfin

/-- **`[1] = 0` in Milnor--Witt `K`-theory.** -/
@[simp]
theorem milnorWittSymbol_one : (milnorWittSymbol (1 : Fˣ) : MilnorWittK F) = 0 := by
  have h := milnorWittSymbol_one_add (F := F) 1
  rw [milnorWittEta_symbol_one, zero_mul, add_zero] at h
  exact h

@[simp]
theorem milnorWittForm_one : (milnorWittForm (1 : Fˣ) : MilnorWittK F) = 1 := by
  rw [milnorWittForm_def, milnorWittSymbol_one, mul_zero, add_zero]

/-- **The forms are units.** -/
theorem milnorWittForm_mul_inv (a : Fˣ) :
    (milnorWittForm a : MilnorWittK F) * milnorWittForm a⁻¹ = 1 := by
  rw [milnorWittForm_mul, mul_inv_cancel, milnorWittForm_one]

theorem eq_zero_of_mul_form_eq_zero {x : MilnorWittK F} {a : Fˣ}
    (h : x * milnorWittForm a = 0) : x = 0 := by
  have h2 : x * milnorWittForm a * milnorWittForm a⁻¹ = 0 := by rw [h, zero_mul]
  rwa [mul_assoc, milnorWittForm_mul_inv, mul_one] at h2

/-- The twisted inverse law: `[a] + [a⁻¹] + η[a][a⁻¹] = 0`. -/
theorem milnorWittSymbol_add_inv (a : Fˣ) :
    (milnorWittSymbol a : MilnorWittK F) + milnorWittSymbol a⁻¹ +
      milnorWittEta F * milnorWittSymbol a * milnorWittSymbol a⁻¹ = 0 := by
  have h := milnorWittSymbol_mul (F := F) a a⁻¹
  rw [mul_inv_cancel, milnorWittSymbol_one] at h
  exact h.symm

/-- **`[a][1 - a⁻¹] = 0`.**  Rewriting `[a]` through the inverse law turns the product into two
Steinberg products. -/
theorem milnorWittSymbol_mul_oneSubInv {a : Fˣ} (hainv : ((a⁻¹ : Fˣ) : F) ≠ 1) :
    (milnorWittSymbol a : MilnorWittK F) * milnorWittSymbol (oneSubUnit hainv) = 0 := by
  have hst : (milnorWittSymbol a⁻¹ : MilnorWittK F) * milnorWittSymbol (oneSubUnit hainv) = 0 :=
    milnorWittSymbol_mul_oneSub hainv
  have h := congrArg (fun z : MilnorWittK F => z * milnorWittSymbol (oneSubUnit hainv))
    (milnorWittSymbol_add_inv (F := F) a)
  simp only [add_mul, zero_mul] at h
  rw [hst, mul_assoc (milnorWittEta F * milnorWittSymbol a), hst, mul_zero, add_zero,
    add_zero] at h
  exact h

/-- **`[a][-a] = 0`.**  The unit identity `(-a)(1 - a⁻¹) = 1 - a` makes `[a][-a]` annihilated by
the one-dimensional form `⟨1 - a⁻¹⟩`, which is a unit. -/
theorem milnorWittSymbol_mul_neg_self (a : Fˣ) :
    (milnorWittSymbol a : MilnorWittK F) * milnorWittSymbol (-a) = 0 := by
  by_cases ha : (a : F) = 1
  · have h1 : a = 1 := Units.ext ha
    rw [h1, milnorWittSymbol_one, zero_mul]
  · have hainv : ((a⁻¹ : Fˣ) : F) ≠ 1 := fun h =>
      ha (congrArg Units.val (inv_eq_one.mp (Units.ext h)))
    have hane : (a : F) ≠ 0 := a.ne_zero
    have hunit : (-a : Fˣ) * oneSubUnit hainv = oneSubUnit ha := by
      refine Units.ext ?_
      rw [Units.val_mul, oneSubUnit_val, oneSubUnit_val, Units.val_neg,
        Units.val_inv_eq_inv_val, mul_sub, mul_one, neg_mul, mul_inv_cancel₀ hane]
      ring
    have htw := milnorWittSymbol_mul (F := F) (-a) (oneSubUnit hainv)
    rw [hunit] at htw
    have h := congrArg (fun z : MilnorWittK F => milnorWittSymbol a * z) htw
    simp only [mul_add] at h
    rw [milnorWittSymbol_mul_oneSub ha, milnorWittSymbol_mul_oneSubInv hainv, add_zero] at h
    have hshift : (milnorWittSymbol a : MilnorWittK F) *
        (milnorWittEta F * milnorWittSymbol (-a) * milnorWittSymbol (oneSubUnit hainv)) =
        milnorWittSymbol a * milnorWittSymbol (-a) *
          (milnorWittEta F * milnorWittSymbol (oneSubUnit hainv)) := by
      rw [mul_assoc (milnorWittEta F) (milnorWittSymbol (-a))
          (milnorWittSymbol (oneSubUnit hainv)),
        milnorWittEta_mul_left,
        ← mul_assoc (milnorWittSymbol a) (milnorWittSymbol (-a))
          (milnorWittSymbol (oneSubUnit hainv)),
        ← mul_assoc (milnorWittEta F) (milnorWittSymbol a * milnorWittSymbol (-a)),
        milnorWittEta_central, mul_assoc]
    rw [hshift] at h
    refine eq_zero_of_mul_form_eq_zero (a := oneSubUnit hainv) ?_
    rw [milnorWittForm_def, mul_add, mul_one]
    exact h.symm

/-- **`⟨a⟩ + ⟨-a⟩ = 1 + ⟨-1⟩`.**  This is the hyperbolic relation, read through the forms:
`1 + ⟨-1⟩` is Morel's hyperbolic element, and `η` annihilates it. -/
theorem milnorWittForm_add_neg (a : Fˣ) :
    (milnorWittForm a : MilnorWittK F) + milnorWittForm (-a) =
      1 + milnorWittForm (-1 : Fˣ) := by
  have hh : (1 : MilnorWittK F) + milnorWittForm (-1 : Fˣ) =
      milnorWittEta F * milnorWittSymbol (-1 : Fˣ) + 2 := by
    rw [milnorWittForm_def, ← one_add_one_eq_two]
    abel
  have hkey : ((1 : MilnorWittK F) + milnorWittForm (-1 : Fˣ)) *
      (milnorWittEta F * milnorWittSymbol a) = 0 := by
    rw [milnorWittEta_mul_left, hh, ← mul_assoc, milnorWittEta_hyperbolic, zero_mul]
  have hneg : (-a : Fˣ) = (-1 : Fˣ) * a := by
    refine Units.ext ?_
    push_cast
    ring
  calc (milnorWittForm a : MilnorWittK F) + milnorWittForm (-a)
      = ((1 : MilnorWittK F) + milnorWittForm (-1 : Fˣ)) * milnorWittForm a := by
        rw [hneg, ← milnorWittForm_mul]
        noncomm_ring
    _ = ((1 : MilnorWittK F) + milnorWittForm (-1 : Fˣ)) +
          ((1 : MilnorWittK F) + milnorWittForm (-1 : Fˣ)) *
            (milnorWittEta F * milnorWittSymbol a) := by
        rw [milnorWittForm_def a, mul_add, mul_one]
    _ = 1 + milnorWittForm (-1 : Fˣ) := by rw [hkey, add_zero]

/-- **`⟨a²⟩ = 1`.**  Expanding `(⟨a⟩ - 1)(⟨-a⟩ - 1) = η²[a][-a] = 0` and substituting
`⟨a⟩ + ⟨-a⟩ = 1 + ⟨-1⟩` leaves `⟨-1⟩⟨a²⟩ = ⟨-1⟩`, and `⟨-1⟩` is a unit. -/
theorem milnorWittForm_sq (a : Fˣ) : (milnorWittForm (a * a) : MilnorWittK F) = 1 := by
  have hzero : ((milnorWittForm a : MilnorWittK F) - 1) * (milnorWittForm (-a) - 1) = 0 := by
    rw [← milnorWittEta_mul_symbol, ← milnorWittEta_mul_symbol, milnorWittEta_mul_mul,
      mul_assoc (milnorWittEta F) (milnorWittSymbol a) (milnorWittSymbol (-a)),
      milnorWittSymbol_mul_neg_self, mul_zero, mul_zero]
  have hprod : (milnorWittForm a : MilnorWittK F) * milnorWittForm (-a) =
      milnorWittForm (-1 : Fˣ) * milnorWittForm (a * a) := by
    rw [milnorWittForm_mul, milnorWittForm_mul]
    congr 1
    refine Units.ext ?_
    push_cast
    ring
  have hsum := milnorWittForm_add_neg (F := F) a
  have hexp : (milnorWittForm a : MilnorWittK F) * milnorWittForm (-a) -
      ((milnorWittForm a : MilnorWittK F) + milnorWittForm (-a)) + 1 = 0 := by
    rw [← hzero]
    simp only [sub_mul, mul_sub, one_mul, mul_one]
    abel
  rw [hprod, hsum] at hexp
  have hinv : (milnorWittForm (-1 : Fˣ) : MilnorWittK F) * milnorWittForm (-1 : Fˣ) = 1 := by
    rw [milnorWittForm_mul]
    have hone : (-1 : Fˣ) * (-1 : Fˣ) = 1 := by
      refine Units.ext ?_
      push_cast
      ring
    rw [hone, milnorWittForm_one]
  have hfin : (milnorWittForm (-1 : Fˣ) : MilnorWittK F) * milnorWittForm (a * a) =
      milnorWittForm (-1 : Fˣ) := by
    have h2 : (milnorWittForm (-1 : Fˣ) : MilnorWittK F) * milnorWittForm (a * a) -
        milnorWittForm (-1 : Fˣ) = 0 := by
      rw [← hexp]
      abel
    exact sub_eq_zero.mp h2
  calc (milnorWittForm (a * a) : MilnorWittK F)
      = 1 * milnorWittForm (a * a) := (one_mul _).symm
    _ = milnorWittForm (-1 : Fˣ) * milnorWittForm (-1 : Fˣ) * milnorWittForm (a * a) := by
        rw [hinv]
    _ = milnorWittForm (-1 : Fˣ) * (milnorWittForm (-1 : Fˣ) * milnorWittForm (a * a)) :=
        mul_assoc _ _ _
    _ = milnorWittForm (-1 : Fˣ) * milnorWittForm (-1 : Fˣ) := by rw [hfin]
    _ = 1 := hinv

/-- **`η[a²] = 0`.** -/
theorem milnorWittEta_symbol_sq (a : Fˣ) :
    milnorWittEta F * milnorWittSymbol (a * a) = 0 := by
  rw [milnorWittEta_mul_symbol, milnorWittForm_sq, sub_self]

/-! ### Quadratically closed fields -/

/-- **Over a quadratically closed field every one-dimensional form is trivial.** -/
theorem milnorWittForm_eq_one (hsq : ∀ x : F, ∃ y : F, x = y * y) (u : Fˣ) :
    (milnorWittForm u : MilnorWittK F) = 1 := by
  obtain ⟨b, hb⟩ := exists_unit_sq F hsq u
  rw [hb, pow_two]
  exact milnorWittForm_sq b

/-- **Over a quadratically closed field `η` annihilates every symbol.**  This is the algebraic
counterpart of the vanishing of the fundamental ideal: nothing quadratic survives. -/
theorem milnorWittEta_symbol_eq_zero (hsq : ∀ x : F, ∃ y : F, x = y * y) (u : Fˣ) :
    milnorWittEta F * milnorWittSymbol u = 0 := by
  rw [milnorWittEta_mul_symbol, milnorWittForm_eq_one hsq, sub_self]

end MilnorWittForms

end GaloisForLFunctions.HTGeometry
