import GaloisForLFunctions.HTGeometry.MilnorKSlotGeneration

/-!
# Expanding one slot of a Milnor symbol along a product

Multilinearity of a Milnor symbol in a fixed slot turns a product of entries into a sum of symbols.
Iterating this over a list of factors is the step that replaces an arbitrary polynomial entry by its
irreducible factors.

* `slotClass` : the class of a symbol with a designated slot.
* `slotClass_prod` : **the class of a symbol whose designated slot is a product of a list is the
  sum of the classes obtained by putting each factor there.**
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] {n : ℕ}

theorem length_slot (l₁ l₂ : List Kˣ) (a : Kˣ) (h : (l₁ ++ l₂).length + 1 = n) :
    (l₁ ++ a :: l₂).length = n := by
  simp only [List.length_append, List.length_cons] at h ⊢
  omega

/-- The class of a symbol with one designated slot. -/
noncomputable def slotClass (l₁ l₂ : List Kˣ) (h : (l₁ ++ l₂).length + 1 = n) (a : Kˣ) :
    MilnorKDeg K n :=
  milnorClassDeg K n ⟨l₁ ++ a :: l₂, length_slot l₁ l₂ a h⟩

theorem slotClass_mul (l₁ l₂ : List Kˣ) (h : (l₁ ++ l₂).length + 1 = n) (a b : Kˣ) :
    slotClass l₁ l₂ h (a * b) = slotClass l₁ l₂ h a + slotClass l₁ l₂ h b :=
  milnorClassDeg_mul_of_eq (F := K) a b l₁ l₂ rfl rfl rfl _ _ _

theorem slotClass_one (l₁ l₂ : List Kˣ) (h : (l₁ ++ l₂).length + 1 = n) :
    slotClass l₁ l₂ h 1 = 0 :=
  milnorClassDeg_one_of_eq (K := K) l₁ l₂ rfl _

/-- **A product in one slot expands into a sum of symbols.** -/
theorem slotClass_prod (l₁ l₂ : List Kˣ) (h : (l₁ ++ l₂).length + 1 = n) :
    ∀ qs : List Kˣ, slotClass l₁ l₂ h qs.prod
      = (qs.map (slotClass l₁ l₂ h)).sum := by
  intro qs
  induction qs with
  | nil => simpa using slotClass_one l₁ l₂ h
  | cons q t ih =>
      rw [List.prod_cons, slotClass_mul, ih, List.map_cons, List.sum_cons]

end GaloisForLFunctions.HTGeometry
