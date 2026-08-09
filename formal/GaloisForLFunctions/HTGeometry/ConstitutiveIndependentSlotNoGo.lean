import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

/-!
# Independent-slot anti-theatre theorem

A field candidate assembled from independently relabelable organs has no nonconstant intrinsic
observable and no proper nonempty intrinsic phase.  The types are packaged with distinguished
points, so every exported theorem is closed and has no external nonemptiness premise.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- One nonempty constitutive slot, with nonemptiness carried as source data. -/
structure ConstitutiveSlot where
  Carrier : Type u
  base : Carrier

/-- States of a finite family of constitutive slots. -/
abbrev ConstitutiveSlotState {n : ℕ} (S : Fin n → ConstitutiveSlot) :=
  ∀ i, (S i).Carrier

/-- Independent coordinate relabellings. -/
abbrev ConstitutiveSlotGauge {n : ℕ} (S : Fin n → ConstitutiveSlot) :=
  ∀ i, (S i).Carrier ≃ (S i).Carrier

/-- Coordinatewise gauge action. -/
def constitutiveSlotAction {n : ℕ} (S : Fin n → ConstitutiveSlot)
    (g : ConstitutiveSlotGauge S) (x : ConstitutiveSlotState S) :
    ConstitutiveSlotState S :=
  fun i ↦ g i (x i)

/-- The independent relabelling action is transitive on every finite slot product. -/
theorem constitutiveSlotAction_transitive {n : ℕ} (S : Fin n → ConstitutiveSlot)
    (x y : ConstitutiveSlotState S) :
    ∃ g : ConstitutiveSlotGauge S, constitutiveSlotAction S g x = y := by
  classical
  refine ⟨fun i ↦ Equiv.swap (x i) (y i), ?_⟩
  funext i
  simp [constitutiveSlotAction]

/-- Predicate together with invariance under every independent relabelling. -/
structure ConstitutiveIntrinsicPredicate {n : ℕ} (S : Fin n → ConstitutiveSlot) where
  pred : ConstitutiveSlotState S → Prop
  invariant : ∀ (g : ConstitutiveSlotGauge S) (x : ConstitutiveSlotState S),
    pred (constitutiveSlotAction S g x) ↔ pred x

/-- An intrinsic phase of bare independent slots is empty or full. -/
theorem constitutiveIntrinsicPredicate_empty_or_full {n : ℕ}
    (S : Fin n → ConstitutiveSlot) (P : ConstitutiveIntrinsicPredicate S) :
    (∀ x, ¬ P.pred x) ∨ (∀ x, P.pred x) := by
  classical
  by_cases h : ∃ x, P.pred x
  · right
    rintro y
    obtain ⟨x, hx⟩ := h
    obtain ⟨g, hg⟩ := constitutiveSlotAction_transitive S x y
    rw [← hg]
    exact (P.invariant g x).2 hx
  · left
    intro x hx
    exact h ⟨x, hx⟩

/-- Observable together with invariance under every independent relabelling. -/
structure ConstitutiveIntrinsicInvariant {n : ℕ} (S : Fin n → ConstitutiveSlot)
    (Y : Type v) where
  value : ConstitutiveSlotState S → Y
  invariant : ∀ (g : ConstitutiveSlotGauge S) (x : ConstitutiveSlotState S),
    value (constitutiveSlotAction S g x) = value x

/-- Every invariant of bare independent slots is constant. -/
theorem constitutiveIntrinsicInvariant_constant {n : ℕ}
    (S : Fin n → ConstitutiveSlot) (Y : Type v)
    (I : ConstitutiveIntrinsicInvariant S Y) (x y : ConstitutiveSlotState S) :
    I.value x = I.value y := by
  obtain ⟨g, hg⟩ := constitutiveSlotAction_transitive S x y
  rw [← hg, I.invariant]

/-- Canonical state, witnessing that the slot product is never empty. -/
def constitutiveSlotBaseState {n : ℕ} (S : Fin n → ConstitutiveSlot) :
    ConstitutiveSlotState S :=
  fun i ↦ (S i).base

end GaloisForLFunctions.HTGeometry
