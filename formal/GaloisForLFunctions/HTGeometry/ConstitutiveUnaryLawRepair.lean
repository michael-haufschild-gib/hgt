import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

/-!
# Unary observer-operation Galois repair

Intersection of all executable observer equivalences gives the canonical least repair forced by a
family of unary source laws.  Quotient descent is equivalent to kernel preservation, so every
observer retaining the laws must contain the repair closure.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

def UnaryPreserves {α : Type u} (f : α → α) (R : α → α → Prop) : Prop :=
  ∀ ⦃x y⦄, R x y → R (f x) (f y)

def UnaryLawClosure {α : Type u} (F : Set (α → α)) (E : α → α → Prop) :
    α → α → Prop :=
  fun x y ↦ ∀ (R : α → α → Prop),
    Equivalence R →
    (∀ ⦃a b⦄, E a b → R a b) →
    (∀ f ∈ F, UnaryPreserves f R) →
    R x y

theorem unaryLawClosure_equivalence {α : Type u} (F : Set (α → α))
    (E : α → α → Prop) : Equivalence (UnaryLawClosure F E) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x R hR hE hF
    exact hR.refl x
  · intro x y hxy R hR hE hF
    exact hR.symm (hxy R hR hE hF)
  · intro x y z hxy hyz R hR hE hF
    exact hR.trans (hxy R hR hE hF) (hyz R hR hE hF)

theorem unaryLawClosure_contains {α : Type u} (F : Set (α → α))
    (E : α → α → Prop) :
    ∀ ⦃x y⦄, E x y → UnaryLawClosure F E x y := by
  intro x y hxy R hR hE hF
  exact hE hxy

theorem unaryLawClosure_preserves {α : Type u} (F : Set (α → α))
    (E : α → α → Prop) {f : α → α} (hf : f ∈ F) :
    UnaryPreserves f (UnaryLawClosure F E) := by
  intro x y hxy R hR hE hF
  exact hF f hf (hxy R hR hE hF)

theorem unaryLawClosure_least {α : Type u} {F : Set (α → α)}
    {E R : α → α → Prop} (hR : Equivalence R)
    (hE : ∀ ⦃x y⦄, E x y → R x y)
    (hF : ∀ f ∈ F, UnaryPreserves f R) :
    ∀ ⦃x y⦄, UnaryLawClosure F E x y → R x y := by
  intro x y hxy
  exact hxy R hR hE hF

theorem unaryLawClosure_fixed_iff {α : Type u} (F : Set (α → α))
    (E : α → α → Prop) (hE : Equivalence E) :
    UnaryLawClosure F E = E ↔ ∀ f ∈ F, UnaryPreserves f E := by
  constructor
  · intro h f hf
    rw [← h]
    exact unaryLawClosure_preserves F E hf
  · intro h
    funext x y
    apply propext
    constructor
    · intro hcl
      exact hcl E hE (fun {_ _} hxy ↦ hxy) h
    · intro hxy
      exact unaryLawClosure_contains F E hxy

def ObserverKernel {α : Type u} {β : Type v} (q : α → β) : α → α → Prop :=
  fun x y ↦ q x = q y

theorem observerKernel_equivalence {α : Type u} {β : Type v} (q : α → β) :
    Equivalence (ObserverKernel q) := by
  exact ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩

theorem observerKernel_preserved_of_descended {α : Type u} {β : Type v}
    (q : α → β) (f : α → α) (g : β → β)
    (h : ∀ x, q (f x) = g (q x)) : UnaryPreserves f (ObserverKernel q) := by
  intro x y hxy
  change q x = q y at hxy
  change q (f x) = q (f y)
  rw [h x, h y, hxy]

theorem descended_of_observerKernel_preserved {α : Type u} {β : Type v}
    (q : α → β) (f : α → α) (h : UnaryPreserves f (ObserverKernel q)) :
    ∃ g : β → β, ∀ x, q (f x) = g (q x) := by
  classical
  let g : β → β := fun b ↦
    if hex : ∃ a, q a = b then q (f (Classical.choose hex)) else b
  refine ⟨g, ?_⟩
  intro x
  have hex : ∃ a, q a = q x := ⟨x, rfl⟩
  rw [show g (q x) = q (f (Classical.choose hex)) by simp [g, hex]]
  exact (h (Classical.choose_spec hex)).symm

theorem descended_iff_observerKernel_preserved {α : Type u} {β : Type v}
    (q : α → β) (f : α → α) :
    (∃ g : β → β, ∀ x, q (f x) = g (q x)) ↔
      UnaryPreserves f (ObserverKernel q) := by
  constructor
  · rintro ⟨g, hg⟩
    exact observerKernel_preserved_of_descended q f g hg
  · exact descended_of_observerKernel_preserved q f

theorem no_descended_of_not_observerKernel_preserved {α : Type u} {β : Type v}
    (q : α → β) (f : α → α) (h : ¬ UnaryPreserves f (ObserverKernel q)) :
    ¬ ∃ g : β → β, ∀ x, q (f x) = g (q x) := by
  exact fun hex ↦ h ((descended_iff_observerKernel_preserved q f).1 hex)

theorem unaryLawClosure_subset_observerKernel_of_descents {α : Type u} {β : Type v}
    (F : Set (α → α)) (E : α → α → Prop) (q : α → β)
    (hE : ∀ ⦃x y⦄, E x y → ObserverKernel q x y)
    (hdesc : ∀ f ∈ F, ∃ g : β → β, ∀ x, q (f x) = g (q x)) :
    ∀ ⦃x y⦄, UnaryLawClosure F E x y → ObserverKernel q x y := by
  apply unaryLawClosure_least (observerKernel_equivalence q) hE
  intro f hf
  obtain ⟨g, hg⟩ := hdesc f hf
  exact observerKernel_preserved_of_descended q f g hg

theorem unaryLawClosure_mono {α : Type u} {F G : Set (α → α)}
    {E E' : α → α → Prop} (hFG : F ⊆ G)
    (hEE' : ∀ ⦃x y⦄, E x y → E' x y) :
    ∀ ⦃x y⦄, UnaryLawClosure F E x y → UnaryLawClosure G E' x y := by
  apply unaryLawClosure_least (unaryLawClosure_equivalence G E')
  · intro x y hxy
    exact unaryLawClosure_contains G E' (hEE' hxy)
  · intro f hf
    exact unaryLawClosure_preserves G E' (hFG hf)

theorem unaryLawRepairMechanism_closed {α : Type u} {β : Type v} :
    (∀ (F : Set (α → α)) (E : α → α → Prop),
      Equivalence (UnaryLawClosure F E)) ∧
    (∀ (F : Set (α → α)) (E : α → α → Prop),
      ∀ ⦃x y⦄, E x y → UnaryLawClosure F E x y) ∧
    (∀ (F : Set (α → α)) (E : α → α → Prop) (f : α → α),
      f ∈ F → UnaryPreserves f (UnaryLawClosure F E)) ∧
    (∀ (q : α → β) (f : α → α),
      (∃ g : β → β, ∀ x, q (f x) = g (q x)) ↔
        UnaryPreserves f (ObserverKernel q)) ∧
    (∀ (F : Set (α → α)) (E : α → α → Prop) (q : α → β),
      (∀ ⦃x y⦄, E x y → ObserverKernel q x y) →
      (∀ f ∈ F, ∃ g : β → β, ∀ x, q (f x) = g (q x)) →
      ∀ ⦃x y⦄, UnaryLawClosure F E x y → ObserverKernel q x y) := by
  exact ⟨unaryLawClosure_equivalence, unaryLawClosure_contains,
    (fun F E _ hf ↦ unaryLawClosure_preserves F E hf),
    descended_iff_observerKernel_preserved,
    unaryLawClosure_subset_observerKernel_of_descents⟩

end GaloisForLFunctions.HTGeometry

