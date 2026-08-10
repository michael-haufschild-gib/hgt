import GaloisForLFunctions.HTGeometry.ConstitutiveRelationalLawRenormalization
import GaloisForLFunctions.HTGeometry.ConstitutiveUnaryLawRepair

/-!
# Bipolar observer repair

A family of unary laws induces two canonical repairs of an observer equivalence: the least
law-invariant coarsening and the greatest law-invariant refinement.  They absorb in opposite order,
so the two repair schedules agree exactly when the original observer already admits every law.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- Execute a finite word of unary laws.  The head acts first. -/
def UnaryLawWordRun {α : Type u} : List (α → α) → α → α
  | [], x => x
  | f :: tail, x => UnaryLawWordRun tail (f x)

@[simp] theorem unaryLawWordRun_nil {α : Type u} (x : α) :
    UnaryLawWordRun ([] : List (α → α)) x = x := rfl

@[simp] theorem unaryLawWordRun_cons {α : Type u} (f : α → α)
    (tail : List (α → α)) (x : α) :
    UnaryLawWordRun (f :: tail) x = UnaryLawWordRun tail (f x) := rfl

/-- Every letter of a word belongs to the declared law family. -/
def UnaryLawWordAdmitted {α : Type u} (F : Set (α → α))
    (word : List (α → α)) : Prop :=
  ∀ f ∈ word, f ∈ F

/-- Greatest law-invariant relation contained in `E`: every admitted future word still sees `E`. -/
def UnaryLawInterior {α : Type u} (F : Set (α → α)) (E : α → α → Prop) :
    α → α → Prop :=
  fun x y ↦ ∀ word, UnaryLawWordAdmitted F word →
    E (UnaryLawWordRun word x) (UnaryLawWordRun word y)

theorem unaryLawInterior_equivalence {α : Type u} (F : Set (α → α))
    (E : α → α → Prop) (hE : Equivalence E) :
    Equivalence (UnaryLawInterior F E) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x word hword
    exact hE.refl _
  · intro x y hxy word hword
    exact hE.symm (hxy word hword)
  · intro x y z hxy hyz word hword
    exact hE.trans (hxy word hword) (hyz word hword)

theorem unaryLawInterior_subset {α : Type u} (F : Set (α → α))
    (E : α → α → Prop) :
    ∀ ⦃x y⦄, UnaryLawInterior F E x y → E x y := by
  intro x y hxy
  exact hxy [] (by simp [UnaryLawWordAdmitted])

theorem unaryLawInterior_preserves {α : Type u} (F : Set (α → α))
    (E : α → α → Prop) {f : α → α} (hf : f ∈ F) :
    UnaryPreserves f (UnaryLawInterior F E) := by
  intro x y hxy word hword
  apply hxy (f :: word)
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hf
  · exact hword g hg

/-- The future interior is the greatest invariant equivalence contained in the observer. -/
theorem unaryLawInterior_greatest {α : Type u} {F : Set (α → α)}
    {E R : α → α → Prop} (_hR : Equivalence R)
    (hRE : ∀ ⦃x y⦄, R x y → E x y)
    (hF : ∀ f ∈ F, UnaryPreserves f R) :
    ∀ ⦃x y⦄, R x y → UnaryLawInterior F E x y := by
  intro x y hxy word hword
  induction word generalizing x y with
  | nil => exact hRE hxy
  | cons f tail ih =>
      apply ih (hF f (hword f (by simp)) hxy)
      intro g hg
      exact hword g (by simp [hg])

theorem unaryLawInterior_fixed_iff {α : Type u} (F : Set (α → α))
    (E : α → α → Prop) (hE : Equivalence E) :
    UnaryLawInterior F E = E ↔ ∀ f ∈ F, UnaryPreserves f E := by
  constructor
  · intro h f hf
    rw [← h]
    exact unaryLawInterior_preserves F E hf
  · intro hF
    funext x y
    apply propext
    constructor
    · intro hxy
      exact unaryLawInterior_subset F E hxy
    · intro hxy
      exact unaryLawInterior_greatest hE (fun {_ _} h ↦ h) hF hxy

/-- Coarsening after the invariant refinement is inert. -/
theorem unaryLawClosure_interior_absorb {α : Type u} (F : Set (α → α))
    (E : α → α → Prop) (hE : Equivalence E) :
    UnaryLawClosure F (UnaryLawInterior F E) = UnaryLawInterior F E := by
  apply (unaryLawClosure_fixed_iff F (UnaryLawInterior F E)
    (unaryLawInterior_equivalence F E hE)).2
  intro f hf
  exact unaryLawInterior_preserves F E hf

/-- Refining after the invariant coarsening is inert. -/
theorem unaryLawInterior_closure_absorb {α : Type u} (F : Set (α → α))
    (E : α → α → Prop) :
    UnaryLawInterior F (UnaryLawClosure F E) = UnaryLawClosure F E := by
  apply (unaryLawInterior_fixed_iff F (UnaryLawClosure F E)
    (unaryLawClosure_equivalence F E)).2
  intro f hf
  exact unaryLawClosure_preserves F E hf

/-- The two opposite repair schedules agree exactly in the already executable chamber. -/
theorem bipolarRepair_exchange_iff {α : Type u} (F : Set (α → α))
    (E : α → α → Prop) (hE : Equivalence E) :
    UnaryLawClosure F (UnaryLawInterior F E) =
        UnaryLawInterior F (UnaryLawClosure F E) ↔
      ∀ f ∈ F, UnaryPreserves f E := by
  rw [unaryLawClosure_interior_absorb F E hE,
    unaryLawInterior_closure_absorb F E]
  constructor
  · intro h
    apply (unaryLawClosure_fixed_iff F E hE).1
    funext x y
    apply propext
    constructor
    · intro hxy
      apply unaryLawInterior_subset F E
      rw [h]
      exact hxy
    · intro hxy
      exact unaryLawClosure_contains F E hxy
  · intro hF
    rw [(unaryLawInterior_fixed_iff F E hE).2 hF,
      (unaryLawClosure_fixed_iff F E hE).2 hF]

/-- Smallest cell in which fine and coarse deterministic repair reach opposite extremes. -/
inductive BipolarRepairState where
  | a
  | b
  | c
  deriving DecidableEq

def bipolarRepairStep : BipolarRepairState → BipolarRepairState
  | .a => .a
  | .b => .c
  | .c => .c

def bipolarRepairObserver : BipolarRepairState → Bool
  | .a => false
  | .b => false
  | .c => true

def BipolarRepairRelation : BipolarRepairState → BipolarRepairState → Prop :=
  ObserverKernel bipolarRepairObserver

theorem bipolarRepairRelation_equivalence : Equivalence BipolarRepairRelation :=
  observerKernel_equivalence bipolarRepairObserver

theorem bipolarRepairStep_not_preserves :
    ¬ UnaryPreserves bipolarRepairStep BipolarRepairRelation := by
  intro h
  have hab : BipolarRepairRelation .a .b := rfl
  have hbad := h hab
  simp [BipolarRepairRelation, ObserverKernel, bipolarRepairStep,
    bipolarRepairObserver] at hbad

theorem bipolarRepairInterior_eq_equality :
    UnaryLawInterior ({bipolarRepairStep} : Set (BipolarRepairState → BipolarRepairState))
      BipolarRepairRelation = Eq := by
  funext x y
  apply propext
  constructor
  · intro hxy
    have hnow : bipolarRepairObserver x = bipolarRepairObserver y :=
      hxy [] (by simp [UnaryLawWordAdmitted])
    have hnext :
        bipolarRepairObserver (bipolarRepairStep x) =
          bipolarRepairObserver (bipolarRepairStep y) := by
      simpa [BipolarRepairRelation, ObserverKernel] using
        hxy [bipolarRepairStep] (by simp [UnaryLawWordAdmitted])
    cases x <;> cases y <;>
      simp [bipolarRepairObserver, bipolarRepairStep] at hnow hnext ⊢
  · intro hxy
    subst y
    exact (unaryLawInterior_equivalence _ _ bipolarRepairRelation_equivalence).refl x

theorem bipolarRepairClosure_eq_universal :
    UnaryLawClosure ({bipolarRepairStep} : Set (BipolarRepairState → BipolarRepairState))
      BipolarRepairRelation = fun _ _ ↦ True := by
  let F : Set (BipolarRepairState → BipolarRepairState) := {bipolarRepairStep}
  let C := UnaryLawClosure F BipolarRepairRelation
  have hC : Equivalence C := unaryLawClosure_equivalence F BipolarRepairRelation
  have hab : C .a .b := unaryLawClosure_contains F BipolarRepairRelation rfl
  have hpres : UnaryPreserves bipolarRepairStep C :=
    unaryLawClosure_preserves F BipolarRepairRelation (by simp [F])
  have hac : C .a .c := by
    simpa [bipolarRepairStep] using hpres hab
  have hbc : C .b .c := hC.trans (hC.symm hab) hac
  funext x y
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    cases x <;> cases y
    · exact hC.refl .a
    · exact hab
    · exact hac
    · exact hC.symm hab
    · exact hC.refl .b
    · exact hbc
    · exact hC.symm hac
    · exact hC.symm hbc
    · exact hC.refl .c

theorem bipolarRepair_fine_then_coarse_eq_equality :
    UnaryLawClosure ({bipolarRepairStep} : Set (BipolarRepairState → BipolarRepairState))
        (UnaryLawInterior ({bipolarRepairStep} :
          Set (BipolarRepairState → BipolarRepairState)) BipolarRepairRelation) = Eq := by
  rw [unaryLawClosure_interior_absorb _ _ bipolarRepairRelation_equivalence,
    bipolarRepairInterior_eq_equality]

theorem bipolarRepair_coarse_then_fine_eq_universal :
    UnaryLawInterior ({bipolarRepairStep} : Set (BipolarRepairState → BipolarRepairState))
        (UnaryLawClosure ({bipolarRepairStep} :
          Set (BipolarRepairState → BipolarRepairState)) BipolarRepairRelation) =
      fun _ _ ↦ True := by
  rw [unaryLawInterior_closure_absorb, bipolarRepairClosure_eq_universal]

theorem bipolarRepair_observedLaw_not_rightUnique :
    ¬ LawRelationRightUnique
      (EffectiveLawRelation bipolarRepairObserver bipolarRepairStep) := by
  rw [effectiveLawRelation_rightUnique_iff_kernelPreserved]
  exact bipolarRepairStep_not_preserves

/-- Unconditional capstone: generic opposite absorption and the exact maximal three-state cell. -/
theorem bipolarObserverRepair_unconditional :
    (∀ (α : Type u) (F : Set (α → α)) (E : α → α → Prop), Equivalence E →
      UnaryLawClosure F (UnaryLawInterior F E) = UnaryLawInterior F E) ∧
    (∀ (α : Type u) (F : Set (α → α)) (E : α → α → Prop),
      UnaryLawInterior F (UnaryLawClosure F E) = UnaryLawClosure F E) ∧
    (∀ (α : Type u) (F : Set (α → α)) (E : α → α → Prop), Equivalence E →
      (UnaryLawClosure F (UnaryLawInterior F E) =
          UnaryLawInterior F (UnaryLawClosure F E) ↔
        ∀ f ∈ F, UnaryPreserves f E)) ∧
    UnaryLawInterior ({bipolarRepairStep} :
        Set (BipolarRepairState → BipolarRepairState)) BipolarRepairRelation = Eq ∧
    UnaryLawClosure ({bipolarRepairStep} :
        Set (BipolarRepairState → BipolarRepairState)) BipolarRepairRelation =
      (fun _ _ ↦ True) ∧
    (¬ LawRelationRightUnique
      (EffectiveLawRelation bipolarRepairObserver bipolarRepairStep)) := by
  exact ⟨(fun _ F E hE ↦ unaryLawClosure_interior_absorb F E hE),
    (fun _ F E ↦ unaryLawInterior_closure_absorb F E),
    (fun _ F E hE ↦ bipolarRepair_exchange_iff F E hE),
    bipolarRepairInterior_eq_equality,
    bipolarRepairClosure_eq_universal,
    bipolarRepair_observedLaw_not_rightUnique⟩

end GaloisForLFunctions.HTGeometry
