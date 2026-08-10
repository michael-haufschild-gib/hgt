import GaloisForLFunctions.HTGeometry.ConstitutiveLawDerivativeGenesis
import GaloisForLFunctions.HTGeometry.ConstitutiveSemanticTransportArityPromotion

namespace GaloisForLFunctions.HTGeometry

universe u v w z

namespace LawContainer

/-- Partial evaluation of an execution reporter in a one-hole context. -/
noncomputable def contextualChallenge (C : LawContainer.{u}) {X : Type u} {Y : Type v}
    (R : Extension C X → Y) (c : OneHoleContext C X) : X → Y :=
  fun x => R (plug C c x)

theorem contextualChallenge_contextOfMarked_original
    (C : LawContainer.{u}) {X : Type u} {Y : Type v}
    (R : Extension C X → Y) (e : Extension C X) (p : C.Pos e.1) :
    contextualChallenge C R (contextOfMarked C e p) (e.2 p) = R e := by
  rw [contextualChallenge, plug_contextOfMarked_restore]

theorem contextualChallenge_not_determined_iff
    (C : LawContainer.{u}) {X : Type u} {Y : Type v} {A : Type w}
    (R : Extension C X → Y) (c : OneHoleContext C X) (a : X → A) :
    ¬ ReporterDeterminedBy a (contextualChallenge C R c) ↔
      ∃ x y, a x = a y ∧ contextualChallenge C R c x ≠ contextualChallenge C R c y := by
  simp only [ReporterDeterminedBy]
  push Not
  rfl

theorem contextualChallenge_strict_contraction_iff
    (C : LawContainer.{u}) {X : Type u} {Y : Type v} {A : Type w}
    (R : Extension C X → Y) (c : OneHoleContext C X) (a : X → A) :
    (∃ f : X → X, ReporterInvisible a f ∧
      ¬ ReporterInvisible (pairedReporter a (contextualChallenge C R c)) f) ↔
      ¬ ReporterDeterminedBy a (contextualChallenge C R c) := by
  exact pairedReporter_strict_contraction_iff a (contextualChallenge C R c)

theorem constantReporter_contextualChallenge_determined
    (C : LawContainer.{u}) {X : Type u} {Y : Type v} {A : Type w}
    (y : Y) (a : X → A) (c : OneHoleContext C X) :
    ReporterDeterminedBy a (contextualChallenge C (fun _ => y) c) := by
  intro x x' h
  rfl

/-- Reporter after exposing the outer context of a composite failure. -/
noncomputable def outerContextualChallenge
    {P Q : LawContainer.{u}} {X : Type u} {Y : Type v}
    (R : CompositeExtension P Q X → Y)
    (e : CompositeExtension P Q X) (z : CompositeSite e) : Extension Q X → Y :=
  contextualChallenge P R (outerFailureContext e z)

/-- Reporter obtained by replacing the marked leaf in a composite execution. -/
noncomputable def leafContextualChallenge
    {P Q : LawContainer.{u}} {X : Type u} {Y : Type v}
    (R : CompositeExtension P Q X → Y)
    (e : CompositeExtension P Q X) (z : CompositeSite e) : X → Y :=
  fun x => R (nestedRepair e z x)

theorem leafContextualChallenge_chain
    {P Q : LawContainer.{u}} {X : Type u} {Y : Type v}
    (R : CompositeExtension P Q X → Y)
    (e : CompositeExtension P Q X) (z : CompositeSite e) :
    leafContextualChallenge R e z =
      contextualChallenge Q (outerContextualChallenge R e z) (innerFailureContext e z) := by
  rfl

theorem contextualChallenge_postcompose
    (C : LawContainer.{u}) {X : Type u} {Y : Type v} {Z : Type z}
    (R : Extension C X → Y) (o : Y → Z) (c : OneHoleContext C X) :
    contextualChallenge C (o ∘ R) c = o ∘ contextualChallenge C R c := by
  rfl

theorem determined_contextualChallenge_postcompose
    (C : LawContainer.{u}) {X : Type u} {Y : Type v} {Z : Type z} {A : Type w}
    (R : Extension C X → Y) (o : Y → Z) (c : OneHoleContext C X) (a : X → A)
    (h : ReporterDeterminedBy a (contextualChallenge C R c)) :
    ReporterDeterminedBy a (contextualChallenge C (o ∘ R) c) := by
  intro x y hxy
  exact congrArg o (h hxy)

theorem observed_effective_implies_source_effective
    (C : LawContainer.{u}) {X : Type u} {Y : Type v} {Z : Type z} {A : Type w}
    (R : Extension C X → Y) (o : Y → Z) (c : OneHoleContext C X) (a : X → A) :
    ¬ ReporterDeterminedBy a (contextualChallenge C (o ∘ R) c) →
      ¬ ReporterDeterminedBy a (contextualChallenge C R c) := by
  exact fun h => mt (determined_contextualChallenge_postcompose C R o c a) h

theorem contextualChallenge_effective_iff_of_injective
    (C : LawContainer.{u}) {X : Type u} {Y : Type v} {Z : Type z} {A : Type w}
    (R : Extension C X → Y) (o : Y → Z) (ho : Function.Injective o)
    (c : OneHoleContext C X) (a : X → A) :
    (¬ ReporterDeterminedBy a (contextualChallenge C (o ∘ R) c)) ↔
      ¬ ReporterDeterminedBy a (contextualChallenge C R c) := by
  constructor
  · exact observed_effective_implies_source_effective C R o c a
  · intro hsource hobserved
    apply hsource
    intro x y hxy
    apply ho
    exact hobserved hxy

def boolUnaryExecution : Extension unaryInnerContainer Bool :=
  ⟨(), fun _ => false⟩

def boolUnaryContext : OneHoleContext unaryInnerContainer Bool :=
  contextOfMarked unaryInnerContainer boolUnaryExecution ()

def readUnaryBool (e : Extension unaryInnerContainer Bool) : Bool :=
  e.2 ()

theorem boolContextualChallenge_eq_id :
    contextualChallenge unaryInnerContainer readUnaryBool boolUnaryContext = id := by
  funext b
  simp [contextualChallenge, boolUnaryContext, boolUnaryExecution, readUnaryBool,
    contextOfMarked, plug]

theorem bool_source_challenge_effective :
    ¬ ReporterDeterminedBy (fun _ : Bool => ())
      (contextualChallenge unaryInnerContainer readUnaryBool boolUnaryContext) := by
  rw [boolContextualChallenge_eq_id]
  intro h
  have hfalseTrue := h (x := false) (y := true) rfl
  exact Bool.false_ne_true hfalseTrue

def eraseBool (_ : Bool) : Unit := ()

theorem bool_observed_challenge_inert :
    ReporterDeterminedBy (fun _ : Bool => ())
      (contextualChallenge unaryInnerContainer (eraseBool ∘ readUnaryBool) boolUnaryContext) := by
  intro x y hxy
  rfl

theorem bool_postobserver_erases_effective_challenge :
    (¬ ReporterDeterminedBy (fun _ : Bool => ())
      (contextualChallenge unaryInnerContainer readUnaryBool boolUnaryContext)) ∧
    ReporterDeterminedBy (fun _ : Bool => ())
      (contextualChallenge unaryInnerContainer (eraseBool ∘ readUnaryBool) boolUnaryContext) := by
  exact ⟨bool_source_challenge_effective, bool_observed_challenge_inert⟩

def optionBoolUnaryExecution : Extension unaryInnerContainer (Option Bool) :=
  ⟨(), fun _ => none⟩

def optionBoolUnaryContext : OneHoleContext unaryInnerContainer (Option Bool) :=
  contextOfMarked unaryInnerContainer optionBoolUnaryExecution ()

def readUnaryNone (e : Extension unaryInnerContainer (Option Bool)) : Prop :=
  e.2 () = none

theorem optionBool_challenge_some_false_eq_some_true :
    contextualChallenge unaryInnerContainer readUnaryNone optionBoolUnaryContext (some false) =
      contextualChallenge unaryInnerContainer readUnaryNone optionBoolUnaryContext (some true) := by
  simp [contextualChallenge, optionBoolUnaryContext, optionBoolUnaryExecution, readUnaryNone,
    contextOfMarked, plug]

theorem optionBool_some_false_ne_some_true :
    (some false : Option Bool) ≠ some true := by
  intro h
  exact Bool.false_ne_true (Option.some.inj h)

theorem contextualChallengeTransduction_closed :
    (∀ (C : LawContainer.{u}) (X : Type u) (Y : Type v)
      (R : Extension C X → Y) (e : Extension C X) (p : C.Pos e.1),
      contextualChallenge C R (contextOfMarked C e p) (e.2 p) = R e) ∧
    (∀ {P Q : LawContainer.{u}} {X : Type u} {Y : Type v}
      (R : CompositeExtension P Q X → Y)
      (e : CompositeExtension P Q X) (z : CompositeSite e),
      leafContextualChallenge R e z =
        contextualChallenge Q (outerContextualChallenge R e z) (innerFailureContext e z)) ∧
    ((¬ ReporterDeterminedBy (fun _ : Bool => ())
      (contextualChallenge unaryInnerContainer readUnaryBool boolUnaryContext)) ∧
    ReporterDeterminedBy (fun _ : Bool => ())
      (contextualChallenge unaryInnerContainer (eraseBool ∘ readUnaryBool) boolUnaryContext)) ∧
    ((some false : Option Bool) ≠ some true ∧
      contextualChallenge unaryInnerContainer readUnaryNone optionBoolUnaryContext (some false) =
        contextualChallenge unaryInnerContainer readUnaryNone optionBoolUnaryContext (some true)) := by
  exact ⟨contextualChallenge_contextOfMarked_original, leafContextualChallenge_chain,
    bool_postobserver_erases_effective_challenge,
    optionBool_some_false_ne_some_true, optionBool_challenge_some_false_eq_some_true⟩

end LawContainer

end GaloisForLFunctions.HTGeometry
