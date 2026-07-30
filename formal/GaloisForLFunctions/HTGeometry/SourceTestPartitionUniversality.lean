import Mathlib.Data.Quot

namespace GaloisForLFunctions.HTGeometry

universe u

/-- A family of tests and the propositions recording which sources respond to them. -/
structure SourceTestPresentation (α : Type u) where
  Test : Type u
  responds : α → Test → Prop

namespace SourceTestPresentation

/-- Two sources are observationally equivalent when every test gives the same response. -/
def ObservationallyEquivalent {α : Type u} (P : SourceTestPresentation α) (a b : α) : Prop :=
  ∀ t, P.responds a t ↔ P.responds b t

/-- Every source-test presentation induces an observational equivalence relation. -/
def observationalSetoid {α : Type u} (P : SourceTestPresentation α) : Setoid α where
  r := P.ObservationallyEquivalent
  iseqv := {
    refl := fun _ _ => Iff.rfl
    symm := fun hab t => (hab t).symm
    trans := fun hab hbc t => (hab t).trans (hbc t)
  }

/-- The quotient-class recognizer associated with an arbitrary identity partition. -/
def quotientRecognizer {α : Type u} (s : Setoid α) : SourceTestPresentation α where
  Test := Quotient s
  responds a q := Quotient.mk s a = q

/-- Every source responds to exactly one quotient-class test. -/
theorem quotientRecognizer_deterministic {α : Type u} (s : Setoid α) (a : α) :
    ∃! q, (quotientRecognizer s).responds a q := by
  refine ⟨Quotient.mk s a, rfl, ?_⟩
  intro q hq
  exact hq.symm

/-- Every quotient-class test is reached by some source. -/
theorem quotientRecognizer_exhaustive {α : Type u} (s : Setoid α) :
    ∀ q, ∃ a, (quotientRecognizer s).responds a q := by
  intro q
  refine Quotient.inductionOn q ?_
  intro a
  exact ⟨a, rfl⟩

/-- The observational equivalence of the quotient recognizer is exactly the chosen partition. -/
theorem quotientRecognizer_observationallyEquivalent_iff {α : Type u} (s : Setoid α)
    (a b : α) :
    (quotientRecognizer s).ObservationallyEquivalent a b ↔ s.r a b := by
  constructor
  · intro h
    have hba : Quotient.mk s b = Quotient.mk s a :=
      (h (Quotient.mk s a)).mp rfl
    exact s.symm (Quotient.exact hba)
  · intro hab q
    have habq : Quotient.mk s a = Quotient.mk s b := Quotient.sound hab
    constructor
    · intro ha
      calc
        Quotient.mk s b = Quotient.mk s a := habq.symm
        _ = q := ha
    · intro hb
      calc
        Quotient.mk s a = Quotient.mk s b := habq
        _ = q := hb

/-- The setoid induced by the quotient recognizer is the original setoid. -/
theorem quotientRecognizer_observationalSetoid_eq {α : Type u} (s : Setoid α) :
    (quotientRecognizer s).observationalSetoid = s := by
  apply Setoid.ext
  intro a b
  exact quotientRecognizer_observationallyEquivalent_iff s a b

/-- Every identity partition has a deterministic, exhaustive, exact source-test presentation. -/
theorem everySetoid_has_perfect_sourceTestPresentation {α : Type u} (s : Setoid α) :
    ∃ P : SourceTestPresentation α,
      (∀ a, ∃! t, P.responds a t) ∧
      (∀ t, ∃ a, P.responds a t) ∧
      (∀ a b, P.ObservationallyEquivalent a b ↔ s.r a b) := by
  refine ⟨quotientRecognizer s, ?_, ?_, ?_⟩
  · exact quotientRecognizer_deterministic s
  · exact quotientRecognizer_exhaustive s
  · exact quotientRecognizer_observationallyEquivalent_iff s

end SourceTestPresentation

end GaloisForLFunctions.HTGeometry
