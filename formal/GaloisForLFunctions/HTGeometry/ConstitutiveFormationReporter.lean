import GaloisForLFunctions.HTGeometry.ConstitutiveFormationExchange

/-!
# Formation-reporter conservation

Reporters invariant under every primitive formation are conserved along every finite formation
word. A changed reporter at joint repair therefore certifies a non-finite formation horizon, while
every nontrivial formation triggers a response in any separating reporter coframe.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

def FormationReporterInvariant {α : Type u} {β : Type v}
    (q : Set α → β) (C : ConstitutiveFormation α) : Prop :=
  ∀ s, q (C.act s) = q s

def FormationReporterCoframeSeparates {α : Type u} {β : Type v}
    (R : Set (Set α → β)) : Prop :=
  ∀ s t, (∀ q ∈ R, q s = q t) → s = t

theorem formationReporter_conserved_along_word {α : Type u} {β : Type v}
    {F : Set (ConstitutiveFormation α)} {q : Set α → β}
    (hq : ∀ C ∈ F, FormationReporterInvariant q C)
    {w : List (ConstitutiveFormation α)} (hw : ∀ C ∈ w, C ∈ F) (s : Set α) :
    q (runConstitutiveFormations w s) = q s := by
  induction w generalizing s with
  | nil => rfl
  | cons C rest ih =>
      calc
        q (runConstitutiveFormations (C :: rest) s) =
            q (runConstitutiveFormations rest (C.act s)) := rfl
        _ = q (C.act s) := ih (fun D hD => hw D (by simp [hD])) (C.act s)
        _ = q s := hq C (hw C (by simp)) s

theorem changedJointReporter_forces_infiniteHorizon {α : Type u} {β : Type v}
    {F : Set (ConstitutiveFormation α)} {q : Set α → β}
    (hq : ∀ C ∈ F, FormationReporterInvariant q C) (s : Set α)
    (hchange : q (constitutiveJointRepair F s) ≠ q s) :
    ∀ w : List (ConstitutiveFormation α),
      (∀ C ∈ w, C ∈ F) →
      runConstitutiveFormations w s ≠ constitutiveJointRepair F s := by
  intro w hw heq
  apply hchange
  rw [← heq]
  exact formationReporter_conserved_along_word hq hw s

theorem separatingCoframe_forces_identity {α : Type u} {β : Type v}
    {R : Set (Set α → β)} (hsep : FormationReporterCoframeSeparates R)
    (C : ConstitutiveFormation α)
    (hC : ∀ q ∈ R, FormationReporterInvariant q C) :
    ∀ s, C.act s = s := by
  intro s
  apply hsep
  intro q hq
  exact hC q hq s

theorem nontrivialFormation_hasReporterResponse {α : Type u} {β : Type v}
    {R : Set (Set α → β)} (hsep : FormationReporterCoframeSeparates R)
    (C : ConstitutiveFormation α) (s : Set α) (hne : C.act s ≠ s) :
    ∃ q ∈ R, q (C.act s) ≠ q s := by
  by_contra h
  push Not at h
  exact hne (hsep _ _ h)

theorem constitutiveFormationReporterMechanism_closed {α : Type u} {β : Type v} :
    (∀ (F : Set (ConstitutiveFormation α)) (q : Set α → β),
      (∀ C ∈ F, FormationReporterInvariant q C) →
      ∀ (w : List (ConstitutiveFormation α)),
        (∀ C ∈ w, C ∈ F) → ∀ s,
        q (runConstitutiveFormations w s) = q s) ∧
    (∀ (R : Set (Set α → β)), FormationReporterCoframeSeparates R →
      ∀ (C : ConstitutiveFormation α) (s : Set α), C.act s ≠ s →
      ∃ q ∈ R, q (C.act s) ≠ q s) := by
  exact ⟨(fun F q hq w hw s => formationReporter_conserved_along_word hq hw s),
    (fun R hsep C s hne => nontrivialFormation_hasReporterResponse hsep C s hne)⟩

end GaloisForLFunctions.HTGeometry
