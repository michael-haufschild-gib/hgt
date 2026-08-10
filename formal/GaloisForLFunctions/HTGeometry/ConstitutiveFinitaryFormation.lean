import Mathlib.Order.Closure
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Finite.Basic

/-!
# Finitary formation and cofinal law birth

This module formalizes the finitary-formation barrier for constitutive process mathematics.
Any finite word in monotone finitary formations is finitary.  If the formations are also
extensive, their finite-word joint saturation is a finitary closure operator and is the least
closure operator containing every formation.  A concrete closure on `Set ℕ` witnesses the sharp
boundary: it adjoins `0` exactly to infinite sets, so its birth at the positive naturals has no
finite witness and cannot be any such joint saturation.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- A formation is finitary when each individual consequence has a finite source witness. -/
def IsFinitaryFormation {α : Type u} (f : Set α → Set α) : Prop :=
  ∀ ⦃A : Set α⦄ ⦃x : α⦄, x ∈ f A →
    ∃ F : Finset α, (F : Set α) ⊆ A ∧ x ∈ f (F : Set α)

/-- A formation is extensive when it retains every input law. -/
def IsExtensiveFormation {α : Type u} (f : Set α → Set α) : Prop :=
  ∀ A, A ⊆ f A

/-- Execute a finite word of formation rules from left to right. -/
def runFormations {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (w : List ι) (A : Set α) : Set α :=
  w.foldl (fun S i => φ i S) A

@[simp] theorem runFormations_nil {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (A : Set α) :
    runFormations φ [] A = A := rfl

@[simp] theorem runFormations_cons {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (i : ι) (w : List ι) (A : Set α) :
    runFormations φ (i :: w) A = runFormations φ w (φ i A) := rfl

theorem runFormations_append {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (u w : List ι) (A : Set α) :
    runFormations φ (u ++ w) A = runFormations φ w (runFormations φ u A) := by
  simp [runFormations, List.foldl_append]

theorem runFormations_monotone {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (hmono : ∀ i, Monotone (φ i)) (w : List ι) :
    Monotone (runFormations φ w) := by
  induction w with
  | nil => exact monotone_id
  | cons i w ih =>
      intro A B hAB
      exact ih (hmono i hAB)

theorem runFormations_extensive {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (hext : ∀ i, IsExtensiveFormation (φ i))
    (w : List ι) (A : Set α) :
    A ⊆ runFormations φ w A := by
  induction w generalizing A with
  | nil => exact Subset.rfl
  | cons i w ih => exact (hext i A).trans (ih (φ i A))

/-- The composite of two monotone finitary formations is finitary. -/
theorem finitaryFormation_comp {α : Type u} (f g : Set α → Set α)
    (hfmono : Monotone f) (hgmono : Monotone g)
    (hf : IsFinitaryFormation f) (hg : IsFinitaryFormation g) :
    IsFinitaryFormation (g ∘ f) := by
  classical
  intro A x hx
  obtain ⟨E, hEA, hxE⟩ := hg hx
  let F : α → Finset α := fun e =>
    if he : e ∈ E then Classical.choose (hf (hEA he)) else ∅
  let U : Finset α := E.biUnion F
  have hUsub : (U : Set α) ⊆ A := by
    intro a ha
    simp only [U, Finset.mem_coe, Finset.mem_biUnion] at ha
    obtain ⟨e, heE, haF⟩ := ha
    have hspec := Classical.choose_spec (hf (hEA heE))
    have hFe : F e = Classical.choose (hf (hEA heE)) := by
      simp only [F, dif_pos heE]
    exact hspec.1 (hFe ▸ haF)
  have hEsub : (E : Set α) ⊆ f (U : Set α) := by
    intro e heE
    change e ∈ E at heE
    have hspec := Classical.choose_spec (hf (hEA heE))
    have hFU :
        ((↑(Classical.choose (hf (hEA heE)))) : Set α) ⊆ (U : Set α) := by
      intro a ha
      simp only [U, Finset.mem_coe, Finset.mem_biUnion]
      refine ⟨e, heE, ?_⟩
      have hFe : F e = Classical.choose (hf (hEA heE)) := by
        simp only [F, dif_pos heE]
      exact hFe.symm ▸ ha
    exact hfmono hFU hspec.2
  refine ⟨U, hUsub, ?_⟩
  exact hgmono hEsub hxE

/-- Every finite formation history has finite source ancestry. -/
theorem runFormations_finitary {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (hmono : ∀ i, Monotone (φ i))
    (hfin : ∀ i, IsFinitaryFormation (φ i)) (w : List ι) :
    IsFinitaryFormation (runFormations φ w) := by
  induction w with
  | nil =>
      intro A x hx
      change x ∈ A at hx
      exact ⟨{x}, by simp [hx], by simp⟩
  | cons i w ih =>
      exact finitaryFormation_comp (φ i) (runFormations φ w)
        (hmono i) (runFormations_monotone φ hmono w) (hfin i) ih

/-- Joint saturation by all finite words in a family of formations. -/
def wordSaturation {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (A : Set α) : Set α :=
  {x | ∃ w : List ι, x ∈ runFormations φ w A}

/-- Arbitrarily many rule types still give finite ancestry when only finite histories are admitted. -/
theorem wordSaturation_finitary {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (hmono : ∀ i, Monotone (φ i))
    (hfin : ∀ i, IsFinitaryFormation (φ i)) :
    IsFinitaryFormation (wordSaturation φ) := by
  intro A x hx
  obtain ⟨w, hxw⟩ := hx
  obtain ⟨F, hFA, hxF⟩ := runFormations_finitary φ hmono hfin w hxw
  exact ⟨F, hFA, ⟨w, hxF⟩⟩

theorem finite_subset_wordSaturation_captured {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (hmono : ∀ i, Monotone (φ i))
    (hext : ∀ i, IsExtensiveFormation (φ i)) (A : Set α) (E : Finset α)
    (hE : (E : Set α) ⊆ wordSaturation φ A) :
    ∃ w : List ι, (E : Set α) ⊆ runFormations φ w A := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨[], by simp⟩
  | @insert e E he ih =>
      have heSat : e ∈ wordSaturation φ A :=
        hE (show e ∈ (insert e E : Finset α) by simp)
      obtain ⟨we, hwe⟩ := heSat
      obtain ⟨wE, hwE⟩ := ih (fun a ha => hE (by simp [ha]))
      refine ⟨wE ++ we, ?_⟩
      intro a ha
      rw [runFormations_append]
      rcases Finset.mem_insert.mp ha with rfl | haE
      · exact (runFormations_monotone φ hmono we)
          (runFormations_extensive φ hext wE A) hwe
      · exact (runFormations_extensive φ hext we (runFormations φ wE A)) (hwE haE)

theorem formation_maps_wordSaturation_into_self {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (hmono : ∀ i, Monotone (φ i))
    (hext : ∀ i, IsExtensiveFormation (φ i))
    (hfin : ∀ i, IsFinitaryFormation (φ i)) (i : ι) (A : Set α) :
    φ i (wordSaturation φ A) ⊆ wordSaturation φ A := by
  classical
  intro x hx
  obtain ⟨E, hE, hxE⟩ := hfin i hx
  obtain ⟨w, hw⟩ := finite_subset_wordSaturation_captured φ hmono hext A E hE
  refine ⟨w ++ [i], ?_⟩
  rw [runFormations_append]
  exact hmono i hw hxE

theorem runFormations_wordSaturation_subset {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (hmono : ∀ i, Monotone (φ i))
    (hext : ∀ i, IsExtensiveFormation (φ i))
    (hfin : ∀ i, IsFinitaryFormation (φ i)) (w : List ι) (A : Set α) :
    runFormations φ w (wordSaturation φ A) ⊆ wordSaturation φ A := by
  induction w with
  | nil => exact Subset.rfl
  | cons i w ih =>
      exact (runFormations_monotone φ hmono w
        (formation_maps_wordSaturation_into_self φ hmono hext hfin i A)).trans ih

theorem wordSaturation_extensive {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (A : Set α) :
    A ⊆ wordSaturation φ A := by
  intro x hx
  exact ⟨[], hx⟩

theorem wordSaturation_monotone {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (hmono : ∀ i, Monotone (φ i)) :
    Monotone (wordSaturation φ) := by
  intro A B hAB x hx
  obtain ⟨w, hxw⟩ := hx
  exact ⟨w, runFormations_monotone φ hmono w hAB hxw⟩

theorem wordSaturation_idempotent {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (hmono : ∀ i, Monotone (φ i))
    (hext : ∀ i, IsExtensiveFormation (φ i))
    (hfin : ∀ i, IsFinitaryFormation (φ i)) (A : Set α) :
    wordSaturation φ (wordSaturation φ A) = wordSaturation φ A := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨w, hxw⟩ := hx
    exact runFormations_wordSaturation_subset φ hmono hext hfin w A hxw
  · exact wordSaturation_extensive φ (wordSaturation φ A)

/-- Least closure obtained by all finite histories in a family of extensive finitary formations. -/
def wordSaturationClosure {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (hmono : ∀ i, Monotone (φ i))
    (hext : ∀ i, IsExtensiveFormation (φ i))
    (hfin : ∀ i, IsFinitaryFormation (φ i)) :
    ClosureOperator (Set α) where
  toFun := wordSaturation φ
  monotone' := wordSaturation_monotone φ hmono
  le_closure' := wordSaturation_extensive φ
  idempotent' := wordSaturation_idempotent φ hmono hext hfin

/-- Finite-word joint saturation cannot cross the finitarity boundary. -/
theorem wordSaturationClosure_finitary {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (hmono : ∀ i, Monotone (φ i))
    (hext : ∀ i, IsExtensiveFormation (φ i))
    (hfin : ∀ i, IsFinitaryFormation (φ i)) :
    IsFinitaryFormation (wordSaturationClosure φ hmono hext hfin) :=
  wordSaturation_finitary φ hmono hfin

theorem runFormations_le_of_le_closure {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (c : ClosureOperator (Set α))
    (hφc : ∀ i A, φ i A ⊆ c A) (w : List ι) (A : Set α) :
    runFormations φ w A ⊆ c A := by
  induction w generalizing A with
  | nil => exact c.le_closure A
  | cons i w ih =>
      exact (ih (φ i A)).trans <| by
        simpa only [c.idempotent A] using c.monotone (hφc i A)

/-- Finite-word saturation is the least closure containing every generating formation. -/
theorem wordSaturationClosure_least {α : Type u} {ι : Type v}
    (φ : ι → Set α → Set α) (c : ClosureOperator (Set α))
    (hφc : ∀ i A, φ i A ⊆ c A) (A : Set α) :
    wordSaturation φ A ⊆ c A := by
  rintro x ⟨w, hxw⟩
  exact runFormations_le_of_le_closure φ c hφc w A hxw

/-- A closure with a genuinely cofinal birth: `0` appears exactly when the source is infinite. -/
noncomputable def cofinalBirth (A : Set ℕ) : Set ℕ := by
  classical
  exact A ∪ if A.Infinite then {0} else ∅

theorem cofinalBirth_monotone : Monotone cofinalBirth := by
  classical
  intro A B hAB
  by_cases hA : A.Infinite
  · have hB : B.Infinite := hA.mono hAB
    simp only [cofinalBirth, if_pos hA, if_pos hB]
    exact union_subset_union hAB Subset.rfl
  · simp only [cofinalBirth, if_neg hA, union_empty]
    exact hAB.trans subset_union_left

theorem cofinalBirth_extensive (A : Set ℕ) : A ⊆ cofinalBirth A := by
  classical
  exact subset_union_left

theorem cofinalBirth_idempotent (A : Set ℕ) :
    cofinalBirth (cofinalBirth A) = cofinalBirth A := by
  classical
  by_cases hA : A.Infinite
  · have hCA : cofinalBirth A = A ∪ {0} := by simp [cofinalBirth, hA]
    have hI : (insert 0 A).Infinite := hA.mono (subset_insert 0 A)
    have hC2 : cofinalBirth (A ∪ {0}) = A ∪ {0} := by
      apply Set.Subset.antisymm
      · simp [cofinalBirth, hI]
      · exact cofinalBirth_extensive (A ∪ {0})
    calc
      cofinalBirth (cofinalBirth A) = cofinalBirth (A ∪ {0}) := congrArg cofinalBirth hCA
      _ = A ∪ {0} := hC2
      _ = cofinalBirth A := hCA.symm
  · have hCA : cofinalBirth A = A := by simp [cofinalBirth, hA]
    exact congrArg cofinalBirth hCA

/-- Closure operator whose distinguished birth is not finitary. -/
def cofinalBirthClosure : ClosureOperator (Set ℕ) where
  toFun := cofinalBirth
  monotone' := cofinalBirth_monotone
  le_closure' := cofinalBirth_extensive
  idempotent' := cofinalBirth_idempotent

/-- Positive naturals, presented as the range of successor. -/
def positiveNaturals : Set ℕ := Set.range Nat.succ

theorem positiveNaturals_infinite : positiveNaturals.Infinite := by
  exact infinite_range_of_injective Nat.succ_injective

theorem zero_not_mem_positiveNaturals : 0 ∉ positiveNaturals := by
  simp [positiveNaturals]

/-- The cofinal law `0` is born from all positive naturals. -/
theorem zero_mem_cofinalBirth_positiveNaturals :
    0 ∈ cofinalBirth positiveNaturals := by
  classical
  simp [cofinalBirth, positiveNaturals_infinite]

/-- No finite subset of the positive naturals witnesses the birth of `0`. -/
theorem cofinalBirth_not_finitary : ¬ IsFinitaryFormation cofinalBirth := by
  classical
  intro hfin
  obtain ⟨F, hFsub, hzero⟩ := hfin zero_mem_cofinalBirth_positiveNaturals
  have hFnotInf : ¬ ((F : Set ℕ).Infinite) := F.finite_toSet.not_infinite
  have hzeroF : 0 ∈ (F : Set ℕ) := by
    simpa [cofinalBirth, hFnotInf] using hzero
  exact zero_not_mem_positiveNaturals (hFsub hzeroF)

theorem cofinalBirthClosure_not_finitary :
    ¬ IsFinitaryFormation cofinalBirthClosure :=
  cofinalBirth_not_finitary

/--
The sharp barrier: no family of monotone, extensive, finitary formations has the cofinal-birth
closure as its finite-history joint saturation.
-/
theorem cofinalBirth_ne_wordSaturationClosure {ι : Type v}
    (φ : ι → Set ℕ → Set ℕ) (hmono : ∀ i, Monotone (φ i))
    (hext : ∀ i, IsExtensiveFormation (φ i))
    (hfin : ∀ i, IsFinitaryFormation (φ i)) :
    wordSaturationClosure φ hmono hext hfin ≠ cofinalBirthClosure := by
  intro h
  apply cofinalBirthClosure_not_finitary
  have hJoint := wordSaturationClosure_finitary φ hmono hext hfin
  rw [h] at hJoint
  exact hJoint

end GaloisForLFunctions.HTGeometry
