import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

/-!
# Formation exchange and joint repair

Law formations are extensive, monotone, idempotent transformations of distinctions.  Their joint
repair is the least common fixed point above the source state.  Every finite formation schedule
stays below that repair, while commuting formations reach it in either two-step order.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

/-- An idempotent law-forming process on observable distinctions. -/
structure ConstitutiveFormation (α : Type u) where
  act : Set α → Set α
  extensive : ∀ s, s ⊆ act s
  monotone' : Monotone act
  idempotent : ∀ s, act (act s) = act s

/-- Least common repair above `s` for every formation in `F`. -/
def constitutiveJointRepair {α : Type u} (F : Set (ConstitutiveFormation α))
    (s : Set α) : Set α :=
  {x | ∀ t, s ⊆ t → (∀ C ∈ F, C.act t = t) → x ∈ t}

theorem constitutiveJointRepair_contains {α : Type u}
    (F : Set (ConstitutiveFormation α)) (s : Set α) :
    s ⊆ constitutiveJointRepair F s := by
  intro x hx t hst _
  exact hst hx

theorem constitutiveJointRepair_least {α : Type u}
    {F : Set (ConstitutiveFormation α)} {s t : Set α}
    (hst : s ⊆ t) (ht : ∀ C ∈ F, C.act t = t) :
    constitutiveJointRepair F s ⊆ t := by
  intro x hx
  exact hx t hst ht

theorem constitutiveJointRepair_fixed {α : Type u}
    {F : Set (ConstitutiveFormation α)} (s : Set α)
    {C : ConstitutiveFormation α} (hC : C ∈ F) :
    C.act (constitutiveJointRepair F s) = constitutiveJointRepair F s := by
  apply Set.Subset.antisymm
  · intro x hx t hst ht
    have hJt : constitutiveJointRepair F s ⊆ t :=
      constitutiveJointRepair_least hst ht
    have hx' : x ∈ C.act t := C.monotone' hJt hx
    simpa [ht C hC] using hx'
  · exact C.extensive _

theorem constitutiveJointRepair_mono {α : Type u}
    {F : Set (ConstitutiveFormation α)} {s t : Set α} (hst : s ⊆ t) :
    constitutiveJointRepair F s ⊆ constitutiveJointRepair F t := by
  apply constitutiveJointRepair_least
  · exact hst.trans (constitutiveJointRepair_contains F t)
  · intro C hC
    exact constitutiveJointRepair_fixed t hC

/-- Execute a formation word from left to right. -/
def runConstitutiveFormations {α : Type u} :
    List (ConstitutiveFormation α) → Set α → Set α
  | [], s => s
  | C :: rest, s => runConstitutiveFormations rest (C.act s)

theorem runConstitutiveFormations_subset_of_commonFixed {α : Type u}
    {F : Set (ConstitutiveFormation α)} {w : List (ConstitutiveFormation α)}
    (hw : ∀ C ∈ w, C ∈ F) {s t : Set α} (hst : s ⊆ t)
    (ht : ∀ C ∈ F, C.act t = t) : runConstitutiveFormations w s ⊆ t := by
  induction w generalizing s with
  | nil => exact hst
  | cons C rest ih =>
      apply ih
      · intro D hD
        exact hw D (by simp [hD])
      · have hCt : C.act t = t := ht C (hw C (by simp))
        simpa [hCt] using C.monotone' hst

theorem everyFormationSchedule_below_jointRepair {α : Type u}
    {F : Set (ConstitutiveFormation α)} {w : List (ConstitutiveFormation α)}
    (hw : ∀ C ∈ w, C ∈ F) (s : Set α) :
    runConstitutiveFormations w s ⊆ constitutiveJointRepair F s := by
  apply runConstitutiveFormations_subset_of_commonFixed hw
    (constitutiveJointRepair_contains F s)
  intro C hC
  exact constitutiveJointRepair_fixed s hC

def constitutivePairFamily {α : Type u}
    (C D : ConstitutiveFormation α) : Set (ConstitutiveFormation α) :=
  {C, D}

theorem commutingFormations_jointRepair {α : Type u}
    (C D : ConstitutiveFormation α)
    (hcomm : ∀ s, C.act (D.act s) = D.act (C.act s)) (s : Set α) :
    constitutiveJointRepair (constitutivePairFamily C D) s = D.act (C.act s) := by
  have hsComp : s ⊆ D.act (C.act s) :=
    (C.extensive s).trans (D.extensive (C.act s))
  have hCComp : C.act (D.act (C.act s)) = D.act (C.act s) := by
    rw [hcomm, C.idempotent]
  have hDComp : D.act (D.act (C.act s)) = D.act (C.act s) := D.idempotent _
  apply Set.Subset.antisymm
  · apply constitutiveJointRepair_least hsComp
    intro E hE
    have h : E = C ∨ E = D := by
      simpa [constitutivePairFamily] using hE
    rcases h with rfl | rfl
    · exact hCComp
    · exact hDComp
  · have hsJ : s ⊆ constitutiveJointRepair (constitutivePairFamily C D) s :=
      constitutiveJointRepair_contains _ _
    have hCJ := constitutiveJointRepair_fixed s
      (show C ∈ constitutivePairFamily C D by simp [constitutivePairFamily])
    have hDJ := constitutiveJointRepair_fixed s
      (show D ∈ constitutivePairFamily C D by simp [constitutivePairFamily])
    have hmonoC := C.monotone' hsJ
    have hmonoD := D.monotone' hmonoC
    simpa [hCJ, hDJ] using hmonoD

theorem commutingFormations_orderIndependent {α : Type u}
    (C D : ConstitutiveFormation α)
    (hcomm : ∀ s, C.act (D.act s) = D.act (C.act s)) (s : Set α) :
    runConstitutiveFormations [C, D] s = runConstitutiveFormations [D, C] s ∧
      runConstitutiveFormations [C, D] s =
        constitutiveJointRepair (constitutivePairFamily C D) s := by
  constructor
  · simpa [runConstitutiveFormations] using (hcomm s).symm
  · simpa [runConstitutiveFormations] using
      (commutingFormations_jointRepair C D hcomm s).symm

theorem formations_commute_iff_twoOrders_are_jointRepair {α : Type u}
    (C D : ConstitutiveFormation α) :
    (∀ s, C.act (D.act s) = D.act (C.act s)) ↔
      ∀ s,
        runConstitutiveFormations [C, D] s =
          constitutiveJointRepair (constitutivePairFamily C D) s ∧
        runConstitutiveFormations [D, C] s =
          constitutiveJointRepair (constitutivePairFamily C D) s := by
  constructor
  · intro hcomm s
    have h := commutingFormations_orderIndependent C D hcomm s
    exact ⟨h.2, h.1.symm.trans h.2⟩
  · intro h s
    have hs := h s
    simpa [runConstitutiveFormations] using hs.2.trans hs.1.symm

theorem failedExchange_is_orderedHistory {α : Type u}
    (C D : ConstitutiveFormation α) (s : Set α)
    (h : C.act (D.act s) ≠ D.act (C.act s)) :
    runConstitutiveFormations [C, D] s ≠ runConstitutiveFormations [D, C] s := by
  simpa [runConstitutiveFormations] using h.symm

def constitutiveTripleFamily {α : Type u}
    (C D E : ConstitutiveFormation α) : Set (ConstitutiveFormation α) :=
  {C, D, E}

theorem pairwiseCommutingThree_jointRepair {α : Type u}
    (C D E : ConstitutiveFormation α)
    (hCD : ∀ s, C.act (D.act s) = D.act (C.act s))
    (hCE : ∀ s, C.act (E.act s) = E.act (C.act s))
    (hDE : ∀ s, D.act (E.act s) = E.act (D.act s)) (s : Set α) :
    constitutiveJointRepair (constitutiveTripleFamily C D E) s =
      E.act (D.act (C.act s)) := by
  let u := E.act (D.act (C.act s))
  have hsu : s ⊆ u :=
    (C.extensive s).trans
      ((D.extensive (C.act s)).trans (E.extensive (D.act (C.act s))))
  have hCu : C.act u = u := by
    dsimp [u]
    rw [hCE, hCD, C.idempotent]
  have hDu : D.act u = u := by
    dsimp [u]
    rw [hDE, D.idempotent]
  have hEu : E.act u = u := E.idempotent _
  apply Set.Subset.antisymm
  · apply constitutiveJointRepair_least hsu
    intro A hA
    have h : A = C ∨ A = D ∨ A = E := by
      simpa [constitutiveTripleFamily] using hA
    rcases h with rfl | rfl | rfl
    · exact hCu
    · exact hDu
    · exact hEu
  · have hsJ : s ⊆ constitutiveJointRepair (constitutiveTripleFamily C D E) s :=
      constitutiveJointRepair_contains _ _
    have hCJ := constitutiveJointRepair_fixed s
      (show C ∈ constitutiveTripleFamily C D E by simp [constitutiveTripleFamily])
    have hDJ := constitutiveJointRepair_fixed s
      (show D ∈ constitutiveTripleFamily C D E by simp [constitutiveTripleFamily])
    have hEJ := constitutiveJointRepair_fixed s
      (show E ∈ constitutiveTripleFamily C D E by simp [constitutiveTripleFamily])
    have hmonoC := C.monotone' hsJ
    have hmonoD := D.monotone' hmonoC
    have hmonoE := E.monotone' hmonoD
    simpa [hCJ, hDJ, hEJ] using hmonoE

theorem pairwiseCommutingThree_noScheduleDefect {α : Type u}
    (C D E : ConstitutiveFormation α)
    (hCD : ∀ s, C.act (D.act s) = D.act (C.act s))
    (hCE : ∀ s, C.act (E.act s) = E.act (C.act s))
    (hDE : ∀ s, D.act (E.act s) = E.act (D.act s)) (s : Set α) :
    runConstitutiveFormations [C, D, E] s =
        constitutiveJointRepair (constitutiveTripleFamily C D E) s ∧
    runConstitutiveFormations [C, E, D] s =
        constitutiveJointRepair (constitutiveTripleFamily C D E) s ∧
    runConstitutiveFormations [D, C, E] s =
        constitutiveJointRepair (constitutiveTripleFamily C D E) s ∧
    runConstitutiveFormations [D, E, C] s =
        constitutiveJointRepair (constitutiveTripleFamily C D E) s ∧
    runConstitutiveFormations [E, C, D] s =
        constitutiveJointRepair (constitutiveTripleFamily C D E) s ∧
    runConstitutiveFormations [E, D, C] s =
        constitutiveJointRepair (constitutiveTripleFamily C D E) s := by
  have hCDE := pairwiseCommutingThree_jointRepair C D E hCD hCE hDE s
  have hCED := pairwiseCommutingThree_jointRepair C E D hCE hCD
    (fun x => (hDE x).symm) s
  have hDCE := pairwiseCommutingThree_jointRepair D C E (fun x => (hCD x).symm)
    hDE hCE s
  have hDEC := pairwiseCommutingThree_jointRepair D E C hDE
    (fun x => (hCD x).symm) (fun x => (hCE x).symm) s
  have hECD := pairwiseCommutingThree_jointRepair E C D (fun x => (hCE x).symm)
    (fun x => (hDE x).symm) hCD s
  have hEDC := pairwiseCommutingThree_jointRepair E D C (fun x => (hDE x).symm)
    (fun x => (hCE x).symm) (fun x => (hCD x).symm) s
  have hCEDFamily : constitutiveTripleFamily C E D = constitutiveTripleFamily C D E := by
    ext A
    simp [constitutiveTripleFamily]
    tauto
  have hDCEFamily : constitutiveTripleFamily D C E = constitutiveTripleFamily C D E := by
    ext A
    simp [constitutiveTripleFamily]
    tauto
  have hDECFamily : constitutiveTripleFamily D E C = constitutiveTripleFamily C D E := by
    ext A
    simp [constitutiveTripleFamily]
    tauto
  have hECDFamily : constitutiveTripleFamily E C D = constitutiveTripleFamily C D E := by
    ext A
    simp [constitutiveTripleFamily]
    tauto
  have hEDCFamily : constitutiveTripleFamily E D C = constitutiveTripleFamily C D E := by
    ext A
    simp [constitutiveTripleFamily]
    tauto
  rw [hCEDFamily] at hCED
  rw [hDCEFamily] at hDCE
  rw [hDECFamily] at hDEC
  rw [hECDFamily] at hECD
  rw [hEDCFamily] at hEDC
  simp only [runConstitutiveFormations]
  exact ⟨hCDE.symm, hCED.symm, hDCE.symm, hDEC.symm, hECD.symm, hEDC.symm⟩

theorem constitutiveFormationExchangeMechanism_closed {α : Type u} :
    (∀ (F : Set (ConstitutiveFormation α)) (s : Set α),
      s ⊆ constitutiveJointRepair F s) ∧
    (∀ (F : Set (ConstitutiveFormation α)) (s : Set α)
      (C : ConstitutiveFormation α), C ∈ F →
      C.act (constitutiveJointRepair F s) = constitutiveJointRepair F s) ∧
    (∀ (F : Set (ConstitutiveFormation α)) (s t : Set α),
      s ⊆ t → (∀ C ∈ F, C.act t = t) → constitutiveJointRepair F s ⊆ t) ∧
    (∀ (C D : ConstitutiveFormation α),
      (∀ s, C.act (D.act s) = D.act (C.act s)) ↔
        ∀ s,
          runConstitutiveFormations [C, D] s =
            constitutiveJointRepair (constitutivePairFamily C D) s ∧
          runConstitutiveFormations [D, C] s =
            constitutiveJointRepair (constitutivePairFamily C D) s) ∧
    (∀ (C D E : ConstitutiveFormation α),
      (∀ s, C.act (D.act s) = D.act (C.act s)) →
      (∀ s, C.act (E.act s) = E.act (C.act s)) →
      (∀ s, D.act (E.act s) = E.act (D.act s)) →
      ∀ s,
        runConstitutiveFormations [C, D, E] s =
          constitutiveJointRepair (constitutiveTripleFamily C D E) s ∧
        runConstitutiveFormations [C, E, D] s =
          constitutiveJointRepair (constitutiveTripleFamily C D E) s ∧
        runConstitutiveFormations [D, C, E] s =
          constitutiveJointRepair (constitutiveTripleFamily C D E) s ∧
        runConstitutiveFormations [D, E, C] s =
          constitutiveJointRepair (constitutiveTripleFamily C D E) s ∧
        runConstitutiveFormations [E, C, D] s =
          constitutiveJointRepair (constitutiveTripleFamily C D E) s ∧
        runConstitutiveFormations [E, D, C] s =
          constitutiveJointRepair (constitutiveTripleFamily C D E) s) := by
  exact ⟨constitutiveJointRepair_contains,
    (fun F s _ hC ↦ constitutiveJointRepair_fixed s hC),
    (fun F _ _ hst ht ↦ constitutiveJointRepair_least hst ht),
    formations_commute_iff_twoOrders_are_jointRepair,
    pairwiseCommutingThree_noScheduleDefect⟩

end GaloisForLFunctions.HTGeometry
