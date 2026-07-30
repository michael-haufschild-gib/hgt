import GaloisForLFunctions.HTGeometry.DifferentialFamilyMatroid
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary

/-!
# Pointed collision laws for differential families

A labelled differential family whose injective nonloop subfamilies are free, whose distinguished
label gives differentially algebraic entries, and whose repeated labels differ by a
differentially algebraic element represents an exact pointed partition matroid.  This isolates the
general law used by both elliptic period classes and arithmetic shift-defect families.
-/

open scoped Differential

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

universe u v w

/-! ## Differential collision laws -/

/-- Differential independence of an arbitrary indexed family follows from differential
independence of every finite restriction. This is the family-level finitary interface. -/
theorem differentialIndependent_of_forall_finite_subfamily
    {F E : Type u} {ι : Type v}
    [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (x : ι → E)
    (hfinite : ∀ I : Set ι, I.Finite →
      DifferentialIndependent F (fun i : I ↦ x i)) :
    DifferentialIndependent F x := by
  classical
  let M := differentialFamilyMatroid (F := F) x
  haveI : M.Finitary := by
    dsimp only [M]
    unfold differentialFamilyMatroid
    infer_instance
  have hM : M.Indep Set.univ := by
    apply Matroid.indep_of_forall_finite_subset_indep
    intro I _ hI
    rw [differentialFamilyMatroid_indep_iff]
    exact hfinite I hI
  have hsubtype := (differentialFamilyMatroid_indep_iff
    (F := F) x Set.univ).mp hM
  let e : ι ≃ (Set.univ : Set ι) := (Equiv.Set.univ ι).symm
  have hall := (differentialIndependent_equiv e
    (fun i : (Set.univ : Set ι) ↦ x i)).mpr hsubtype
  simpa [e, Equiv.Set.univ] using! hall

/-- A differentially independent family cannot contain two distinct entries whose difference is
differentially algebraic over the base. -/
theorem DifferentialIndependent.sub_not_differentialAlgebraic
    {F E ι : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x : ι → E} (hx : DifferentialIndependent F x) {i j : ι} (hij : i ≠ j) :
    ¬ DifferentialAlgebraicOver F (x i - x j) := by
  let left : Unit → E := fun _ ↦ x i
  let right : Unit → E := fun _ ↦ x j
  have hinjective : Function.Injective
      (Sum.elim (fun _ : Unit ↦ i) (fun _ : Unit ↦ j)) := by
    intro a b hab
    cases a with
    | inl a =>
        cases b with
        | inl b => simp
        | inr b => exact False.elim (hij hab)
    | inr a =>
        cases b with
        | inl b => exact False.elim (hij hab.symm)
        | inr b => simp
  have hpair : DifferentialIndependent F (Sum.elim left right) := by
    have hcomp := hx.comp
      (Sum.elim (fun _ : Unit ↦ i) (fun _ : Unit ↦ j)) hinjective
    convert hcomp using 1
    funext s
    cases s <;> rfl
  have hleft := (differentialIndependent_sumElim_right_iff left right).mp hpair |>.2
  intro hsub
  let S := differentialAdjoin F (Set.range right)
  letI : DifferentialAlgebra S E :=
    ⟨fun c ↦ derivationClosedDifferential_apply S
      (derivationClosed_differentialAdjoin F (Set.range right)) c⟩
  have hsubS : DifferentialAlgebraicOver S (x i - x j) :=
    differentialAlgebraicOver_mono hsub
  have hxjS : DifferentialAlgebraicOver S (x j) := by
    have hxj : x j ∈ S := by
      exact subset_differentialAdjoin F (Set.range right)
        ⟨(), by simp [right]⟩
    simpa using differentialAlgebraicOver_algebraMap
      (F := S) (E := E) (⟨x j, hxj⟩ : S)
  have hxiS : DifferentialAlgebraicOver S (x i) := by
    simpa only [sub_add_cancel] using differentialAlgebraicOver_add hsubS hxjS
  have hxiHT : HypertranscendentalOver S (x i) := by
    rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
    simpa [left, S] using hleft
  exact hxiHT hxiS

/-- Every entry of a differentially independent family is hypertranscendental over the base. -/
theorem DifferentialIndependent.apply_not_differentialAlgebraic
    {F E ι : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x : ι → E} (hx : DifferentialIndependent F x) (i : ι) :
    ¬ DifferentialAlgebraicOver F (x i) := by
  have hsingle : DifferentialIndependent F (fun _ : Unit ↦ x i) :=
    hx.comp (fun _ : Unit ↦ i) (fun _ _ _ ↦ Subsingleton.elim _ _)
  have hHT : HypertranscendentalOver F (x i) := by
    rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
    exact hsingle
  exact hHT

/-- **Differential collision-matroid law.** If injectively labelled subfamilies are
differentially independent and equal labels force a DA difference, then the represented
differential matroid is exactly the collision matroid of the labels. -/
theorem differentialFamilyMatroid_eq_affineCollisionMatroid_of_parallel
    {F E : Type u} {ι : Type v} {Frame : Type w}
    [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (x : ι → E) (frame : ι → Frame)
    (hindep : ∀ I : Set ι, Set.InjOn frame I →
      DifferentialIndependent F (fun i : I ↦ x i))
    (hparallel : ∀ i j, i ≠ j → frame i = frame j →
      DifferentialAlgebraicOver F (x i - x j)) :
    differentialFamilyMatroid (F := F) x = affineCollisionMatroid frame := by
  rw [differentialFamilyMatroid_eq_affineCollisionMatroid_iff]
  intro I
  constructor
  · intro hI i hi j hj hframe
    by_contra hij
    have hsubtype : (⟨i, hi⟩ : I) ≠ ⟨j, hj⟩ := by
      intro heq
      exact hij (congrArg Subtype.val heq)
    exact (hI.sub_not_differentialAlgebraic hsubtype)
      (hparallel i j hij hframe)
  · exact hindep I

/-! ## Pointed collision matroids -/

/-- The collision matroid of a label map with one distinguished loop label. Each nonloop label
has rank one, while every index carrying `loopFrame` is a loop. -/
def affinePointedCollisionMatroid {Λ Frame : Type*}
    (frame : Λ → Frame) (loopFrame : Frame) : Matroid Λ :=
  (Matroid.uniqueBaseOn {q | q ≠ loopFrame} Set.univ).comap frame

@[simp]
theorem affinePointedCollisionMatroid_ground {Λ Frame : Type*}
    (frame : Λ → Frame) (loopFrame : Frame) :
    (affinePointedCollisionMatroid frame loopFrame).E = Set.univ := by
  simp [affinePointedCollisionMatroid]

/-- Independence in a pointed collision matroid means injective nonloop labels. -/
theorem affinePointedCollisionMatroid_indep_iff {Λ Frame : Type*}
    (frame : Λ → Frame) (loopFrame : Frame) (I : Set Λ) :
    (affinePointedCollisionMatroid frame loopFrame).Indep I ↔
      Set.InjOn frame I ∧ ∀ i ∈ I, frame i ≠ loopFrame := by
  rw [affinePointedCollisionMatroid, Matroid.comap_indep_iff,
    Matroid.uniqueBaseOn_indep_iff (Set.subset_univ _)]
  constructor
  · rintro ⟨himage, hinj⟩
    refine ⟨hinj, ?_⟩
    intro i hi
    exact himage ⟨i, hi, rfl⟩
  · rintro ⟨hinj, hnonloop⟩
    refine ⟨?_, hinj⟩
    rintro q ⟨i, hi, rfl⟩
    exact hnonloop i hi

/-- **Exact pointed-collision closure law.** The closure of an arbitrary observation set consists
precisely of every loop and every index whose nonloop label is already observed. Thus pointed
collision dependence over a subfamily is completely determined by label incidence, with no
finiteness or injectivity assumption. -/
theorem affinePointedCollisionMatroid_mem_closure_iff
    {Λ Frame : Type*} (frame : Λ → Frame) (loopFrame : Frame)
    (I : Set Λ) (i : Λ) :
    i ∈ (affinePointedCollisionMatroid frame loopFrame).closure I ↔
      frame i = loopFrame ∨ frame i ∈ frame '' I := by
  classical
  by_cases hloop : frame i = loopFrame <;>
    simp [affinePointedCollisionMatroid, Matroid.comap_closure_eq,
      Matroid.uniqueBaseOn_closure_eq, hloop]

/-- Loop classifier for pointed collision matroids. -/
theorem affinePointedCollisionMatroid_isLoop_iff
    {Λ Frame : Type*} (frame : Λ → Frame) (loopFrame : Frame) (i : Λ) :
    (affinePointedCollisionMatroid frame loopFrame).IsLoop i ↔
      frame i = loopFrame := by
  change i ∈ (affinePointedCollisionMatroid frame loopFrame).closure ∅ ↔ _
  rw [affinePointedCollisionMatroid_mem_closure_iff]
  simp

/-- Nonloop classifier for pointed collision matroids. -/
theorem affinePointedCollisionMatroid_isNonloop_iff
    {Λ Frame : Type*} (frame : Λ → Frame) (loopFrame : Frame) (i : Λ) :
    (affinePointedCollisionMatroid frame loopFrame).IsNonloop i ↔
      frame i ≠ loopFrame := by
  simp [Matroid.isNonloop_iff, affinePointedCollisionMatroid_ground,
    affinePointedCollisionMatroid_isLoop_iff]

/-- A pair of distinct indices is a circuit exactly when it carries one common nonloop label. -/
theorem affinePointedCollisionMatroid_pair_isCircuit_iff
    {Λ Frame : Type*} (frame : Λ → Frame) (loopFrame : Frame)
    {i j : Λ} (hij : i ≠ j) :
    (affinePointedCollisionMatroid frame loopFrame).IsCircuit {i, j} ↔
      frame i = frame j ∧ frame i ≠ loopFrame := by
  let M := affinePointedCollisionMatroid frame loopFrame
  constructor
  · intro hC
    have hiIndep : M.Indep ({i} : Set Λ) := by
      have h := hC.sdiff_singleton_indep (show j ∈ ({i, j} : Set Λ) by simp)
      simpa [Set.pair_sdiff_right hij] using h
    have hjIndep : M.Indep ({j} : Set Λ) := by
      have h := hC.sdiff_singleton_indep (show i ∈ ({i, j} : Set Λ) by simp)
      simpa [Set.pair_sdiff_left hij] using h
    have hi : M.IsNonloop i := by rwa [← Matroid.indep_singleton]
    have hj : M.IsNonloop j := by rwa [← Matroid.indep_singleton]
    have hclosure : M.closure {i} = M.closure {j} :=
      (hi.closure_eq_closure_iff_isCircuit_of_ne hij).2 hC
    have hjcl : j ∈ M.closure {i} := by
      rw [hclosure]
      exact M.mem_closure_self j
    have hlabel :=
      (affinePointedCollisionMatroid_mem_closure_iff
        frame loopFrame {i} j).1 hjcl
    refine ⟨?_, (affinePointedCollisionMatroid_isNonloop_iff
      frame loopFrame i).1 hi⟩
    rcases hlabel with hloop | himage
    · exact False.elim
        ((affinePointedCollisionMatroid_isNonloop_iff
          frame loopFrame j).1 hj hloop)
    · have hji : frame j = frame i := by simpa using himage
      exact hji.symm
  · rintro ⟨hframe, hloop⟩
    have hi : M.IsNonloop i :=
      (affinePointedCollisionMatroid_isNonloop_iff
        frame loopFrame i).2 hloop
    apply (hi.closure_eq_closure_iff_isCircuit_of_ne hij).1
    ext k
    rw [affinePointedCollisionMatroid_mem_closure_iff,
      affinePointedCollisionMatroid_mem_closure_iff]
    simp [hframe]

/-- **Complete pointed-collision circuit classification.** Every minimal dependence is either a
singleton carrying the distinguished loop label or a pair of distinct indices carrying the same
nonloop label. There are no higher circuits, even for infinite or highly repeated families. -/
theorem affinePointedCollisionMatroid_isCircuit_iff
    {Λ Frame : Type*} (frame : Λ → Frame) (loopFrame : Frame) (C : Set Λ) :
    (affinePointedCollisionMatroid frame loopFrame).IsCircuit C ↔
      (∃ i, C = {i} ∧ frame i = loopFrame) ∨
        ∃ i j, i ≠ j ∧ C = {i, j} ∧
          frame i = frame j ∧ frame i ≠ loopFrame := by
  classical
  let M := affinePointedCollisionMatroid frame loopFrame
  constructor
  · intro hC
    obtain ⟨i, hiC⟩ := hC.nonempty
    by_cases hloopi : frame i = loopFrame
    · left
      have hiLoop : M.IsLoop i :=
        (affinePointedCollisionMatroid_isLoop_iff
          frame loopFrame i).2 hloopi
      exact ⟨i, hiLoop.eq_of_isCircuit_mem hC hiC, hloopi⟩
    · right
      have hall : ∀ j ∈ C, frame j ≠ loopFrame := by
        intro j hjC hloopj
        have hjLoop : M.IsLoop j :=
          (affinePointedCollisionMatroid_isLoop_iff
            frame loopFrame j).2 hloopj
        have hCeq : C = {j} := hjLoop.eq_of_isCircuit_mem hC hjC
        have hij : i = j := by simpa [hCeq] using hiC
        exact hloopi (hij ▸ hloopj)
      have hnotinj : ¬ Set.InjOn frame C := by
        intro hinj
        have hIndep : M.Indep C :=
          (affinePointedCollisionMatroid_indep_iff
            frame loopFrame C).2 ⟨hinj, hall⟩
        exact hC.not_indep hIndep
      simp only [Set.InjOn] at hnotinj
      push Not at hnotinj
      obtain ⟨j, hjC, k, hkC, hframe, hjk⟩ := hnotinj
      have hpair : M.IsCircuit {j, k} :=
        (affinePointedCollisionMatroid_pair_isCircuit_iff
          frame loopFrame hjk).2 ⟨hframe, hall j hjC⟩
      have hpairC : ({j, k} : Set Λ) = C :=
        (Matroid.isCircuit_iff.mp hC).2 hpair.dep
          (Set.pair_subset hjC hkC)
      exact ⟨j, k, hjk, hpairC.symm, hframe, hall j hjC⟩
  · rintro (⟨i, rfl, hloop⟩ |
      ⟨i, j, hij, rfl, hframe, hloop⟩)
    · exact
        ((affinePointedCollisionMatroid_isLoop_iff
          frame loopFrame i).2 hloop).isCircuit
    · exact
        (affinePointedCollisionMatroid_pair_isCircuit_iff
          frame loopFrame hij).2 ⟨hframe, hloop⟩

/-- **Coloop classifier for pointed collision matroids.** An index is essential exactly when it
carries a nonloop label that occurs nowhere else in the family. -/
theorem affinePointedCollisionMatroid_isColoop_iff
    {Λ Frame : Type*} (frame : Λ → Frame) (loopFrame : Frame) (i : Λ) :
    (affinePointedCollisionMatroid frame loopFrame).IsColoop i ↔
      frame i ≠ loopFrame ∧ ∀ j, frame j = frame i → j = i := by
  rw [Matroid.isColoop_iff_notMem_closure_compl]
  simp only [affinePointedCollisionMatroid_ground]
  simp [affinePointedCollisionMatroid, Matroid.comap_closure_eq,
    Matroid.uniqueBaseOn_closure_eq]
  constructor
  · rintro ⟨hunique, hloop⟩
    refine ⟨hloop, fun j hj ↦ ?_⟩
    by_contra hji
    exact hloop (hunique j hji hj)
  · rintro ⟨hloop, hunique⟩
    refine ⟨?_, hloop⟩
    intro j hji hj
    exact (hji (hunique j hj)).elim

/-- A pointed collision matroid is unchanged by a relabelling that is injective on exactly the
labels used by the family together with its distinguished loop label. -/
theorem affinePointedCollisionMatroid_comp_eq_of_injOn
    {Λ Frame Frame' : Type*}
    (frame : Λ → Frame) (loopFrame : Frame)
    (g : Frame → Frame')
    (hg : Set.InjOn g (Set.range frame ∪ {loopFrame})) :
    affinePointedCollisionMatroid (g ∘ frame) (g loopFrame) =
      affinePointedCollisionMatroid frame loopFrame := by
  apply Matroid.ext_indep
  · simp
  · intro I _
    rw [affinePointedCollisionMatroid_indep_iff,
      affinePointedCollisionMatroid_indep_iff]
    constructor
    · rintro ⟨hcomp, hnonloop⟩
      refine ⟨?_, ?_⟩
      · intro i hi j hj hij
        exact hcomp hi hj (congrArg g hij)
      · intro i hi hloop
        exact hnonloop i hi (congrArg g hloop)
    · rintro ⟨hframe, hnonloop⟩
      refine ⟨?_, ?_⟩
      · intro i hi j hj hij
        have hfi : frame i ∈ Set.range frame ∪ {loopFrame} :=
          Or.inl ⟨i, rfl⟩
        have hfj : frame j ∈ Set.range frame ∪ {loopFrame} :=
          Or.inl ⟨j, rfl⟩
        exact hframe hi hj (hg hfi hfj hij)
      · intro i hi hloop
        have hfi : frame i ∈ Set.range frame ∪ {loopFrame} :=
          Or.inl ⟨i, rfl⟩
        have hloopFrame : loopFrame ∈ Set.range frame ∪ {loopFrame} :=
          Or.inr (Set.mem_singleton loopFrame)
        exact hnonloop i hi (hg hfi hloopFrame hloop)

/-- In particular, every globally injective change of label coordinates preserves the pointed
collision matroid. -/
theorem affinePointedCollisionMatroid_comp_eq_of_injective
    {Λ Frame Frame' : Type*}
    (frame : Λ → Frame) (loopFrame : Frame)
    (g : Frame → Frame') (hg : Function.Injective g) :
    affinePointedCollisionMatroid (g ∘ frame) (g loopFrame) =
      affinePointedCollisionMatroid frame loopFrame :=
  affinePointedCollisionMatroid_comp_eq_of_injOn
    frame loopFrame g hg.injOn

/-- The extended rank of a pointed collision packet is the number of distinct nonloop labels. -/
theorem affinePointedCollisionMatroid_eRk {Λ Frame : Type*}
    (frame : Λ → Frame) (loopFrame : Frame) (I : Set Λ) :
    (affinePointedCollisionMatroid frame loopFrame).eRk I =
      ((frame '' I) ∩ {q | q ≠ loopFrame}).encard := by
  rw [affinePointedCollisionMatroid, Matroid.eRk_comap]
  exact (Matroid.uniqueBaseOn_inter_isBasis
    (I := {q | q ≠ loopFrame}) (E := Set.univ)
    (X := frame '' I) (Set.subset_univ _)).eRk_eq_encard

/-- On a finite packet, pointed collision rank is the number of distinct labels after deleting
the distinguished loop label. -/
theorem affinePointedCollisionMatroid_eRk_finset
    {Λ Frame : Type*} [DecidableEq Frame]
    (frame : Λ → Frame) (loopFrame : Frame) (E : Finset Λ) :
    (affinePointedCollisionMatroid frame loopFrame).eRk (↑E : Set Λ) =
      ((E.image frame).erase loopFrame).card := by
  rw [affinePointedCollisionMatroid_eRk]
  calc
    ((frame '' (↑E : Set Λ)) ∩ {q | q ≠ loopFrame}).encard =
        (↑((E.image frame).erase loopFrame) : Set Frame).encard := by
      congr 1
      ext x
      simp
    _ = ((E.image frame).erase loopFrame).card :=
      Set.encard_coe_eq_coe_finsetCard _

/-- **Pointed differential collision-matroid law.** If injective nonloop subfamilies are
differentially independent, the loop label gives DA entries, and repeated labels give DA
differences, then the represented differential matroid is the pointed collision matroid. -/
theorem differentialFamilyMatroid_eq_affinePointedCollisionMatroid_of_parallel
    {F E : Type u} {ι : Type v} {Frame : Type w}
    [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (x : ι → E) (frame : ι → Frame) (loopFrame : Frame)
    (hindep : ∀ I : Set ι, Set.InjOn frame I →
      (∀ i ∈ I, frame i ≠ loopFrame) →
      DifferentialIndependent F (fun i : I ↦ x i))
    (hloop : ∀ i, frame i = loopFrame →
      DifferentialAlgebraicOver F (x i))
    (hparallel : ∀ i j, i ≠ j → frame i = frame j →
      DifferentialAlgebraicOver F (x i - x j)) :
    differentialFamilyMatroid (F := F) x =
      affinePointedCollisionMatroid frame loopFrame := by
  apply Matroid.ext_indep
  · simp [differentialFamilyMatroid]
  · intro I _
    rw [differentialFamilyMatroid_indep_iff,
      affinePointedCollisionMatroid_indep_iff]
    constructor
    · intro hI
      constructor
      · intro i hi j hj hframe
        by_contra hij
        have hsubtype : (⟨i, hi⟩ : I) ≠ ⟨j, hj⟩ := by
          intro heq
          exact hij (congrArg Subtype.val heq)
        exact (hI.sub_not_differentialAlgebraic hsubtype)
          (hparallel i j hij hframe)
      · intro i hi hframe
        exact (hI.apply_not_differentialAlgebraic ⟨i, hi⟩)
          (hloop i hframe)
    · rintro ⟨hinj, hnonloop⟩
      exact hindep I hinj hnonloop

end

end GaloisForLFunctions
