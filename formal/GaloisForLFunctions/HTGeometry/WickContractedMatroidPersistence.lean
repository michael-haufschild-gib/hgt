import GaloisForLFunctions.HTGeometry.WickContractedInteractionMatroid
import GaloisForLFunctions.HTGeometry.DifferentialMatroid

/-!
# Directed persistence of Wick-contracted independence

Contracting a larger base can only destroy independence, and over a finitary matroid the loss is
completely captured by finite stages: a set is independent after contracting a nonempty directed
union of bases exactly when it is independent after contracting every member base.  Freedom that
survives all finite refinements therefore survives the face-complete limit, and any collapse over
the limit base is already witnessed at one finite stage.

Directedness is essential: two bases can each leave a signal free while their union explains it.
Finitarity is essential: it provides the finite witness for any dependence over the limit base.
The differential-transcendence matroid is finitary, so the persistence law holds for the
interaction skeleton of every differential field extension.
-/

open Matroid Set

universe u

namespace GaloisForLFunctions.HTGeometry

variable {α ι : Type*} {M : Matroid α}

/-- Base refinement can only destroy independence: independence after contracting a larger base
implies independence after contracting a smaller one. -/
theorem contract_indep_of_contract_indep_of_subset
    {C C' I : Set α} (hCC' : C ⊆ C') (h : (M ／ C').Indep I) :
    (M ／ C).Indep I := by
  have h2 : ((M ／ C) ／ (C' \ C)).Indep I := by
    rw [Matroid.contract_contract, Set.union_diff_cancel hCC']
    exact h
  exact h2.of_contract

/-- **Directed persistence law.**  Over a finitary matroid, independence in the contraction by a
nonempty directed union of bases is exactly stage-wise independence at every member base. -/
theorem contract_iUnion_indep_iff_forall [Nonempty ι] [M.Finitary]
    {C : ι → Set α} (hdir : Directed (· ⊆ ·) C) {I : Set α} :
    (M ／ ⋃ i, C i).Indep I ↔ ∀ i, (M ／ C i).Indep I := by
  constructor
  · intro h i
    exact contract_indep_of_contract_indep_of_subset (Set.subset_iUnion C i) h
  · intro h
    obtain ⟨J, hJ⟩ := M.exists_isBasis' (⋃ i, C i)
    rw [hJ.contract_indep_iff]
    refine ⟨?_, ?_⟩
    · apply Matroid.indep_of_forall_finite_subset_indep
      intro K hK hKfin
      have hKsub : K ⊆ (K ∩ I) ∪ (K ∩ J) := by
        intro x hx
        rcases hK hx with hxI | hxJ
        · exact Or.inl ⟨hx, hxI⟩
        · exact Or.inr ⟨hx, hxJ⟩
      have hKJfin : (K ∩ J).Finite := hKfin.inter_of_left J
      have hKJU : ↑hKJfin.toFinset ⊆ ⋃ i, C i := by
        rw [Set.Finite.coe_toFinset]
        exact Set.inter_subset_right.trans hJ.subset
      obtain ⟨i₀, hi₀⟩ := hdir.exists_mem_subset_of_finset_subset_biUnion hKJU
      rw [Set.Finite.coe_toFinset] at hi₀
      have hKJindep : M.Indep (K ∩ J) := hJ.indep.subset Set.inter_subset_right
      obtain ⟨J₀, hJ₀, hKJJ₀⟩ := hKJindep.subset_isBasis'_of_subset hi₀
      have hIJ₀ : M.Indep (I ∪ J₀) := ((hJ₀.contract_indep_iff).mp (h i₀)).1
      exact hIJ₀.subset
        (hKsub.trans (Set.union_subset_union Set.inter_subset_right hKJJ₀))
    · refine Set.disjoint_left.mpr fun x hxU hxI => ?_
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxU
      have hIground := (h i).subset_ground
      rw [Matroid.contract_ground] at hIground
      exact (hIground hxI).2 hxi

/-- Nonloop persistence: one signal label is free over the face-complete base exactly when it is
free at every stage. -/
theorem contract_iUnion_indep_singleton_iff_forall [Nonempty ι] [M.Finitary]
    {C : ι → Set α} (hdir : Directed (· ⊆ ·) C) {e : α} :
    (M ／ ⋃ i, C i).Indep {e} ↔ ∀ i, (M ／ C i).Indep {e} :=
  contract_iUnion_indep_iff_forall hdir

/-- **Face-complete persistence for Wick interaction matroids.**  On any signal window,
independence in the face-complete Wick contraction is stage-wise independence throughout a
nonempty directed base family. -/
theorem wickContractedInteractionMatroid_iUnion_indep_iff_forall [Nonempty ι] [M.Finitary]
    {C : ι → Set α} (hdir : Directed (· ⊆ ·) C) (signal : Set α) {I : Set α} :
    (wickContractedInteractionMatroid M (⋃ i, C i) signal).Indep I ↔
      ∀ i, (wickContractedInteractionMatroid M (C i) signal).Indep I := by
  unfold wickContractedInteractionMatroid
  simp only [Matroid.restrict_indep_iff]
  rw [contract_iUnion_indep_iff_forall hdir]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact ⟨h1 i, h2⟩
  · intro h
    exact ⟨fun i => (h i).1, (h (Classical.arbitrary ι)).2⟩

/-- Directed persistence for the differential-transcendence matroid: the interaction skeleton of
a characteristic-zero differential field extension satisfies the face-complete limit law. -/
theorem differentialMatroid_contract_iUnion_indep_iff_forall
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {ι : Type*} [Nonempty ι] {C : ι → Set E} (hdir : Directed (· ⊆ ·) C) {I : Set E} :
    (differentialMatroid F E ／ ⋃ i, C i).Indep I ↔
      ∀ i, (differentialMatroid F E ／ C i).Indep I :=
  contract_iUnion_indep_iff_forall hdir

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

/-- Disjoint-union splitting of differential independence: a disjoint union is differentially
independent over `k` exactly when one part is and the other part is differentially independent
over the differential field the first part generates. -/
theorem diffIndepOn_union_iff
    {k K : Type*} [Field k] [Field K] [Algebra k K] [Differential K]
    {s t : Set K} (hst : Disjoint s t) :
    DiffIndepOn k (s ∪ t) ↔
      DiffIndepOn k t ∧ DiffIndepOn (differentialAdjoin k t) s := by
  classical
  have hfamily :
      (Subtype.val : ↑(s ∪ t) → K) =
        (Sum.elim (Subtype.val : s → K) (Subtype.val : t → K)) ∘
          Equiv.Set.union hst := by
    funext z
    by_cases hz : (z : K) ∈ s
    · rw [Function.comp_apply, Equiv.Set.union_apply_left hst hz]
      rfl
    · have hzt : (z : K) ∈ t := z.2.resolve_left hz
      rw [Function.comp_apply, Equiv.Set.union_apply_right hst hzt]
      rfl
  unfold DiffIndepOn
  rw [hfamily, differentialIndependent_equiv (Equiv.Set.union hst),
    differentialIndependent_sumElim_right_iff, Subtype.range_val]

/-- **Relative reading of Wick contraction.**  Contracting a base in the
differential-transcendence matroid and testing a disjoint signal set is exactly testing
differential independence over the differential field generated by any basis of the base. -/
theorem differentialMatroid_contract_indep_iff_of_isBasis'
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {G J I : Set E} (hJ : (differentialMatroid F E).IsBasis' J G) :
    (differentialMatroid F E ／ G).Indep I ↔
      Disjoint G I ∧ DiffIndepOn (differentialAdjoin F J) I := by
  rw [hJ.contract_indep_iff]
  constructor
  · rintro ⟨hIJ, hGI⟩
    have hdisj : Disjoint I J := (hGI.mono_left hJ.subset).symm
    have hIJ' : DiffIndepOn F (I ∪ J) := hIJ
    exact ⟨hGI, ((diffIndepOn_union_iff hdisj).mp hIJ').2⟩
  · rintro ⟨hGI, hrel⟩
    have hdisj : Disjoint I J := (hGI.mono_left hJ.subset).symm
    have hJindep : DiffIndepOn F J := hJ.indep
    exact ⟨(diffIndepOn_union_iff hdisj).mpr ⟨hJindep, hrel⟩, hGI⟩

/-- **Semantic persistence.**  Relative differential freedom over the face-complete basis field
is exactly stage-wise relative freedom throughout a nonempty directed base family. -/
theorem diffIndepOn_differentialAdjoin_iUnion_iff_forall
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {ι : Type*} [Nonempty ι] {G : ι → Set E} (hdir : Directed (· ⊆ ·) G)
    {J : Set E} (hJ : (differentialMatroid F E).IsBasis' J (⋃ i, G i))
    {Js : ι → Set E} (hJs : ∀ i, (differentialMatroid F E).IsBasis' (Js i) (G i))
    {I : Set E} (hGI : Disjoint (⋃ i, G i) I) :
    DiffIndepOn (differentialAdjoin F J) I ↔
      ∀ i, DiffIndepOn (differentialAdjoin F (Js i)) I := by
  have hlimit := differentialMatroid_contract_indep_iff_of_isBasis' (I := I) hJ
  have hpers :=
    differentialMatroid_contract_iUnion_indep_iff_forall
      (F := F) (E := E) hdir (I := I)
  constructor
  · intro h i
    have hcontract : (differentialMatroid F E ／ ⋃ i, G i).Indep I :=
      hlimit.mpr ⟨hGI, h⟩
    exact ((differentialMatroid_contract_indep_iff_of_isBasis' (hJs i)).mp
      (hpers.mp hcontract i)).2
  · intro h
    have hstage : ∀ i, (differentialMatroid F E ／ G i).Indep I := fun i =>
      (differentialMatroid_contract_indep_iff_of_isBasis' (hJs i)).mpr
        ⟨hGI.mono_left (Set.subset_iUnion G i), h i⟩
    exact (hlimit.mp (hpers.mpr hstage)).2

end GaloisForLFunctions.HTGeometry
