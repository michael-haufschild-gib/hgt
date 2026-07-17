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

namespace GaloisForLFunctions.HTGeometry

/-- Coefficient-field form of `differentialAdjoin_union` for differential algebraicity. -/
theorem differentialAlgebraicOver_union_iff_nested
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (s t : Set E) (x : E) :
    DifferentialAlgebraicOver (differentialAdjoin F (s ∪ t)) x ↔
      DifferentialAlgebraicOver
        (differentialAdjoin (differentialAdjoin F s) t) x := by
  rw [← differentialAdjoin_union]
  rfl

/-- Coefficient-field form of `differentialAdjoin_union` for differential independence. -/
theorem diffIndepOn_union_iff_nested
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (s t I : Set E) :
    DiffIndepOn (differentialAdjoin F (s ∪ t)) I ↔
      DiffIndepOn (differentialAdjoin (differentialAdjoin F s) t) I := by
  rw [← differentialAdjoin_union]
  rfl

/-- **One-step base insensitivity.**  Adjoining one differentially algebraic element to the
coefficient field preserves differential independence of any set. -/
theorem diffIndepOn_differentialAdjoin_singleton_of_differentialAlgebraicOver
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Differential k] [Differential K] [DifferentialAlgebra k K] [CharZero K]
    {I : Set K} {g : K}
    (hg : DifferentialAlgebraicOver k g) (hI : DiffIndepOn k I) :
    DiffIndepOn (differentialAdjoin k ({g} : Set K)) I := by
  apply diffIndepOn_of_forall_finite
  intro t hts htfin
  revert hts
  refine Set.Finite.induction_on
    (motive := fun t _ =>
      t ⊆ I → DiffIndepOn (differentialAdjoin k ({g} : Set K)) t)
    t htfin (fun _ => diffIndepOn_empty) ?_
  intro a s hnot hsfin ih hsub
  have hsub' : s ⊆ I := (Set.subset_insert a s).trans hsub
  rw [diffIndepOn_insert_iff hnot]
  refine ⟨ih hsub', ?_⟩
  intro hDA
  rw [← differentialAlgebraicOver_union_iff_nested] at hDA
  rw [Set.union_comm] at hDA
  rw [differentialAlgebraicOver_union_iff_nested] at hDA
  letI : Differential ↥(differentialAdjoin k s) :=
    derivationClosedDifferential _ (derivationClosed_differentialAdjoin k s)
  letI : DifferentialAlgebra ↥(differentialAdjoin k s) K :=
    ⟨fun c => derivationClosedDifferential_apply _
      (derivationClosed_differentialAdjoin k s) c⟩
  have hgS : DifferentialAlgebraicOver (differentialAdjoin k s) g :=
    differentialAlgebraicOver_mono hg
  have haS : DifferentialAlgebraicOver (differentialAdjoin k s) a :=
    differentialAlgebraicOver_trans hgS hDA
  have hins : DiffIndepOn k (insert a s) := hI.subset hsub
  rw [diffIndepOn_insert_iff hnot] at hins
  exact hins.2 haS

/-- **Finite base extension.**  Adjoining a finite packet of differentially algebraic elements
to the coefficient field preserves differential independence. -/
theorem diffIndepOn_differentialAdjoin_union_finite_of_differentialAlgebraicOver
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {S I : Set E} {G₀ : Set E} (hfin : G₀.Finite)
    (hDA : ∀ g ∈ G₀, DifferentialAlgebraicOver (differentialAdjoin F S) g)
    (hI : DiffIndepOn (differentialAdjoin F S) I) :
    DiffIndepOn (differentialAdjoin F (S ∪ G₀)) I := by
  revert hDA
  refine Set.Finite.induction_on
    (motive := fun t _ =>
      (∀ g ∈ t, DifferentialAlgebraicOver (differentialAdjoin F S) g) →
        DiffIndepOn (differentialAdjoin F (S ∪ t)) I)
    G₀ hfin (fun _ => by rw [Set.union_empty]; exact hI) ?_
  intro g G₀' hgnot hfin' ih hDA'
  have hIH : DiffIndepOn (differentialAdjoin F (S ∪ G₀')) I :=
    ih fun g' hg' => hDA' g' (Set.mem_insert_of_mem g hg')
  have hSsub : S ⊆ (differentialAdjoin F (S ∪ G₀') : IntermediateField F E) :=
    fun x hx => subset_differentialAdjoin F (S ∪ G₀') (Set.mem_union_left _ hx)
  letI : Differential ↥(differentialAdjoin F (S ∪ G₀')) :=
    derivationClosedDifferential _
      (derivationClosed_differentialAdjoin F (S ∪ G₀'))
  letI : DifferentialAlgebra ↥(differentialAdjoin F (S ∪ G₀')) E :=
    ⟨fun c => derivationClosedDifferential_apply _
      (derivationClosed_differentialAdjoin F (S ∪ G₀')) c⟩
  have hgB : DifferentialAlgebraicOver (differentialAdjoin F (S ∪ G₀')) g :=
    differentialAlgebraicOver_mono_differentialAdjoin_narrow _
      (derivationClosed_differentialAdjoin F (S ∪ G₀')) hSsub
      (hDA' g (Set.mem_insert g G₀'))
  have hstep :=
    diffIndepOn_differentialAdjoin_singleton_of_differentialAlgebraicOver hgB hIH
  rw [← diffIndepOn_union_iff_nested] at hstep
  have hset : (S ∪ G₀') ∪ {g} = S ∪ insert g G₀' := by
    rw [Set.union_insert, Set.insert_eq, Set.union_comm]
  rwa [hset] at hstep

/-- **Basis-free finite-stage intrinsic reading.**  Contracted independence in the
differential-transcendence matroid is disjointness plus relative differential independence over
the face field of every finite base stage; no basis choice occurs in the statement. -/
theorem differentialMatroid_contract_indep_iff_forall_finite_stage
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {G I : Set E} :
    (differentialMatroid F E ／ G).Indep I ↔
      Disjoint G I ∧
        ∀ G₀ : Set E, G₀ ⊆ G → G₀.Finite →
          DiffIndepOn (differentialAdjoin F G₀) I := by
  constructor
  · intro h
    have hdisj : Disjoint G I := by
      refine Set.disjoint_left.mpr fun x hxG hxI => ?_
      have hg := h.subset_ground
      rw [Matroid.contract_ground] at hg
      exact (hg hxI).2 hxG
    refine ⟨hdisj, fun G₀ hsub hfin => ?_⟩
    have hstage : (differentialMatroid F E ／ G₀).Indep I :=
      contract_indep_of_contract_indep_of_subset hsub h
    obtain ⟨J₀, hJ₀⟩ := (differentialMatroid F E).exists_isBasis' G₀
    have hrel : DiffIndepOn (differentialAdjoin F J₀) I :=
      ((differentialMatroid_contract_indep_iff_of_isBasis' hJ₀).mp hstage).2
    have hDAg : ∀ g ∈ G₀,
        DifferentialAlgebraicOver (differentialAdjoin F J₀) g := by
      intro g hgmem
      have hcl : g ∈ (differentialMatroid F E).closure J₀ := by
        rw [hJ₀.closure_eq_closure]
        exact (differentialMatroid F E).subset_closure G₀ (by simp) hgmem
      exact (differentialMatroid_mem_closure_iff_of_indep hJ₀.indep g).mp hcl
    have hup :=
      diffIndepOn_differentialAdjoin_union_finite_of_differentialAlgebraicOver
        hfin hDAg hrel
    rwa [Set.union_eq_self_of_subset_left hJ₀.subset] at hup
  · rintro ⟨hdisj, hstages⟩
    haveI : Nonempty {t : Set E // t ⊆ G ∧ t.Finite} :=
      ⟨⟨∅, Set.empty_subset G, Set.finite_empty⟩⟩
    have hdir : Directed (· ⊆ ·)
        (fun i : {t : Set E // t ⊆ G ∧ t.Finite} => i.1) := fun i j =>
      ⟨⟨i.1 ∪ j.1, Set.union_subset i.2.1 j.2.1, i.2.2.union j.2.2⟩,
        Set.subset_union_left, Set.subset_union_right⟩
    have hunion : (⋃ i : {t : Set E // t ⊆ G ∧ t.Finite}, i.1) = G := by
      apply Set.Subset.antisymm
      · exact Set.iUnion_subset fun i => i.2.1
      · intro x hx
        exact Set.mem_iUnion.mpr
          ⟨⟨{x}, Set.singleton_subset_iff.mpr hx, Set.finite_singleton x⟩, rfl⟩
    rw [← hunion, contract_iUnion_indep_iff_forall hdir]
    intro i
    obtain ⟨J₀, hJ₀⟩ := (differentialMatroid F E).exists_isBasis' i.1
    refine (differentialMatroid_contract_indep_iff_of_isBasis' hJ₀).mpr
      ⟨hdisj.mono_left i.2.1, ?_⟩
    have hstage := hstages i.1 i.2.1 i.2.2
    have hle : differentialAdjoin F J₀ ≤ differentialAdjoin F i.1 :=
      differentialAdjoin_le F
        (hJ₀.subset.trans (subset_differentialAdjoin F i.1))
        (derivationClosed_differentialAdjoin F i.1)
    letI : Algebra ↥(differentialAdjoin F J₀) ↥(differentialAdjoin F i.1) :=
      (IntermediateField.inclusion hle).toAlgebra
    haveI : IsScalarTower
        ↥(differentialAdjoin F J₀) ↥(differentialAdjoin F i.1) E :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact DifferentialIndependent.restrictScalarsTower hstage

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

/-- **Directed-union coefficient lemma.**  Differential independence over the face field of an
arbitrary base holds as soon as it holds over the face field of every finite sub-base: an
annihilating polynomial has finitely many coefficients, each generated by finitely many jets,
so it descends to one finite stage. -/
theorem diffIndepOn_differentialAdjoin_of_forall_finite_subset
    {F E : Type u} [Field F] [Field E] [Algebra F E] [Differential E]
    {G I : Set E}
    (h : ∀ G₀ : Set E, G₀ ⊆ G → G₀.Finite →
      DiffIndepOn (differentialAdjoin F G₀) I) :
    DiffIndepOn (differentialAdjoin F G) I := by
  classical
  unfold DiffIndepOn DifferentialIndependent
  rw [algebraicIndependent_iff]
  intro p hp
  choose T hT1 hT2 using fun m : { m // m ∈ p.support } =>
    IntermediateField.exists_finset_of_mem_adjoin
      (show (↑(p.coeff m.1) : E) ∈
          IntermediateField.adjoin F (differentialJetSet G) from (p.coeff m.1).2)
  set Tall : Finset E := p.support.attach.biUnion T with hTalldef
  have hTallsub : (↑Tall : Set E) ⊆ differentialJetSet G := by
    intro t ht
    obtain ⟨m, _, htm⟩ := Finset.mem_biUnion.mp ht
    exact hT1 m htm
  choose gw hgwmem nw hw using fun t : { t // t ∈ Tall } => hTallsub t.2
  set G₀ : Finset E := Tall.attach.image gw with hG₀def
  have hG₀sub : (↑G₀ : Set E) ⊆ G := by
    intro g hg
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hg
    exact hgwmem t
  have hjetsub : (↑Tall : Set E) ⊆ differentialJetSet (↑G₀ : Set E) := by
    intro t ht
    exact ⟨gw ⟨t, ht⟩,
      Finset.mem_coe.mpr (Finset.mem_image_of_mem gw (Finset.mem_attach _ _)),
      nw ⟨t, ht⟩, hw ⟨t, ht⟩⟩
  have hjetmono : differentialJetSet (↑G₀ : Set E) ⊆ differentialJetSet G := by
    rintro y ⟨z, hz, n', rfl⟩
    exact ⟨z, hG₀sub hz, n', rfl⟩
  have hle : differentialAdjoin F (↑G₀ : Set E) ≤ differentialAdjoin F G :=
    IntermediateField.adjoin_le_iff.mpr
      (hjetmono.trans (IntermediateField.subset_adjoin F _))
  have hmem : ∀ m : { m // m ∈ p.support },
      (↑(p.coeff m.1) : E) ∈ differentialAdjoin F (↑G₀ : Set E) := by
    intro m
    have hTm : (↑(T m) : Set E) ⊆ ↑(differentialAdjoin F (↑G₀ : Set E)) := by
      intro t ht
      have htall : t ∈ Tall := Finset.mem_biUnion.mpr ⟨m, Finset.mem_attach _ _, ht⟩
      exact IntermediateField.subset_adjoin F _ (hjetsub htall)
    exact (IntermediateField.adjoin_le_iff.mpr hTm) (hT2 m)
  letI : Algebra ↥(differentialAdjoin F (↑G₀ : Set E)) ↥(differentialAdjoin F G) :=
    (IntermediateField.inclusion hle).toAlgebra
  haveI : IsScalarTower ↥(differentialAdjoin F (↑G₀ : Set E))
      ↥(differentialAdjoin F G) E :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  set q : MvPolynomial (↑I × ℕ) ↥(differentialAdjoin F (↑G₀ : Set E)) :=
    ∑ m ∈ p.support.attach,
      MvPolynomial.monomial m.1 (⟨(↑(p.coeff m.1) : E), hmem m⟩ :
        ↥(differentialAdjoin F (↑G₀ : Set E))) with hqdef
  have hq : MvPolynomial.map
      (algebraMap ↥(differentialAdjoin F (↑G₀ : Set E))
        ↥(differentialAdjoin F G)) q = p := by
    rw [hqdef, map_sum]
    conv_rhs => rw [MvPolynomial.as_sum p]
    rw [← Finset.sum_attach p.support
      (fun m => MvPolynomial.monomial m (MvPolynomial.coeff m p))]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.map_monomial]
    congr 1
  have haeval : (MvPolynomial.aeval
      (fun r : ↑I × ℕ => differentialJet r.2 (r.1 : E))) q = 0 := by
    have h2 := MvPolynomial.aeval_map_algebraMap (↥(differentialAdjoin F G))
      (fun r : ↑I × ℕ => differentialJet r.2 (r.1 : E)) q
    rw [hq] at h2
    rw [← h2]
    exact hp
  have hstage := h (↑G₀ : Set E) hG₀sub G₀.finite_toSet
  have hq0 : q = 0 :=
    (algebraicIndependent_iff.mp hstage) q haeval
  rw [← hq, hq0, map_zero]

/-- Jet-fibre freedom over the face field of an arbitrary base is exactly stage-wise freedom at
every finite sub-base. -/
theorem diffIndepOn_differentialAdjoin_iff_forall_finite_subset
    {F E : Type u} [Field F] [Field E] [Algebra F E] [Differential E]
    {G I : Set E} :
    DiffIndepOn (differentialAdjoin F G) I ↔
      ∀ G₀ : Set E, G₀ ⊆ G → G₀.Finite →
        DiffIndepOn (differentialAdjoin F G₀) I := by
  constructor
  · intro h G₀ hsub _hfin
    have hjetmono : differentialJetSet G₀ ⊆ differentialJetSet G := by
      rintro y ⟨z, hz, n', rfl⟩
      exact ⟨z, hsub hz, n', rfl⟩
    have hle : differentialAdjoin F G₀ ≤ differentialAdjoin F G :=
      IntermediateField.adjoin_le_iff.mpr
        (hjetmono.trans (IntermediateField.subset_adjoin F _))
    letI : Algebra ↥(differentialAdjoin F G₀) ↥(differentialAdjoin F G) :=
      (IntermediateField.inclusion hle).toAlgebra
    haveI : IsScalarTower ↥(differentialAdjoin F G₀)
        ↥(differentialAdjoin F G) E :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact DifferentialIndependent.restrictScalarsTower h
  · exact diffIndepOn_differentialAdjoin_of_forall_finite_subset

/-- **Limit-field intrinsic reading.**  For every base, of any cardinality, Wick contraction in
the differential-transcendence matroid measures relative differential independence over the
single face field of that base. -/
theorem differentialMatroid_contract_indep_iff_diffIndepOn_differentialAdjoin
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {G I : Set E} :
    (differentialMatroid F E ／ G).Indep I ↔
      Disjoint G I ∧ DiffIndepOn (differentialAdjoin F G) I := by
  rw [differentialMatroid_contract_indep_iff_forall_finite_stage]
  exact and_congr_right fun _ =>
    diffIndepOn_differentialAdjoin_iff_forall_finite_subset.symm

end GaloisForLFunctions.HTGeometry
