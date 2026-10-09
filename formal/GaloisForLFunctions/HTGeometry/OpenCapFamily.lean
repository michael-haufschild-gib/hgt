import GaloisForLFunctions.HTGeometry.OpenCapFundamentalGroup

/-!
# Fundamental groups after a family of cap attachments

Simply connected open caps whose pairwise overlaps lie in an open path-connected
body create no fundamental-group classes. Compactness reduces arbitrary families
to finite attachments. The puncture-neighborhood corollary supplies a precise
loop-avoidance theorem without assuming global disjointness of charts.
-/

open Set Topology
open DifferentialGeometry.Topology.VanKampen

namespace GaloisForLFunctions.HTGeometry

/-- Relative form of cap attachment, within the union rather than all of the ambient space. -/
theorem fundamentalGroup_inclusion_union_surjective_of_simplyConnected
    {X : Type*} [TopologicalSpace X]
    (U V : Set X) (hUo : IsOpen U) (hVo : IsOpen V)
    (hUp : IsPathConnected U) (hVs : IsSimplyConnected V)
    (hIp : IsPathConnected (U ∩ V)) (a : U) :
    Function.Surjective (FundamentalGroup.map
      (ContinuousMap.inclusion (show U ⊆ U ∪ V from subset_union_left)) a) := by
  let W := U ∪ V
  let U' : Set W := Subtype.val ⁻¹' U
  let V' : Set W := Subtype.val ⁻¹' V
  have hU'p : IsPathConnected U' := hUp.preimage_coe subset_union_left
  have hV's : IsSimplyConnected V' := by
    apply (IsEmbedding.subtypeVal.isSimplyConnected_image).mp
    change IsSimplyConnected (((↑) : W → X) '' (((↑) : W → X) ⁻¹' V))
    rw [Subtype.image_preimage_val, inter_eq_right.mpr (show V ⊆ W from subset_union_right)]
    exact hVs
  have hI'p : IsPathConnected (U' ∩ V') :=
    hIp.preimage_coe (inter_subset_left.trans subset_union_left)
  letI : PathConnectedSpace U' := isPathConnected_iff_pathConnectedSpace.mp hU'p
  letI : SimplyConnectedSpace V' := hV's
  letI : PathConnectedSpace (↑(U' ∩ V')) := isPathConnected_iff_pathConnectedSpace.mp hI'p
  have hcover : U' ∪ V' = univ := by
    ext x
    simp only [mem_union, mem_preimage, mem_univ, iff_true, U', V']
    exact x.property
  let a' : U' := ⟨⟨a, Or.inl a.property⟩, a.property⟩
  have hs := fundamentalGroup_inclusion_surjective_of_simplyConnected_cap_at
    U' V' (hUo.preimage continuous_subtype_val) (hVo.preimage continuous_subtype_val)
    hcover hI'p.nonempty a'
  let f : C(U', U) := ⟨fun x => ⟨x.1.1, x.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  intro p
  obtain ⟨q, hq⟩ := hs p
  refine ⟨(FundamentalGroup.map f a') q, ?_⟩
  change Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.map q f)
    (ContinuousMap.inclusion subset_union_left) = p
  rw [← Path.Homotopic.Quotient.map_comp]
  exact hq

/-- Finite cap attachments whose overlaps lie in the body preserve its loop surjectivity. -/
theorem fundamentalGroup_inclusion_finite_caps_surjective
    {X : Type*} [TopologicalSpace X] {ι : Type*}
    (U : Set X) (V : ι → Set X) (hUo : IsOpen U) (hUp : IsPathConnected U)
    (hVo : ∀ i, IsOpen (V i)) (hVs : ∀ i, IsSimplyConnected (V i))
    (hIp : ∀ i, IsPathConnected (U ∩ V i))
    (hmeet : ∀ i j, i ≠ j → V i ∩ V j ⊆ U)
    (a : U) (s : Finset ι) :
    IsPathConnected (U ∪ ⋃ i ∈ s, V i) ∧
      Function.Surjective (FundamentalGroup.map
        (ContinuousMap.inclusion (show U ⊆ U ∪ ⋃ i ∈ s, V i from subset_union_left)) a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have heq : U ∪ ⋃ i ∈ (∅ : Finset ι), V i = U := by simp
      generalize_proofs hsub
      revert hsub
      rw [heq]
      intro hsub
      refine ⟨hUp, ?_⟩
      intro p
      refine ⟨p, ?_⟩
      induction p using Quotient.inductionOn with
      | _ γ => rfl
  | @insert j s hjs ih =>
      have heq : U ∪ ⋃ i ∈ insert j s, V i = (U ∪ ⋃ i ∈ s, V i) ∪ V j := by
        ext x
        simp only [mem_union, mem_iUnion, Finset.mem_insert]
        aesop
      generalize_proofs hsub
      revert hsub
      rw [heq]
      intro hsub
      let W := U ∪ ⋃ i ∈ s, V i
      have hWo : IsOpen W := hUo.union (isOpen_iUnion fun i => isOpen_iUnion fun _ => hVo i)
      have hinter : W ∩ V j = U ∩ V j := by
        ext x
        constructor
        · rintro ⟨hx, hxj⟩
          rcases hx with hxU | hxV
          · exact ⟨hxU, hxj⟩
          · obtain ⟨i, hi⟩ := mem_iUnion.mp hxV
            obtain ⟨his, hxi⟩ := mem_iUnion.mp hi
            exact ⟨hmeet i j (fun hij => hjs (hij ▸ his)) ⟨hxi, hxj⟩, hxj⟩
        · rintro ⟨hxU, hxj⟩
          exact ⟨Or.inl hxU, hxj⟩
      have hWI : IsPathConnected (W ∩ V j) := hinter.symm ▸ hIp j
      refine ⟨ih.1.union (hVs j).isPathConnected hWI.nonempty, ?_⟩
      let aW : W := ⟨a, Or.inl a.property⟩
      have hs := fundamentalGroup_inclusion_union_surjective_of_simplyConnected
        W (V j) hWo (hVo j) ih.1 (hVs j) hWI aW
      intro z
      obtain ⟨q, hq⟩ := hs z
      obtain ⟨p, hp⟩ := ih.2 q
      refine ⟨p, ?_⟩
      rw [← hp] at hq
      change Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.map p
          (ContinuousMap.inclusion (show U ⊆ W from subset_union_left)))
        (ContinuousMap.inclusion (show W ⊆ W ∪ V j from subset_union_left)) = z at hq
      rw [← Path.Homotopic.Quotient.map_comp] at hq
      exact hq

/-- An arbitrary family of simply connected open caps overlapping only in the body
creates no loop classes. -/
theorem fundamentalGroup_inclusion_open_caps_surjective
    {X : Type*} [TopologicalSpace X] {ι : Type*}
    (U : Set X) (V : ι → Set X) (hUo : IsOpen U) (hUp : IsPathConnected U)
    (hVo : ∀ i, IsOpen (V i)) (hVs : ∀ i, IsSimplyConnected (V i))
    (hIp : ∀ i, IsPathConnected (U ∩ V i))
    (hmeet : ∀ i j, i ≠ j → V i ∩ V j ⊆ U)
    (hcover : U ∪ ⋃ i, V i = univ) (a : U) :
    Function.Surjective (FundamentalGroup.map (subsetToAmbient U) a) := by
  classical
  let W : Finset ι → Set X := fun s => U ∪ ⋃ i ∈ s, V i
  have hWo : ∀ s, IsOpen (W s) := fun s =>
    hUo.union (isOpen_iUnion fun i => isOpen_iUnion fun _ => hVo i)
  have hWmono : Monotone W := by
    intro s t hst x hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      obtain ⟨his, hxi⟩ := mem_iUnion.mp hi
      exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hst his, hxi⟩⟩)
  have hWdir : Directed (· ⊆ ·) W := fun s t =>
    ⟨s ∪ t, hWmono Finset.subset_union_left, hWmono Finset.subset_union_right⟩
  have hWcover : (⋃ s, W s) = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x ∈ U ∪ ⋃ i, V i := hcover.symm ▸ mem_univ x
    rcases hx with hxU | hxV
    · exact mem_iUnion.mpr ⟨∅, Or.inl hxU⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hxV
      exact mem_iUnion.mpr ⟨{i}, Or.inr
        (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨by simp, hi⟩⟩)⟩
  intro p
  obtain ⟨s, ha, q, hq⟩ := fundamentalGroup_exists_preimage_of_directed_open_cover
    W hWo hWcover hWdir (a : X) p
  have hs := (fundamentalGroup_inclusion_finite_caps_surjective
    U V hUo hUp hVo hVs hIp hmeet a s).2
  obtain ⟨r, hr⟩ := hs q
  refine ⟨r, ?_⟩
  rw [← hr] at hq
  change Path.Homotopic.Quotient.map
    (Path.Homotopic.Quotient.map r
      (ContinuousMap.inclusion (show U ⊆ W s from subset_union_left)))
    (subsetToAmbient (W s)) = p at hq
  rw [← Path.Homotopic.Quotient.map_comp] at hq
  exact hq

/-- Deleting isolated punctures preserves surjectivity on fundamental groups when each
puncture has a simply connected neighborhood with path-connected punctured part. -/
theorem fundamentalGroup_compl_inclusion_surjective_of_puncture_neighborhoods
    {X : Type*} [TopologicalSpace X] (A : Set X) (hAc : IsClosed A)
    (hUp : IsPathConnected Aᶜ)
    (hlocal : ∀ a : A, ∃ V : Set X, IsOpen V ∧ IsSimplyConnected V ∧
      (a : X) ∈ V ∧ V ∩ A = {(a : X)} ∧ IsPathConnected (V \ {(a : X)}))
    (x : ↥(Aᶜ)) :
    Function.Surjective (FundamentalGroup.map (subsetToAmbient Aᶜ) x) := by
  classical
  choose V hVo hVs ha hVA hVp using hlocal
  have hIp : ∀ i, IsPathConnected (Aᶜ ∩ V i) := by
    intro i
    have heq : Aᶜ ∩ V i = V i \ {(i : X)} := by
      ext y
      constructor
      · rintro ⟨hyA, hyV⟩
        refine ⟨hyV, ?_⟩
        intro hyi
        have hyi' : y = (i : X) := mem_singleton_iff.mp hyi
        exact hyA (hyi'.symm ▸ i.property)
      · rintro ⟨hyV, hyi⟩
        refine ⟨?_, hyV⟩
        intro hyA
        exact hyi ((hVA i) ▸ (show y ∈ V i ∩ A from ⟨hyV, hyA⟩))
    rw [heq]
    exact hVp i
  have hmeet : ∀ i j, i ≠ j → V i ∩ V j ⊆ Aᶜ := by
    intro i j hij y hy hyA
    have hi : y = (i : X) := mem_singleton_iff.mp
      ((hVA i) ▸ (show y ∈ V i ∩ A from ⟨hy.1, hyA⟩))
    have hj : y = (j : X) := mem_singleton_iff.mp
      ((hVA j) ▸ (show y ∈ V j ∩ A from ⟨hy.2, hyA⟩))
    exact hij (Subtype.ext (hi.symm.trans hj))
  have hcover : Aᶜ ∪ ⋃ i, V i = univ := by
    apply eq_univ_of_forall
    intro y
    by_cases hy : y ∈ A
    · exact Or.inr (mem_iUnion.mpr ⟨⟨y, hy⟩, ha ⟨y, hy⟩⟩)
    · exact Or.inl hy
  exact fundamentalGroup_inclusion_open_caps_surjective
    Aᶜ V hAc.isOpen_compl hUp hVo hVs hIp hmeet hcover x

end GaloisForLFunctions.HTGeometry
