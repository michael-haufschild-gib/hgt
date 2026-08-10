import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Milman's partial converse to the Krein–Milman theorem

If `A` is compact and the closed convex hull `K` of `A` is compact, then every extreme point of `K`
already lies in `A`.

The proof is Rudin's: given a convex neighbourhood `V` of the origin, cover `A` by finitely many
translates `a + V`, replace each piece by the closed convex hull of `A ∩ (a + closure V)`, and
observe that the convex hull of finitely many nonempty compact convex sets is compact — hence
closed, hence contains `K`.  An extreme point of `K` lying in such a hull must lie in one of the
pieces, so it lies in `A + closure V`; letting `V` shrink puts it in `A`.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Pointwise

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The convex join of two compact sets is compact: it is the image of `[0,1] × s × t` under the
segment map. -/
theorem isCompact_convexJoin {s t : Set E} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (convexJoin ℝ s t) := by
  have hEq : convexJoin ℝ s t
      = (fun p : ℝ × E × E => (1 - p.1) • p.2.1 + p.1 • p.2.2) '' (Icc 0 1 ×ˢ s ×ˢ t) := by
    ext z
    constructor
    · rw [mem_convexJoin]
      rintro ⟨a, ha, b, hb, hz⟩
      rw [segment_eq_image] at hz
      obtain ⟨θ, hθ, rfl⟩ := hz
      exact ⟨(θ, a, b), ⟨hθ, ha, hb⟩, rfl⟩
    · rintro ⟨⟨θ, a, b⟩, ⟨hθ, ha, hb⟩, rfl⟩
      rw [mem_convexJoin]
      refine ⟨a, ha, b, hb, ?_⟩
      rw [segment_eq_image]
      exact ⟨θ, hθ, rfl⟩
  rw [hEq]
  exact (isCompact_Icc.prod (hs.prod ht)).image (by fun_prop)

/-- The convex hull of a finite family of nonempty compact convex sets is compact. -/
theorem isCompact_convexHull_biUnion {ι : Type*} [DecidableEq ι] (t : Finset ι) (K : ι → Set E)
    (hne : ∀ i ∈ t, (K i).Nonempty) (hc : ∀ i ∈ t, IsCompact (K i))
    (hconv : ∀ i ∈ t, Convex ℝ (K i)) :
    IsCompact (convexHull ℝ (⋃ i ∈ t, K i)) := by
  induction t using Finset.induction with
  | empty => simp
  | insert b t hb ih =>
      have hbmem : b ∈ insert b t := Finset.mem_insert_self b t
      have hsub : ∀ i ∈ t, i ∈ insert b t := fun i hi => Finset.mem_insert_of_mem hi
      have hKb : IsCompact (K b) := hc b hbmem
      have hKbconv : Convex ℝ (K b) := hconv b hbmem
      have hKbne : (K b).Nonempty := hne b hbmem
      have hUnion : (⋃ i ∈ insert b t, K i) = K b ∪ ⋃ i ∈ t, K i := by
        simp
      rcases t.eq_empty_or_nonempty with rfl | htne
      · rw [hUnion]
        have hEmpty : K b ∪ ⋃ i ∈ (∅ : Finset ι), K i = K b := by simp
        rw [hEmpty, hKbconv.convexHull_eq]
        exact hKb
      · have hrest := ih (fun i hi => hne i (hsub i hi)) (fun i hi => hc i (hsub i hi))
          (fun i hi => hconv i (hsub i hi))
        obtain ⟨j, hj⟩ := htne
        have hUne : (⋃ i ∈ t, K i).Nonempty := by
          obtain ⟨z, hz⟩ := hne j (hsub j hj)
          exact ⟨z, Set.mem_biUnion hj hz⟩
        rw [hUnion, convexHull_union hKbne hUne, hKbconv.convexHull_eq]
        exact isCompact_convexJoin hKb hrest

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- An extreme point of `S` lying in the convex hull of finitely many convex subsets of `S` lies in
one of them. -/
theorem exists_mem_of_extremePoint_mem_convexHull_biUnion {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (Kfam : ι → Set E) {S : Set E} (hSconv : Convex ℝ S)
    (hsub : ∀ i ∈ t, Kfam i ⊆ S) (hconv : ∀ i ∈ t, Convex ℝ (Kfam i))
    {x : E} (hx : x ∈ S.extremePoints ℝ) (hmem : x ∈ convexHull ℝ (⋃ i ∈ t, Kfam i)) :
    ∃ i ∈ t, x ∈ Kfam i := by
  induction t using Finset.induction with
  | empty => simp at hmem
  | insert b t hb ih =>
      have hbmem : b ∈ insert b t := Finset.mem_insert_self b t
      have hsub' : ∀ i ∈ t, i ∈ insert b t := fun i hi => Finset.mem_insert_of_mem hi
      have hUnion : (⋃ i ∈ insert b t, Kfam i) = Kfam b ∪ ⋃ i ∈ t, Kfam i := by simp
      rw [hUnion] at hmem
      rcases (Kfam b).eq_empty_or_nonempty with hbe | hbne
      · rw [hbe, Set.empty_union] at hmem
        obtain ⟨i, hi, hxi⟩ := ih (fun i hi => hsub i (hsub' i hi))
          (fun i hi => hconv i (hsub' i hi)) hmem
        exact ⟨i, Finset.mem_insert_of_mem hi, hxi⟩
      rcases (⋃ i ∈ t, Kfam i).eq_empty_or_nonempty with hUe | hUne
      · rw [hUe, Set.union_empty, (hconv b hbmem).convexHull_eq] at hmem
        exact ⟨b, hbmem, hmem⟩
      rw [convexHull_union hbne hUne, (hconv b hbmem).convexHull_eq, mem_convexJoin] at hmem
      obtain ⟨y, hy, z, hz, hseg⟩ := hmem
      have hyS : y ∈ S := hsub b hbmem hy
      have hzS : z ∈ S := by
        refine convexHull_min ?_ hSconv hz
        intro w hw
        obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.mp hw
        exact hsub i (hsub' i hi) hwi
      rw [← insert_endpoints_openSegment] at hseg
      rcases hseg with rfl | hseg
      · exact ⟨b, hbmem, hy⟩
      rcases hseg with rfl | hseg
      · obtain ⟨i, hi, hxi⟩ := ih (fun i hi => hsub i (hsub' i hi))
          (fun i hi => hconv i (hsub' i hi)) hz
        exact ⟨i, Finset.mem_insert_of_mem hi, hxi⟩
      · have : y = x := hx.2 hyS hzS hseg
        exact ⟨b, hbmem, this ▸ hy⟩

omit [Module ℝ E] [ContinuousSMul ℝ E] in
/-- In a topological additive group the closure of a set is contained in any of its neighbourhood
thickenings. -/
theorem closure_subset_add_nhds {T W : Set E} (hW : W ∈ nhds (0 : E)) :
    closure T ⊆ T + W := by
  intro y hy
  have hcont : Continuous fun z : E => y - z := continuous_const.sub continuous_id
  have hU : (fun z : E => y - z) ⁻¹' W ∈ nhds y :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨s, hsU, hsT⟩ := mem_closure_iff_nhds.mp hy _ hU
  exact Set.mem_add.mpr ⟨s, hsT, y - s, hsU, by abel⟩

/-! ## Milman's theorem -/

variable [T2Space E] [LocallyConvexSpace ℝ E]

/-- **Milman's partial converse to the Krein–Milman theorem.**  Every extreme point of the closed
convex hull of a compact set already belongs to that set. -/
theorem extremePoints_closure_convexHull_subset {A : Set E} (hA : IsCompact A)
    (hK : IsCompact (closure (convexHull ℝ A))) :
    (closure (convexHull ℝ A)).extremePoints ℝ ⊆ A := by
  classical
  intro x hx
  set K : Set E := closure (convexHull ℝ A) with hKdef
  have hKconv : Convex ℝ K := (convex_convexHull ℝ A).closure
  have hAK : A ⊆ K := (subset_convexHull ℝ A).trans subset_closure
  have hxA : x ∈ closure A := by
    rw [mem_closure_iff_nhds]
    intro U hU
    -- a symmetric neighbourhood of the origin inside the translate of `U`
    set N : Set E := (fun z : E => z + x) ⁻¹' U with hN
    have hNmem : N ∈ nhds (0 : E) := by
      have hcont : Continuous fun z : E => z + x := continuous_id.add continuous_const
      exact hcont.continuousAt.preimage_mem_nhds (by simpa using hU)
    set N' : Set E := N ∩ (-N) with hN'
    have hN'mem : N' ∈ nhds (0 : E) := by
      refine Filter.inter_mem hNmem ?_
      have hcont : Continuous fun z : E => -z := continuous_neg
      have : (fun z : E => -z) ⁻¹' N ∈ nhds (0 : E) :=
        hcont.continuousAt.preimage_mem_nhds (by simpa using hNmem)
      simpa [Set.neg_preimage] using this
    obtain ⟨W, hWmem, hWadd⟩ : ∃ W ∈ nhds (0 : E), W + W ⊆ N' := by
      obtain ⟨W₁, hW₁, W₂, hW₂, hsub⟩ :=
        Filter.mem_prod_iff.mp
          (show (fun p : E × E => p.1 + p.2) ⁻¹' N' ∈ (nhds (0 : E)) ×ˢ (nhds (0 : E)) by
            rw [← nhds_prod_eq]
            exact (continuous_fst.add continuous_snd).continuousAt.preimage_mem_nhds (by
              simpa using hN'mem))
      refine ⟨W₁ ∩ W₂, Filter.inter_mem hW₁ hW₂, ?_⟩
      rintro z hz
      obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.mp hz
      exact hsub (Set.mk_mem_prod hu.1 hv.2)
    obtain ⟨V, ⟨hVmem, hVconv⟩, hVW⟩ :=
      (LocallyConvexSpace.convex_basis_zero ℝ E).mem_iff.mp hWmem
    -- finitely many translates of `V` cover `A`
    obtain ⟨t, htA, htcover⟩ :=
      hA.elim_nhds_subcover (fun a => (fun y : E => y - a) ⁻¹' V) (fun a _ => by
        have hcont : Continuous fun y : E => y - a := continuous_id.sub continuous_const
        exact hcont.continuousAt.preimage_mem_nhds (by simpa using hVmem))
    set Kfam : E → Set E := fun a => closure (convexHull ℝ (A ∩ (fun y : E => y - a) ⁻¹' V))
      with hKfam
    have hKfamsub : ∀ a, Kfam a ⊆ K := by
      intro a
      refine closure_mono (convexHull_min ?_ (convex_convexHull ℝ A))
      exact fun y hy => subset_convexHull ℝ A hy.1
    have hKfamconv : ∀ a, Convex ℝ (Kfam a) := fun a => (convex_convexHull ℝ _).closure
    have hKfamcomp : ∀ a, IsCompact (Kfam a) :=
      fun a => hK.of_isClosed_subset isClosed_closure (hKfamsub a)
    have hKfamne : ∀ a ∈ t, (Kfam a).Nonempty := by
      intro a ha
      refine ⟨a, subset_closure (subset_convexHull ℝ _ ⟨htA a ha, ?_⟩)⟩
      simpa using mem_of_mem_nhds hVmem
    have hcover : A ⊆ ⋃ a ∈ t, Kfam a := by
      intro y hy
      obtain ⟨a, ha, hya⟩ := Set.mem_iUnion₂.mp (htcover hy)
      exact Set.mem_biUnion ha (subset_closure (subset_convexHull ℝ _ ⟨hy, hya⟩))
    have hhullcomp : IsCompact (convexHull ℝ (⋃ a ∈ t, Kfam a)) :=
      isCompact_convexHull_biUnion t Kfam hKfamne (fun a _ => hKfamcomp a)
        (fun a _ => hKfamconv a)
    have hKsub : K ⊆ convexHull ℝ (⋃ a ∈ t, Kfam a) := by
      refine closure_minimal (convexHull_min (hcover.trans (subset_convexHull ℝ _))
        (convex_convexHull ℝ _)) hhullcomp.isClosed
    obtain ⟨a, hat, hxa⟩ :=
      exists_mem_of_extremePoint_mem_convexHull_biUnion t Kfam hKconv
        (fun a _ => hKfamsub a) (fun a _ => hKfamconv a) hx (hKsub hx.1)
    -- `x` is within `V + W` of the point `a ∈ A`
    have hVset : (fun y : E => y - a) ⁻¹' V = (fun z : E => -a + z) ⁻¹' V := by
      ext y; simp [sub_eq_neg_add]
    have hxV : x ∈ ((fun y : E => y - a) ⁻¹' V) + W := by
      refine closure_subset_add_nhds hWmem ?_
      rw [hVset]
      refine closure_mono (convexHull_min ?_ (hVconv.translate_preimage_right (-a))) hxa
      intro y hy
      have := hy.2
      rw [hVset] at this
      exact this
    obtain ⟨u, hu, w, hw, huw⟩ := Set.mem_add.mp hxV
    have huV : u - a ∈ V := hu
    have hxa' : x - a ∈ N' :=
      hWadd (Set.mem_add.mpr ⟨u - a, hVW huV, w, hw, by rw [← huw]; abel⟩)
    have hax : a ∈ U := by
      have h2 := hxa'.2
      rw [Set.mem_neg] at h2
      have h1 : a - x ∈ N := by simpa using h2
      have h3 : (a - x) + x ∈ U := h1
      simpa using h3
    exact ⟨a, hax, htA a hat⟩
  rwa [hA.isClosed.closure_eq] at hxA

end GaloisForLFunctions.HTGeometry
