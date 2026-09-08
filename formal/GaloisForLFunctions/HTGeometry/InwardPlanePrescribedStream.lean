import GaloisForLFunctions.HTGeometry.InwardPlaneDisplacementReturn

/-!
# Bounded displacement along prescribed streams

A fixed number of fresh inward helpers after each prescribed packet
restores a fixed radius. The construction preserves the prescribed relative
order, distinctness, every prefix bound and a linear total cardinality.
-/

noncomputable section
open Finset
namespace HTGeometry

/-- A prescribed distinct stream can be interleaved with a fixed number of fresh inward
helpers per insertion. Its relative order, bounded displacement and linear total length are retained. -/
theorem exists_planeDisplacement_prescribed_stream {ι : Type*} [DecidableEq ι]
    (v : ι → ℝ × ℝ) (U : Finset ι) (t : List ι) (K : ℕ) (z0 : ℝ × ℝ) (B c : ℝ)
    (hB : 0<B) (hc : 0<c) (hK : 2*B ≤ (K:ℝ)*c/4)
    (hz : planeDisplacementRadius z0 ≤ 4*B^2/c+2*B+c)
    (htnd : t.Nodup) (htv : ∀ p ∈ t,‖v p‖ ≤ B)
    (hUt : ∀ p ∈ U,p ∉ t) (hv : ∀ p ∈ U,‖v p‖ ≤ B)
    (hdir : ∀ L ⊆ U,L.card<K*t.length → ∀ z : ℝ × ℝ,
      ∃ p ∈ U,p ∉ L ∧ z.1*(v p).1+z.2*(v p).2 ≤ -c*‖z‖) :
    ∃ l : List ι,l.Nodup ∧ t.Sublist l ∧ l.length=(K+1)*t.length ∧
      l.toFinset ⊆ t.toFinset ∪ U ∧
      (∀ k : ℕ,planeDisplacementRadius (z0+((l.take k).map v).sum) ≤ 4*B^2/c+4*B+c) ∧
      planeDisplacementRadius (z0+(l.map v).sum) ≤ 4*B^2/c+2*B+c := by
  induction t generalizing U z0 with
  | nil =>
    refine ⟨[],by simp,by simp,by simp,by simp,?_,?_⟩
    · intro k
      simp only [List.take_nil,List.map_nil,List.sum_nil,add_zero]
      linarith
    · simpa using hz
  | cons a t ih =>
    obtain ⟨hat,htnd⟩ := List.nodup_cons.mp htnd
    have hKdir : ∀ L ⊆ U,L.card<K → ∀ z : ℝ × ℝ,
        ∃ p ∈ U,p ∉ L ∧ z.1*(v p).1+z.2*(v p).2 ≤ -c*‖z‖ := by
      intro L hL hLc z
      apply hdir L hL _ z
      simp only [List.length_cons]
      nlinarith
    obtain ⟨l₁,hnd₁,hlen₁,hsub₁,hprefix₁,hend₁⟩ :=
      exists_planeDisplacement_restoring_batch v U K z0 (v a) B c hB hc hK hz
        (htv a (by simp)) hv hKdir
    let U₁ := U \ l₁.toFinset
    let z₁ := z0+v a+(l₁.map v).sum
    have hdir₁ : ∀ L ⊆ U₁,L.card<K*t.length → ∀ z : ℝ × ℝ,
        ∃ p ∈ U₁,p ∉ L ∧ z.1*(v p).1+z.2*(v p).2 ≤ -c*‖z‖ := by
      intro L hL hLc z
      have hLU : L ∪ l₁.toFinset ⊆ U := union_subset (hL.trans sdiff_subset) hsub₁
      have hcard : (L ∪ l₁.toFinset).card<K*(a::t).length := by
        have hh := card_union_le L l₁.toFinset
        rw [List.toFinset_card_of_nodup hnd₁,hlen₁] at hh
        simp only [List.length_cons]
        nlinarith
      obtain ⟨p,hp,hpnot,hpd⟩ := hdir (L ∪ l₁.toFinset) hLU hcard z
      have hpn : p ∉ L ∧ p ∉ l₁.toFinset := by simpa only [mem_union,not_or] using hpnot
      exact ⟨p,mem_sdiff.mpr ⟨hp,hpn.2⟩,hpn.1,hpd⟩
    obtain ⟨l₂,hnd₂,horder₂,hlen₂,hsub₂,hprefix₂,hend₂⟩ :=
      ih (U:=U₁) (z0:=z₁) hend₁ htnd
        (fun p hp => htv p (List.mem_cons_of_mem a hp))
        (fun p hp hn => hUt p (mem_sdiff.mp hp).1 (List.mem_cons_of_mem a hn))
        (fun p hp => hv p (mem_sdiff.mp hp).1) hdir₁
    have hdis : List.Disjoint l₁ l₂ := by
      intro p hp₁ hp₂
      have hh := hsub₂ (List.mem_toFinset.mpr hp₂)
      rcases mem_union.mp hh with ht|hu
      · exact hUt p (hsub₁ (List.mem_toFinset.mpr hp₁))
          (List.mem_cons_of_mem a (List.mem_toFinset.mp ht))
      · exact (mem_sdiff.mp hu).2 (List.mem_toFinset.mpr hp₁)
    have ha₁ : a ∉ l₁ := fun ha => hUt a (hsub₁ (List.mem_toFinset.mpr ha)) (by simp)
    have ha₂ : a ∉ l₂ := by
      intro ha
      rcases mem_union.mp (hsub₂ (List.mem_toFinset.mpr ha)) with ht|hu
      · exact hat (List.mem_toFinset.mp ht)
      · exact hUt a (mem_sdiff.mp hu).1 (by simp)
    refine ⟨a::(l₁++l₂),?_,?_,?_,?_,?_,?_⟩
    · apply List.nodup_cons.mpr
      exact ⟨by simpa only [List.mem_append,not_or] using And.intro ha₁ ha₂,
        List.nodup_append'.mpr ⟨hnd₁,hnd₂,hdis⟩⟩
    · exact (horder₂.trans (List.sublist_append_right l₁ l₂)).cons_cons a
    · simp only [List.length_cons,List.length_append,hlen₁,hlen₂]
      ring
    · intro p hp
      simp only [List.toFinset_cons,List.toFinset_append,mem_insert,mem_union] at hp ⊢
      rcases hp with rfl|hp₁|hp₂
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr (hsub₁ hp₁)
      · rcases mem_union.mp (hsub₂ hp₂) with ht|hu
        · exact Or.inl (Or.inr ht)
        · exact Or.inr (mem_sdiff.mp hu).1
    · intro k
      cases k with
      | zero =>
        simp only [List.take_zero,List.map_nil,List.sum_nil,add_zero]
        linarith
      | succ k =>
        simp only [List.take_succ_cons,List.map_cons,List.sum_cons]
        by_cases hk : k ≤ l₁.length
        · rw [List.take_append_of_le_length hk]
          have hh := hprefix₁ k (by rwa [hlen₁] at hk)
          convert hh using 1; congr 1; abel
        · rw [List.take_append,List.take_of_length_le (le_of_not_ge hk)]
          simp only [List.map_append,List.sum_append]
          have hh := hprefix₂ (k-l₁.length)
          dsimp [z₁] at hh
          convert hh using 1; congr 1; abel
    · simp only [List.map_cons,List.map_append,List.sum_cons,List.sum_append]
      dsimp [z₁] at hend₂
      convert hend₂ using 1; congr 1; abel

end HTGeometry
