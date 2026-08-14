import GaloisForLFunctions.HTGeometry.DifferentialIndependentTowerIff

/-!
# Splitting a dependent finite family

A finite family that is differentially dependent over a base contains a subfamily which is
independent together with one further member differentially algebraic over the field that subfamily
generates.  This is the shape a coefficient-field descent consumes: the descent is available for a
*single* element over a base of finite transcendence degree, and the tower law reassembles the
conclusion for the whole family.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- Differential independence is inherited by subfamilies. -/
theorem DifferentialIndependent.comp {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential E] {ι ι' : Type*} {x : ι → E} (hx : DifferentialIndependent F x)
    (g : ι' → ι) (hg : Function.Injective g) : DifferentialIndependent F (x ∘ g) := by
  unfold DifferentialIndependent at hx ⊢
  refine hx.comp (fun p : ι' × ℕ => (g p.1, p.2)) ?_
  intro p p' h
  rw [Prod.mk.injEq] at h
  exact Prod.ext (hg h.1) h.2

/-- Differential independence is inherited by subsets. -/
theorem differentialIndependent_subset {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential E] {s t : Set E} (hts : t ⊆ s)
    (hs : DifferentialIndependent F ((↑) : s → E)) :
    DifferentialIndependent F ((↑) : t → E) := by
  have hcomp : ((↑) : t → E) = ((↑) : s → E) ∘ (fun z : t => (⟨z.1, hts z.2⟩ : s)) := rfl
  rw [hcomp]
  refine hs.comp _ ?_
  intro a b hab
  exact Subtype.ext (by simpa using hab)

/-- **Adjoining a transcendental member.**  A subset independent over the base, together with an
element not differentially algebraic over the field it generates, is independent over the base. -/
theorem differentialIndependent_insert {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential E] {t : Set E} {z : E}
    (ht : DifferentialIndependent F ((↑) : ↥t → E))
    (hzt : DifferentialIndependent ↥(differentialAdjoin F t) (fun _ : PUnit.{u + 1} => z)) :
    DifferentialIndependent F ((↑) : ↥(insert z t) → E) := by
  classical
  have hrange : Set.range ((↑) : ↥t → E) = t := Subtype.range_coe
  have hsum : DifferentialIndependent F
      (Sum.elim (fun _ : PUnit.{u + 1} => z) ((↑) : ↥t → E)) := by
    refine differentialIndependent_sumElim_iff.mpr ⟨ht, ?_⟩
    rw [hrange]
    exact hzt
  have hg : ∀ w : ↥(insert z t),
      (Sum.elim (fun _ : PUnit.{u + 1} => z) ((↑) : ↥t → E))
        (if hw : (w : E) ∈ t then Sum.inr ⟨(w : E), hw⟩ else Sum.inl PUnit.unit) = (w : E) := by
    intro w
    by_cases hw : (w : E) ∈ t
    · rw [dif_pos hw]
      rfl
    · rw [dif_neg hw]
      rcases w.2 with h | h
      · exact h.symm
      · exact absurd h hw
  have hcomp : ((↑) : ↥(insert z t) → E)
      = (Sum.elim (fun _ : PUnit.{u + 1} => z) ((↑) : ↥t → E))
        ∘ (fun w : ↥(insert z t) =>
            if hw : (w : E) ∈ t then Sum.inr ⟨(w : E), hw⟩ else Sum.inl PUnit.unit) := by
    funext w
    exact (hg w).symm
  rw [hcomp]
  refine hsum.comp _ ?_
  intro a b hab
  dsimp only at hab
  by_cases ha : (a : E) ∈ t <;> by_cases hb : (b : E) ∈ t
  · rw [dif_pos ha, dif_pos hb] at hab
    have h2 : (⟨(a : E), ha⟩ : ↥t) = ⟨(b : E), hb⟩ := by simpa using hab
    exact Subtype.ext (by simpa using h2)
  · rw [dif_pos ha, dif_neg hb] at hab
    exact absurd hab (by simp)
  · rw [dif_neg ha, dif_pos hb] at hab
    exact absurd hab (by simp)
  · refine Subtype.ext ?_
    have haz : (a : E) = z := by
      rcases a.2 with h | h
      · exact h
      · exact absurd h ha
    have hbz : (b : E) = z := by
      rcases b.2 with h | h
      · exact h
      · exact absurd h hb
    rw [haz, hbz]

/-- **A dependent finite family splits.**  Some subset is independent while one further member is
differentially algebraic over the field that subset generates. -/
theorem exists_split_of_not_differentialIndependent {F E : Type u} [Field F] [Field E]
    [Algebra F E] [Differential E] {s : Set E} (hs : s.Finite)
    (hdep : ¬ DifferentialIndependent F ((↑) : ↥s → E)) :
    ∃ (t : Set E) (z : E), t ⊆ s ∧ z ∈ s ∧ z ∉ t ∧
      DifferentialIndependent F ((↑) : ↥t → E) ∧
      ¬ DifferentialIndependent ↥(differentialAdjoin F t)
        (fun _ : PUnit.{u + 1} => z) := by
  classical
  set C : Set (Set E) :=
    {t | t ⊆ s ∧ DifferentialIndependent F ((↑) : ↥t → E)} with hC
  have hCfin : C.Finite := (hs.finite_subsets).subset (fun t ht => ht.1)
  have hCne : C.Nonempty := by
    refine ⟨∅, Set.empty_subset s, ?_⟩
    have : IsEmpty (↥(∅ : Set E)) := Set.isEmpty_coe_sort.mpr rfl
    unfold DifferentialIndependent
    have hemp : IsEmpty (↥(∅ : Set E) × ℕ) := by
      constructor
      rintro ⟨i, -⟩
      exact IsEmpty.elim ‹IsEmpty (↥(∅ : Set E))› i
    exact algebraicIndependent_empty_type
  obtain ⟨t, htmem, htmax⟩ := Finset.exists_max_image hCfin.toFinset (fun t => t.ncard)
    (by rw [Set.Finite.toFinset_nonempty]; exact hCne)
  rw [Set.Finite.mem_toFinset] at htmem
  obtain ⟨hts, htind⟩ := htmem
  have hne : t ≠ s := by
    intro heq
    exact hdep (heq ▸ htind)
  obtain ⟨z, hzs, hzt⟩ : ∃ z ∈ s, z ∉ t := by
    by_contra hno
    refine hne (Set.Subset.antisymm hts fun w hw => ?_)
    by_contra hwt
    exact hno ⟨w, hw, hwt⟩
  refine ⟨t, z, hts, hzs, hzt, htind, ?_⟩
  intro hzind
  have hins : DifferentialIndependent F ((↑) : ↥(insert z t) → E) :=
    differentialIndependent_insert htind hzind
  have hmem : insert z t ∈ C := ⟨Set.insert_subset hzs hts, hins⟩
  have hlt : t.ncard < (insert z t).ncard := by
    rw [Set.ncard_insert_of_notMem hzt (hs.subset hts)]
    omega
  have hle := htmax (insert z t) (by rw [Set.Finite.mem_toFinset]; exact hmem)
  omega

end

end GaloisForLFunctions.HTGeometry
