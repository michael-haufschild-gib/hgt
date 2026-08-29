import GaloisForLFunctions.HTGeometry.LinearFamilyDefectSupermodularity
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.QuestionRelationBalance
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Linear Hall transversals

Finite linear Rado selection: if every packet of colors spans at least as many
dimensions as it has colors, one may choose one vector of each color and obtain
a linearly independent family.  The final theorem specializes this to the
images of an arbitrary basis under a Hall linear-map family.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped BigOperators

/-- Span of all vectors whose colors belong to `s`. -/
def coloredLinearSpan
    {ι κ M : Type*} [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (v : ι → κ → M) (s : Finset ι) : Submodule ℂ M :=
  ⨆ i : ↥s, Submodule.span ℂ (Set.range (v i.1))

theorem coloredLinearSpan_mono
    {ι κ M : Type*} [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (v : ι → κ → M) {s t : Finset ι} (hst : s ⊆ t) :
    coloredLinearSpan v s ≤ coloredLinearSpan v t := by
  apply iSup_le
  intro i
  exact le_iSup_of_le (⟨i.1, hst i.2⟩ : ↥t) le_rfl

theorem mem_coloredLinearSpan
    {ι κ M : Type*} [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (v : ι → κ → M) {s : Finset ι} (i : ι) (hi : i ∈ s) (k : κ) :
    v i k ∈ coloredLinearSpan v s := by
  exact (le_iSup (fun j : ↥s => Submodule.span ℂ (Set.range (v j.1))) ⟨i, hi⟩)
    (Submodule.subset_span (Set.mem_range_self k))

theorem coloredLinearSpan_union
    {ι κ M : Type*} [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (v : ι → κ → M) (s t : Finset ι) :
    coloredLinearSpan v (s ∪ t) =
      coloredLinearSpan v s ⊔ coloredLinearSpan v t := by
  apply le_antisymm
  · apply iSup_le
    intro i
    rcases Finset.mem_union.mp i.2 with hi | hi
    · exact le_sup_of_le_left
        (le_iSup (fun j : ↥s => Submodule.span ℂ (Set.range (v j.1))) ⟨i.1, hi⟩)
    · exact le_sup_of_le_right
        (le_iSup (fun j : ↥t => Submodule.span ℂ (Set.range (v j.1))) ⟨i.1, hi⟩)
  · exact sup_le
      (coloredLinearSpan_mono v Finset.subset_union_left)
      (coloredLinearSpan_mono v Finset.subset_union_right)

theorem coloredLinearSpan_map
    {ι κ M N : Type*} [DecidableEq ι]
    [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (f : M →ₗ[ℂ] N) (v : ι → κ → M) (s : Finset ι) :
    coloredLinearSpan (fun i k => f (v i k)) s =
      Submodule.map f (coloredLinearSpan v s) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact ⟨v i.1 k, mem_coloredLinearSpan v i.1 i.2 k, rfl⟩
  · apply Submodule.map_le_iff_le_comap.mpr
    apply iSup_le
    intro i
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact mem_coloredLinearSpan (fun i k => f (v i k)) i.1 i.2 k

/-- Canonical equivalence splitting a finite packet into a subpacket and its complement. -/
def finsetPartitionEquiv
    {ι : Type*} [DecidableEq ι] (s t : Finset ι) (hts : t ⊆ s) :
    (↥t ⊕ ↥(s \ t)) ≃ ↥s where
  toFun
    | Sum.inl i => ⟨i.1, hts i.2⟩
    | Sum.inr i => ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩
  invFun i := if hit : i.1 ∈ t then Sum.inl ⟨i.1, hit⟩
    else Sum.inr ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, hit⟩⟩
  left_inv x := by
    rcases x with i | i
    · simp
    · have hit : i.1 ∉ t := (Finset.mem_sdiff.mp i.2).2
      simp [hit]
  right_inv i := by
    by_cases hit : i.1 ∈ t <;> simp [hit]

/-- The span of selected vectors is contained in the span of all available vectors. -/
theorem span_selected_le_coloredLinearSpan
    {ι κ M : Type*} [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (v : ι → κ → M) (s : Finset ι) (k : ↥s → κ) :
    Submodule.span ℂ (Set.range (fun i : ↥s => v i.1 (k i))) ≤
      coloredLinearSpan v s := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact mem_coloredLinearSpan v i.1 i.2 (k i)

/-- Merge independent selections across a partition when the second block is independent
modulo the span of the first. -/
theorem exists_independentColoredSelection_of_partition
    {ι κ M : Type*} [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (v : ι → κ → M) {s t : Finset ι} (hts : t ⊆ s)
    (x : ↥t → M) (y : ↥(s \ t) → M)
    (hxmem : ∀ i, x i ∈ Set.range (v i.1))
    (hymem : ∀ i, y i ∈ Set.range (v i.1))
    (hx : LinearIndependent ℂ x)
    (hy : LinearIndependent ℂ
      ((Submodule.span ℂ (Set.range x)).mkQ ∘ y)) :
    ∃ z : ↥s → M,
      (∀ i, z i ∈ Set.range (v i.1)) ∧ LinearIndependent ℂ z := by
  let P : Submodule ℂ M := Submodule.span ℂ (Set.range x)
  let xP : ↥t → P := fun i =>
    ⟨x i, Submodule.subset_span (Set.mem_range_self i)⟩
  have hxP : LinearIndependent ℂ xP := by
    apply LinearIndependent.of_comp P.subtype
    simpa [xP, Function.comp_def] using hx
  have hsum : LinearIndependent ℂ (Sum.elim x y) := by
    have := hxP.sumElim_of_quotient y
      (by simpa [P, Function.comp_def] using hy)
    simpa [xP] using this
  let e : (↥t ⊕ ↥(s \ t)) ≃ ↥s := finsetPartitionEquiv s t hts
  let z : ↥s → M := (Sum.elim x y) ∘ e.symm
  refine ⟨z, ?_, hsum.comp e.symm e.symm.injective⟩
  intro i
  have hei : e (e.symm i) = i := e.apply_symm_apply i
  generalize hz : e.symm i = q at hei
  rcases q with j | j
  · have hji : j.1 = i.1 := congrArg Subtype.val hei
    simpa [z, hz, hji] using hxmem j
  · have hji : j.1 = i.1 := congrArg Subtype.val hei
    simpa [z, hz, hji] using hymem j

private theorem exists_independentColoredSelection_of_card_le
    {ι κ : Type*} [DecidableEq ι] :
    ∀ n : ℕ, ∀ {M : Type*}, [AddCommGroup M] → [Module ℂ M] →
      [FiniteDimensional ℂ M] →
      ∀ (v : ι → κ → M) (s : Finset ι), s.card ≤ n →
        (∀ t : Finset ι, t ⊆ s →
          t.card ≤ Module.finrank ℂ (coloredLinearSpan v t)) →
        ∃ x : ↥s → M,
          (∀ i, x i ∈ Set.range (v i.1)) ∧ LinearIndependent ℂ x := by
  intro n
  induction n with
  | zero =>
      intro M _ _ _ v s hs _
      have hsempty : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
      subst s
      let x : ↥(∅ : Finset ι) → M := fun i =>
        (Finset.notMem_empty i.1 i.2).elim
      refine ⟨x, ?_, linearIndependent_empty_type⟩
      intro i
      exact (Finset.notMem_empty i.1 i.2).elim
  | succ n ih =>
      intro M _ _ _ v s hs hHall
      classical
      by_cases hsempty : s = ∅
      · subst s
        let x : ↥(∅ : Finset ι) → M := fun i =>
          (Finset.notMem_empty i.1 i.2).elim
        refine ⟨x, ?_, linearIndependent_empty_type⟩
        intro i
        exact (Finset.notMem_empty i.1 i.2).elim
      have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hsempty
      by_cases hsplit : ∃ t : Finset ι, t.Nonempty ∧ t ⊂ s ∧
          Module.finrank ℂ (coloredLinearSpan v t) = t.card
      · obtain ⟨t, htne, hts, htight⟩ := hsplit
        have ht_le_n : t.card ≤ n := by
          have hlt := Finset.card_lt_card hts
          omega
        have hHall_t : ∀ u : Finset ι, u ⊆ t →
            u.card ≤ Module.finrank ℂ (coloredLinearSpan v u) := by
          intro u hu
          exact hHall u (hu.trans hts.1)
        obtain ⟨x, hxmem, hx⟩ := ih v t ht_le_n hHall_t
        let P : Submodule ℂ M := coloredLinearSpan v t
        have hspanx : Submodule.span ℂ (Set.range x) = P := by
          apply Submodule.eq_of_le_of_finrank_le
          · apply Submodule.span_le.mpr
            rintro _ ⟨i, rfl⟩
            obtain ⟨k, hk⟩ := hxmem i
            rw [← hk]
            exact mem_coloredLinearSpan v i.1 i.2 k
          · have hfinx := finrank_span_eq_card hx
            simpa [P, htight] using hfinx.ge
        let r : Finset ι := s \ t
        let qv : ι → κ → (M ⧸ P) := fun i k => P.mkQ (v i k)
        have hqHall : ∀ u : Finset ι, u ⊆ r →
            u.card ≤ Module.finrank ℂ (coloredLinearSpan qv u) := by
          intro u hu
          have hus : u ⊆ s := hu.trans Finset.sdiff_subset
          have hdisj : Disjoint t u := Finset.disjoint_left.mpr (by
            intro a hat hau
            exact (Finset.mem_sdiff.mp (hu hau)).2 hat)
          have htu : t ∪ u ⊆ s := Finset.union_subset hts.1 hus
          have hUnion := hHall (t ∪ u) htu
          rw [Finset.card_union_of_disjoint hdisj, coloredLinearSpan_union] at hUnion
          let Q : Submodule ℂ M := coloredLinearSpan v u
          change t.card + u.card ≤
            Module.finrank ℂ (P ⊔ Q : Submodule ℂ M) at hUnion
          have hrank :=
            HTGeometry.ConstraintRelativity.finrank_map_add_finrank_inf_ker P.mkQ Q
          rw [Submodule.ker_mkQ] at hrank
          have hsup := Submodule.finrank_sup_add_finrank_inf_eq P Q
          have hinf : Module.finrank ℂ (P ⊓ Q : Submodule ℂ M) =
              Module.finrank ℂ (Q ⊓ P : Submodule ℂ M) := by rw [inf_comm]
          rw [coloredLinearSpan_map]
          change u.card ≤ Module.finrank ℂ (Submodule.map P.mkQ Q)
          have hPt : Module.finrank ℂ P = t.card := by simpa [P] using htight
          omega
        have hr_le_n : r.card ≤ n := by
          have hdiff := Finset.card_sdiff_add_card_eq_card hts.1
          have htpos := Finset.card_pos.mpr htne
          change r.card + t.card = s.card at hdiff
          omega
        obtain ⟨y, hymem, hy⟩ := ih qv r hr_le_n hqHall
        choose ky hky using hymem
        let y0 : ↥r → M := fun i => v i.1 (ky i)
        have hy0mem : ∀ i, y0 i ∈ Set.range (v i.1) := by
          intro i
          exact Set.mem_range_self (ky i)
        have hcomp : P.mkQ ∘ y0 = y := by
          funext i
          simpa [qv, y0] using hky i
        have hy0 : LinearIndependent ℂ
            ((Submodule.span ℂ (Set.range x)).mkQ ∘ y0) := by
          rw [hspanx, hcomp]
          exact hy
        simpa [r] using
          exists_independentColoredSelection_of_partition v hts.1 x y0
            hxmem hy0mem hx hy0
      · obtain ⟨i0, hi0⟩ := hsne
        have hsingle := hHall {i0} (Finset.singleton_subset_iff.mpr hi0)
        have hk0 : ∃ k : κ, v i0 k ≠ 0 := by
          by_contra hk
          push Not at hk
          have hbot : coloredLinearSpan v {i0} = ⊥ := by
            apply le_antisymm
            · apply iSup_le
              intro i
              apply Submodule.span_le.mpr
              rintro _ ⟨k, rfl⟩
              have hii : i.1 = i0 := Finset.mem_singleton.mp i.2
              rw [hii, hk k]
              exact Submodule.zero_mem _
            · exact bot_le
          rw [hbot] at hsingle
          simp at hsingle
        obtain ⟨k0, hk0⟩ := hk0
        let t : Finset ι := {i0}
        let x : ↥t → M := fun i => v i.1 k0
        have hxmem : ∀ i, x i ∈ Set.range (v i.1) := by
          intro i
          exact Set.mem_range_self k0
        have hx : LinearIndependent ℂ x := by
          letI : Unique ↥t :=
            { default := ⟨i0, by simp [t]⟩
              uniq := fun i => Subtype.ext (Finset.mem_singleton.mp i.2) }
          rw [linearIndependent_unique_iff]
          have hii : (default : ↥t).1 = i0 :=
            Finset.mem_singleton.mp (default : ↥t).property
          simpa [x, hii] using hk0
        let P : Submodule ℂ M := Submodule.span ℂ (Set.range x)
        have hP : Module.finrank ℂ P = 1 := by
          have hfin := finrank_span_eq_card hx
          simpa [P, t] using hfin
        let r : Finset ι := s \ t
        let qv : ι → κ → (M ⧸ P) := fun i k => P.mkQ (v i k)
        have hqHall : ∀ u : Finset ι, u ⊆ r →
            u.card ≤ Module.finrank ℂ (coloredLinearSpan qv u) := by
          intro u hu
          by_cases huempty : u = ∅
          · subst u
            simp
          have hune : u.Nonempty := Finset.nonempty_iff_ne_empty.mpr huempty
          have hus : u ⊆ s := hu.trans Finset.sdiff_subset
          have hi0not : i0 ∉ u := by
            intro hiu
            exact (Finset.mem_sdiff.mp (hu hiu)).2 (Finset.mem_singleton_self i0)
          have huprop : u ⊂ s := by
            exact Finset.ssubset_iff_subset_ne.mpr ⟨hus, by
              intro husEq
              exact hi0not (husEq ▸ hi0)⟩
          have hQhall := hHall u hus
          have hQne : Module.finrank ℂ (coloredLinearSpan v u) ≠ u.card := by
            intro heq
            exact hsplit ⟨u, hune, huprop, heq⟩
          let Q : Submodule ℂ M := coloredLinearSpan v u
          have hrank :=
            HTGeometry.ConstraintRelativity.finrank_map_add_finrank_inf_ker P.mkQ Q
          rw [Submodule.ker_mkQ] at hrank
          have hinf : Module.finrank ℂ (Q ⊓ P : Submodule ℂ M) ≤ 1 := by
            exact (Submodule.finrank_mono inf_le_right).trans_eq hP
          rw [coloredLinearSpan_map]
          change u.card ≤ Module.finrank ℂ (Submodule.map P.mkQ Q)
          change u.card ≤ Module.finrank ℂ Q at hQhall
          have hQne' : Module.finrank ℂ Q ≠ u.card := by simpa [Q] using hQne
          omega
        have hr_le_n : r.card ≤ n := by
          have hdiff := Finset.card_sdiff_add_card_eq_card (show t ⊆ s by
            simpa [t] using Finset.singleton_subset_iff.mpr hi0)
          change r.card + t.card = s.card at hdiff
          have htcard : t.card = 1 := by simp [t]
          omega
        obtain ⟨y, hymem, hy⟩ := ih qv r hr_le_n hqHall
        choose ky hky using hymem
        let y0 : ↥r → M := fun i => v i.1 (ky i)
        have hy0mem : ∀ i, y0 i ∈ Set.range (v i.1) := by
          intro i
          exact Set.mem_range_self (ky i)
        have hcomp : P.mkQ ∘ y0 = y := by
          funext i
          simpa [qv, y0] using hky i
        have hy0 : LinearIndependent ℂ (P.mkQ ∘ y0) := by
          rw [hcomp]
          exact hy
        have hts : t ⊆ s := by
          simpa [t] using Finset.singleton_subset_iff.mpr hi0
        simpa [P, r] using
          exists_independentColoredSelection_of_partition v hts x y0
            hxmem hy0mem hx hy0

/-- Finite linear Rado theorem, in colored-vector form. -/
theorem exists_linearIndependent_colored_choice
    {ι κ M : Type*} [DecidableEq ι]
    [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (v : ι → κ → M) (s : Finset ι)
    (hHall : ∀ t : Finset ι, t ⊆ s →
      t.card ≤ Module.finrank ℂ (coloredLinearSpan v t)) :
    ∃ k : ↥s → κ, LinearIndependent ℂ (fun i => v i.1 (k i)) := by
  classical
  obtain ⟨x, hxmem, hx⟩ :=
    exists_independentColoredSelection_of_card_le s.card v s le_rfl hHall
  choose k hk using hxmem
  refine ⟨k, ?_⟩
  have heq : (fun i : ↥s => v i.1 (k i)) = x := by
    funext i
    exact hk i
  rwa [heq]

/-- Hall expansion of a linear-map family supplies an independent image choice in every basis. -/
theorem exists_linearIndependent_image_choice_of_hall
    {d κ M : Type*} [Fintype d] [DecidableEq d]
    [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (A : κ → M →ₗ[ℂ] M) (hHall : LinearFamilyHall A)
    (b : Module.Basis d ℂ M) :
    ∃ k : d → κ, LinearIndependent ℂ (fun i => A (k i) (b i)) := by
  classical
  let v : d → κ → M := fun i k => A k (b i)
  have hcolored : ∀ s : Finset d,
      s.card ≤ Module.finrank ℂ (coloredLinearSpan v s) := by
    intro s
    let U : Submodule ℂ M :=
      Submodule.span ℂ (Set.range (fun i : ↥s => b i.1))
    have hbi : LinearIndependent ℂ (fun i : ↥s => b i.1) :=
      b.linearIndependent.comp Subtype.val Subtype.val_injective
    have hfinU : Module.finrank ℂ U = s.card := by
      simpa [U] using finrank_span_eq_card hbi
    have hshadow := hHall U
    have hshadow_le : linearFamilyShadow A U ≤ coloredLinearSpan v s := by
      apply iSup_le
      intro k
      change Submodule.map (A k) U ≤ coloredLinearSpan v s
      dsimp only [U]
      rw [Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact mem_coloredLinearSpan v i.1 i.2 k
    have hshadowRank : Module.finrank ℂ (linearFamilyShadow A U) ≤
        Module.finrank ℂ (coloredLinearSpan v s) :=
      Submodule.finrank_mono hshadow_le
    omega
  obtain ⟨ku, hku⟩ := exists_linearIndependent_colored_choice v Finset.univ
    (fun t _ => hcolored t)
  let e : d → ↥(Finset.univ : Finset d) := fun i => ⟨i, Finset.mem_univ i⟩
  let k : d → κ := fun i => ku (e i)
  refine ⟨k, ?_⟩
  have he := hku.comp e (by
    intro i j hij
    exact Subtype.ext_iff.mp hij)
  simpa [v, k, e, Function.comp_def] using he

end

end GaloisForLFunctions.HTGeometry
