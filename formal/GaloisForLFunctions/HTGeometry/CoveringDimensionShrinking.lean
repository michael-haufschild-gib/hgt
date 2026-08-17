import Mathlib

/-!
# Covering dimension in shrinking form

Foundations of Lebesgue covering dimension, absent from mathlib.  `HasCoverDimLE X n` says every
finite open cover of `X` admits an open shrinking of order at most `n + 1` (no point lies in more
than `n + 1` of the shrunk sets).  This is the topological-dimension notion the frequency-budget and
moment-fiber cards invoke (`singular-autonomous-ade-kolchin-frequency-law`,
`nonautonomous-kolchin-frequency-budget-law`), where the load-bearing input is invariance of covering
dimension under inverse limits of compact spaces with surjective bonding maps.

This file develops the invariants — monotonicity, the small-cover bound, and homeomorphism
invariance — as the base of that development.
-/

open Set

/-- Lebesgue covering dimension `≤ n` (shrinking form): every finite open cover admits an open
shrinking of order at most `n + 1`. -/
def HasCoverDimLE (X : Type*) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ {ι : Type} [Fintype ι] (U : ι → Set X), (∀ i, IsOpen (U i)) → (⋃ i, U i = Set.univ) →
    ∃ V : ι → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧ (⋃ i, V i = Set.univ) ∧
      ∀ x : X, {i : ι | x ∈ V i}.ncard ≤ n + 1

variable {X : Type*} [TopologicalSpace X]

/-- Covering dimension is monotone in `n`. -/
theorem HasCoverDimLE.mono {m n : ℕ} (hmn : m ≤ n) (h : HasCoverDimLE X m) :
    HasCoverDimLE X n := by
  intro ι _ U hU hcov
  obtain ⟨V, hVopen, hVsub, hVcov, hVord⟩ := h U hU hcov
  exact ⟨V, hVopen, hVsub, hVcov, fun x => (hVord x).trans (by omega)⟩

/-- If every finite open cover already uses at most `n + 1` sets, the space has covering
dimension `≤ n`. -/
theorem hasCoverDimLE_of_card_le {n : ℕ}
    (h : ∀ {ι : Type} [Fintype ι] (U : ι → Set X), (∀ i, IsOpen (U i)) → (⋃ i, U i = Set.univ) →
      Fintype.card ι ≤ n + 1) : HasCoverDimLE X n := by
  intro ι _ U hU hcov
  refine ⟨U, hU, fun i => subset_rfl, hcov, fun x => ?_⟩
  calc {i : ι | x ∈ U i}.ncard
      ≤ (Set.univ : Set ι).ncard := Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
    _ = Fintype.card ι := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]
    _ ≤ n + 1 := h U hU hcov

/-- Covering dimension is a homeomorphism invariant. -/
theorem HasCoverDimLE.of_homeomorph {Y : Type*} [TopologicalSpace Y] (e : X ≃ₜ Y) {n : ℕ}
    (h : HasCoverDimLE X n) : HasCoverDimLE Y n := by
  intro ι _ U hU hcov
  obtain ⟨V, hVo, hVs, hVc, hVord⟩ := h (fun i => e ⁻¹' U i)
    (fun i => (hU i).preimage e.continuous)
    (by rw [← Set.preimage_iUnion, hcov, Set.preimage_univ])
  refine ⟨fun i => e.symm ⁻¹' V i, fun i => (hVo i).preimage e.symm.continuous, ?_, ?_, ?_⟩
  · intro i y hy
    have : e.symm y ∈ e ⁻¹' U i := hVs i hy
    simpa using this
  · rw [← Set.preimage_iUnion, hVc, Set.preimage_univ]
  · intro y
    have hset : {i : ι | y ∈ e.symm ⁻¹' V i} = {i : ι | e.symm y ∈ V i} := rfl
    rw [hset]; exact hVord (e.symm y)

/-- **Dimension of a retract.**  A retract `Y` of `X` (continuous `i : Y → X`, `r : X → Y` with
`r ∘ i = id`) has covering dimension at most that of `X`.  This is the monotonicity behind the
Bauer-retract boundary constructions: passing to a retract cannot raise covering dimension. -/
theorem HasCoverDimLE.of_retract {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (i : Y → X) (r : X → Y) (hi : Continuous i) (hr : Continuous r)
    (hri : Function.LeftInverse r i) (h : HasCoverDimLE X n) : HasCoverDimLE Y n := by
  intro κ _ U hU hcov
  obtain ⟨V, hVo, hVs, hVc, hVord⟩ := h (fun k => r ⁻¹' U k) (fun k => (hU k).preimage hr)
    (by rw [← Set.preimage_iUnion, hcov, Set.preimage_univ])
  refine ⟨fun k => i ⁻¹' V k, fun k => (hVo k).preimage hi, ?_, ?_, ?_⟩
  · intro k y hy
    have hmem : i y ∈ r ⁻¹' U k := hVs k hy
    rw [Set.mem_preimage, hri y] at hmem
    exact hmem
  · rw [← Set.preimage_iUnion, hVc, Set.preimage_univ]
  · intro y
    have hset : {k : κ | y ∈ i ⁻¹' V k} = {k : κ | i y ∈ V k} := rfl
    rw [hset]; exact hVord (i y)

/-- **Inverse-limit covering-dimension bound.**  If every finite open cover of `X` refines through
one of the stages `Y i` (via continuous `f i : X → Y i`) — the compactness property that an inverse
limit enjoys — and each stage has covering dimension `≤ n`, then so does `X`.  This is the
load-bearing dimension input of the frequency-budget cards: the covering dimension of an inverse
limit of compact spaces with surjective bonding maps does not exceed the supremum of the stage
dimensions. -/
theorem HasCoverDimLE.of_refinedByStages {ι : Type*} {Y : ι → Type} [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, X → Y i) (hf : ∀ i, Continuous (f i)) {n : ℕ}
    (hdim : ∀ i, HasCoverDimLE (Y i) n)
    (hrefine : ∀ {κ : Type} [Fintype κ] (U : κ → Set X), (∀ k, IsOpen (U k)) →
      (⋃ k, U k = Set.univ) →
      ∃ i, ∃ W : κ → Set (Y i), (∀ k, IsOpen (W k)) ∧ (⋃ k, W k = Set.univ) ∧
        ∀ k, (f i) ⁻¹' (W k) ⊆ U k) :
    HasCoverDimLE X n := by
  intro κ _ U hU hcov
  obtain ⟨i, W, hWo, hWc, hWs⟩ := hrefine U hU hcov
  obtain ⟨V, hVo, hVs, hVc, hVord⟩ := hdim i W hWo hWc
  refine ⟨fun k => (f i) ⁻¹' (V k), fun k => (hVo k).preimage (hf i), ?_, ?_, ?_⟩
  · intro k; exact subset_trans (Set.preimage_mono (hVs k)) (hWs k)
  · rw [← Set.preimage_iUnion, hVc, Set.preimage_univ]
  · intro x
    have hset : {k : κ | x ∈ (f i) ⁻¹' V k} = {k : κ | f i x ∈ V k} := rfl
    rw [hset]; exact hVord (f i x)

/-- A space with at most one point has covering dimension `0`: any finite open cover shrinks to a
single covering set (`Set.univ` at one index, `∅` elsewhere), so every point lies in exactly one. -/
theorem HasCoverDimLE.of_subsingleton [Subsingleton X] : HasCoverDimLE X 0 := by
  intro ι _ U hU hcov
  by_cases hne : Nonempty X
  · obtain ⟨a⟩ := hne
    have ha : a ∈ ⋃ i, U i := by rw [hcov]; exact Set.mem_univ a
    obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp ha
    classical
    refine ⟨fun i => if i = i₀ then Set.univ else ∅, ?_, ?_, ?_, ?_⟩
    · intro i; by_cases h : i = i₀ <;> simp [h]
    · intro i x hx
      by_cases h : i = i₀
      · subst h; exact (Subsingleton.elim x a) ▸ hi₀
      · simp only [if_neg h, Set.mem_empty_iff_false] at hx
    · rw [Set.eq_univ_iff_forall]; intro x
      exact Set.mem_iUnion.mpr ⟨i₀, by simp⟩
    · intro x
      have hset : {i : ι | x ∈ (if i = i₀ then (Set.univ : Set X) else ∅)} = {i₀} := by
        ext i; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        by_cases h : i = i₀ <;> simp [h]
      rw [hset, Set.ncard_singleton]
  · exact ⟨U, hU, fun i => subset_rfl, hcov, fun x => absurd ⟨x⟩ hne⟩

/-- A discrete space has covering dimension `0`: choosing for each point one covering index yields a
partition into (cl)open sets in which every point lies in exactly one.  Composed with
`HasCoverDimLE.of_refinedByStages`, this is the base case for the vanishing covering dimension of a
profinite inverse limit of finite discrete stages. -/
theorem HasCoverDimLE.of_discreteTopology [DiscreteTopology X] : HasCoverDimLE X 0 := by
  intro ι _ U hU hcov
  classical
  have hmem : ∀ x, ∃ i, x ∈ U i := fun x =>
    Set.mem_iUnion.mp (by rw [hcov]; exact Set.mem_univ x)
  refine ⟨fun i => {x | (hmem x).choose = i}, fun i => isOpen_discrete _, ?_, ?_, ?_⟩
  · intro i x hx
    simp only [Set.mem_setOf_eq] at hx
    have hspec := (hmem x).choose_spec
    rwa [hx] at hspec
  · rw [Set.eq_univ_iff_forall]; intro x
    exact Set.mem_iUnion.mpr ⟨(hmem x).choose, rfl⟩
  · intro x
    have hset : {i : ι | x ∈ {y | (hmem y).choose = i}} = {(hmem x).choose} := by
      ext i; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, eq_comm]
    rw [hset, Set.ncard_singleton]

/-- **Finite-coproduct sum theorem.**  Covering dimension does not increase under disjoint union:
`dim (X ⊕ Y) ≤ max(dim X, dim Y)`, stated as `HasCoverDimLE X n → HasCoverDimLE Y n →
HasCoverDimLE (X ⊕ Y) n`.  A cover of the sum restricts to covers of each summand; the shrinkings
recombine via the open embeddings `Sum.inl`, `Sum.inr`, and each point sees only its own summand. -/
theorem HasCoverDimLE.sum {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (hX : HasCoverDimLE X n) (hY : HasCoverDimLE Y n) : HasCoverDimLE (X ⊕ Y) n := by
  intro ι _ U hU hcov
  obtain ⟨VX, hVXo, hVXs, hVXc, hVXord⟩ := hX (fun i => Sum.inl ⁻¹' U i)
    (fun i => (hU i).preimage continuous_inl)
    (by rw [← Set.preimage_iUnion, hcov, Set.preimage_univ])
  obtain ⟨VY, hVYo, hVYs, hVYc, hVYord⟩ := hY (fun i => Sum.inr ⁻¹' U i)
    (fun i => (hU i).preimage continuous_inr)
    (by rw [← Set.preimage_iUnion, hcov, Set.preimage_univ])
  refine ⟨fun i => Sum.inl '' VX i ∪ Sum.inr '' VY i, ?_, ?_, ?_, ?_⟩
  · intro i; exact (isOpenMap_inl _ (hVXo i)).union (isOpenMap_inr _ (hVYo i))
  · rintro i _ (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact hVXs i hx
    · exact hVYs i hy
  · rw [Set.eq_univ_iff_forall]; rintro (x | y)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hVXc ▸ Set.mem_univ x : x ∈ ⋃ i, VX i)
      exact Set.mem_iUnion.mpr ⟨i, Or.inl ⟨x, hi, rfl⟩⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hVYc ▸ Set.mem_univ y : y ∈ ⋃ i, VY i)
      exact Set.mem_iUnion.mpr ⟨i, Or.inr ⟨y, hi, rfl⟩⟩
  · rintro (x | y)
    · have hset : {i : ι | (Sum.inl x : X ⊕ Y) ∈ Sum.inl '' VX i ∪ Sum.inr '' VY i}
          = {i : ι | x ∈ VX i} := by
        ext i
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image, Sum.inl.injEq,
          reduceCtorEq, and_false, exists_false, or_false, exists_eq_right]
      rw [hset]; exact hVXord x
    · have hset : {i : ι | (Sum.inr y : X ⊕ Y) ∈ Sum.inl '' VX i ∪ Sum.inr '' VY i}
          = {i : ι | y ∈ VY i} := by
        ext i
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image, Sum.inr.injEq,
          reduceCtorEq, and_false, exists_false, false_or, exists_eq_right]
      rw [hset]; exact hVYord y

/-- **Covering dimension passes to closed subspaces.**  A cover of the subspace extends to a cover
of the ambient space by adding the complement of its (closed) image; a shrinking of the extended
cover restricts to a shrinking of the original one, and restriction cannot raise the order. -/
theorem HasCoverDimLE.of_isClosedEmbedding {Y : Type*} [TopologicalSpace Y] {f : Y → X}
    (hf : Topology.IsClosedEmbedding f) {n : ℕ} (h : HasCoverDimLE X n) : HasCoverDimLE Y n := by
  classical
  intro ι _ U hU hcov
  choose W hWo hWpre using fun i => (hf.isInducing.isOpen_iff).mp (hU i)
  set W' : Option ι → Set X := fun o => o.elim (Set.range f)ᶜ W with hW'
  have hW'o : ∀ o, IsOpen (W' o) := by
    intro o
    cases o with
    | none => exact hf.isClosed_range.isOpen_compl
    | some i => exact hWo i
  have hW'c : ⋃ o, W' o = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ Set.range f
    · obtain ⟨y, rfl⟩ := hx
      have hy : y ∈ ⋃ i, U i := by rw [hcov]; exact Set.mem_univ y
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      refine Set.mem_iUnion.mpr ⟨some i, ?_⟩
      have : y ∈ f ⁻¹' W i := by rw [hWpre i]; exact hi
      exact this
    · exact Set.mem_iUnion.mpr ⟨none, hx⟩
  obtain ⟨V, hVo, hVs, hVc, hVord⟩ := h W' hW'o hW'c
  refine ⟨fun i => f ⁻¹' V (some i), fun i => (hVo (some i)).preimage hf.continuous, ?_, ?_, ?_⟩
  · intro i y hy
    have : f y ∈ W i := hVs (some i) hy
    have : y ∈ f ⁻¹' W i := this
    rwa [hWpre i] at this
  · rw [Set.eq_univ_iff_forall]
    intro y
    have hy : f y ∈ ⋃ o, V o := by rw [hVc]; exact Set.mem_univ _
    obtain ⟨o, ho⟩ := Set.mem_iUnion.mp hy
    cases o with
    | none => exact absurd (Set.mem_range_self y) (hVs none ho)
    | some i => exact Set.mem_iUnion.mpr ⟨i, ho⟩
  · intro y
    have himg : (fun i => some i) '' {i : ι | f y ∈ V (some i)} ⊆ {o : Option ι | f y ∈ V o} := by
      rintro _ ⟨i, hi, rfl⟩
      exact hi
    calc {i : ι | y ∈ f ⁻¹' V (some i)}.ncard
        = ((fun i => some i) '' {i : ι | f y ∈ V (some i)}).ncard :=
          (Set.ncard_image_of_injective _ (Option.some_injective ι)).symm
      _ ≤ {o : Option ι | f y ∈ V o}.ncard := Set.ncard_le_ncard himg (Set.toFinite _)
      _ ≤ n + 1 := hVord (f y)
