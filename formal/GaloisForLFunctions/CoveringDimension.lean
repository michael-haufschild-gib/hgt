import Mathlib

/-!
# Lebesgue covering dimension

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
