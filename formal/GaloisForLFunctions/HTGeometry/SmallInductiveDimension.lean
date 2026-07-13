import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Clopen
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Small inductive dimension

Mathlib has no topological dimension theory.  The finite Bohr-rank conclusion of the finite-phase
theorem (eq. 9) needs it: the joint hull embeds in `ℂ^N`, hence has finite topological dimension,
hence (Pontryagin) finite character rank.  This file begins the theory by defining the **small
inductive dimension** `ind` and proving its foundational laws.

`SmallIndDimLE X n` reads `ind X ≤ n` for `n : ℕ` (the empty space has `ind = -1`, so it satisfies
`SmallIndDimLE _ n` for every `n`).  The definition is Menger–Urysohn's recursion: `ind X ≤ n+1`
iff every point has arbitrarily small neighbourhoods whose topological frontier has `ind ≤ n`.

Established here: the empty space is `≤ n` for all `n`; the bound is monotone in `n`.  The remaining
targets (`ind ℝ^N ≤ N`, subspace monotonicity, and the Pontryagin `dim = character-rank` bridge) are
the load-bearing pieces still under construction.
-/

open Topology

namespace GaloisForLFunctions

/-- `SmallIndDimLE X n` : the small inductive dimension of `X` is at most `n`.  Menger–Urysohn
recursion: at level `0`, every neighbourhood contains a neighbourhood with empty frontier (a clopen
neighbourhood basis); at level `n+1`, one with frontier of small inductive dimension `≤ n`. -/
def SmallIndDimLE (X : Type*) [TopologicalSpace X] : ℕ → Prop
  | 0 => ∀ (x : X) (U : Set X), U ∈ nhds x → ∃ V ∈ nhds x, V ⊆ U ∧ frontier V = ∅
  | (n + 1) => ∀ (x : X) (U : Set X), U ∈ nhds x →
      ∃ V ∈ nhds x, V ⊆ U ∧ SmallIndDimLE (frontier V) n

/-- The empty space has small inductive dimension `-1 ≤ n` for every `n`: the defining condition is
vacuous over an empty point set. -/
theorem smallIndDimLE_of_isEmpty (X : Type*) [TopologicalSpace X] [IsEmpty X] (n : ℕ) :
    SmallIndDimLE X n := by
  cases n <;> exact fun x => isEmptyElim x

/-- The dimension bound is monotone: `ind X ≤ n` implies `ind X ≤ n+1`. -/
theorem SmallIndDimLE.succ {X : Type*} [TopologicalSpace X] {n : ℕ} :
    SmallIndDimLE X n → SmallIndDimLE X (n + 1) := by
  induction n generalizing X with
  | zero =>
      intro h x U hU
      obtain ⟨V, hVnhds, hVU, hVfront⟩ := h x U hU
      refine ⟨V, hVnhds, hVU, ?_⟩
      have : IsEmpty (frontier V) := by rw [hVfront]; exact Set.isEmpty_coe_sort.mpr rfl
      exact smallIndDimLE_of_isEmpty _ 0
  | succ n ih =>
      intro h x U hU
      obtain ⟨V, hVnhds, hVU, hVfront⟩ := h x U hU
      exact ⟨V, hVnhds, hVU, ih hVfront⟩

/-- Consequently the bound is monotone along `≤`. -/
theorem SmallIndDimLE.mono {X : Type*} [TopologicalSpace X] {m n : ℕ}
    (h : SmallIndDimLE X m) (hmn : m ≤ n) : SmallIndDimLE X n := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact ih.succ

/-- A discrete space is zero-dimensional: singletons are a clopen neighbourhood basis, so every
neighbourhood contains one with empty frontier.  This is the base case of the inductive climb to
`ind ℝ^N ≤ N` (frontiers of boxes drop one dimension, bottoming out at discrete point sets). -/
theorem smallIndDimLE_zero_of_discrete (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    SmallIndDimLE X 0 := by
  intro x U hU
  refine ⟨{x}, (isOpen_discrete _).mem_nhds (Set.mem_singleton x),
    Set.singleton_subset_iff.mpr (mem_of_mem_nhds hU), ?_⟩
  exact IsClopen.frontier_eq ⟨isClosed_discrete _, isOpen_discrete _⟩

/-- The topological frontier of a preimage under a continuous map is contained in the preimage of
the frontier.  This is the key monotonicity input for the subspace/embedding behaviour of small
inductive dimension. -/
theorem frontier_preimage_subset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) (s : Set Y) :
    frontier (f ⁻¹' s) ⊆ f ⁻¹' (frontier s) := by
  intro x hx
  exact ⟨hf.closure_preimage_subset s hx.1,
    fun hxi => hx.2 (preimage_interior_subset_interior_preimage hf hxi)⟩

/-- **Topological invariance.**  Small inductive dimension is a homeomorphism invariant: a
homeomorphism `e : X ≃ₜ Y` transports the bound `ind X ≤ n` to `ind Y ≤ n`.  This is what lets a
dimension bound pass across the finite jet-sample embedding `hull ≅ image ⊆ ℂ^N`. -/
theorem SmallIndDimLE.of_homeomorph :
    ∀ {n : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
      (_ : X ≃ₜ Y), SmallIndDimLE X n → SmallIndDimLE Y n := by
  intro n
  induction n with
  | zero =>
      intro X Y _ _ e h y V hV
      have hxU : e ⁻¹' V ∈ nhds (e.symm y) :=
        e.continuous.continuousAt.preimage_mem_nhds (by rw [Homeomorph.apply_symm_apply]; exact hV)
      obtain ⟨W', hW'n, hW'sub, hW'fr⟩ := h (e.symm y) (e ⁻¹' V) hxU
      refine ⟨e '' W', ?_, (Set.image_mono hW'sub).trans (Set.image_preimage_subset e V), ?_⟩
      · have hmap : e '' W' ∈ Filter.map e (nhds (e.symm y)) := Filter.image_mem_map hW'n
        rwa [e.map_nhds_eq, Homeomorph.apply_symm_apply] at hmap
      · rw [← e.image_frontier, hW'fr, Set.image_empty]
  | succ n ih =>
      intro X Y _ _ e h y V hV
      have hxU : e ⁻¹' V ∈ nhds (e.symm y) :=
        e.continuous.continuousAt.preimage_mem_nhds (by rw [Homeomorph.apply_symm_apply]; exact hV)
      obtain ⟨W', hW'n, hW'sub, hW'dim⟩ := h (e.symm y) (e ⁻¹' V) hxU
      refine ⟨e '' W', ?_, (Set.image_mono hW'sub).trans (Set.image_preimage_subset e V), ?_⟩
      · have hmap : e '' W' ∈ Filter.map e (nhds (e.symm y)) := Filter.image_mem_map hW'n
        rwa [e.map_nhds_eq, Homeomorph.apply_symm_apply] at hmap
      · rw [show frontier (e '' W') = e '' frontier W' from (e.image_frontier W').symm]
        exact ih (e.image (frontier W')) hW'dim

/-- **Monotonicity under inducing maps (embedding / subspace monotonicity).**  If `f : X → Y` is an
inducing map (the topology on `X` is induced from `Y` — e.g. a subspace inclusion), then a dimension
bound transfers backwards: `ind Y ≤ n` implies `ind X ≤ n`.  The frontier of a preimage sits inside
the preimage of the frontier, and `f` corestricts to an inducing map of those frontiers, closing the
induction with a single inductive call. -/
theorem SmallIndDimLE.of_isInducing :
    ∀ {n : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
      {f : X → Y}, IsInducing f → SmallIndDimLE Y n → SmallIndDimLE X n := by
  intro n
  induction n with
  | zero =>
      intro X Y _ _ f hf h x U hU
      rw [hf.nhds_eq_comap, Filter.mem_comap] at hU
      obtain ⟨U', hU'nhds, hU'sub⟩ := hU
      obtain ⟨V', hV'nhds, hV'sub, hV'fr⟩ := h (f x) U' hU'nhds
      refine ⟨f ⁻¹' V', ?_, (Set.preimage_mono hV'sub).trans hU'sub, ?_⟩
      · rw [hf.nhds_eq_comap]; exact Filter.preimage_mem_comap hV'nhds
      · have hfr := frontier_preimage_subset hf.continuous V'
        rw [hV'fr, Set.preimage_empty] at hfr
        exact Set.subset_empty_iff.mp hfr
  | succ n ih =>
      intro X Y _ _ f hf h x U hU
      rw [hf.nhds_eq_comap, Filter.mem_comap] at hU
      obtain ⟨U', hU'nhds, hU'sub⟩ := hU
      obtain ⟨V', hV'nhds, hV'sub, hV'dim⟩ := h (f x) U' hU'nhds
      refine ⟨f ⁻¹' V', ?_, (Set.preimage_mono hV'sub).trans hU'sub, ?_⟩
      · rw [hf.nhds_eq_comap]; exact Filter.preimage_mem_comap hV'nhds
      · have hsub : frontier (f ⁻¹' V') ⊆ f ⁻¹' (frontier V') :=
          frontier_preimage_subset hf.continuous V'
        have hmaps : ∀ z : ↥(frontier (f ⁻¹' V')), f z.val ∈ frontier V' := fun z => hsub z.2
        exact ih ((hf.comp IsInducing.subtypeVal).codRestrict hmaps) hV'dim

/-- **Subspace monotonicity.**  A subspace has small inductive dimension at most that of the whole
space: `ind ↥A ≤ ind X`. -/
theorem SmallIndDimLE.subtype {X : Type*} [TopologicalSpace X] {n : ℕ} (A : Set X)
    (h : SmallIndDimLE X n) : SmallIndDimLE (↥A) n :=
  SmallIndDimLE.of_isInducing IsInducing.subtypeVal h

/-- **Product of zero-dimensional spaces (base case of the addition theorem).**  If `ind X ≤ 0` and
`ind Y ≤ 0` then `ind (X × Y) ≤ 0`: products of clopen neighbourhoods form a clopen basis of the
product, and the frontier of a product of clopen sets is empty. -/
theorem smallIndDimLE_prod_zero {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : SmallIndDimLE X 0) (hY : SmallIndDimLE Y 0) : SmallIndDimLE (X × Y) 0 := by
  rintro ⟨x, y⟩ U hU
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hU
  obtain ⟨A, hA, B, hB, hAB⟩ := hU
  obtain ⟨V, hVnhds, hVA, hVfr⟩ := hX x A hA
  obtain ⟨W, hWnhds, hWB, hWfr⟩ := hY y B hB
  refine ⟨V ×ˢ W, ?_, (Set.prod_mono hVA hWB).trans hAB, ?_⟩
  · rw [nhds_prod_eq]; exact Filter.prod_mem_prod hVnhds hWnhds
  · rw [frontier_prod_eq, hVfr, hWfr]; simp

/-- **The real line is one-dimensional: `ind ℝ ≤ 1`.**  Every neighbourhood of a point contains an
open interval, whose topological frontier is the two-point set `{a, b}` — a discrete (hence
zero-dimensional) subspace.  This is the first rung of `ind ℝ^N ≤ N`. -/
theorem smallIndDimLE_real_le_one : SmallIndDimLE ℝ 1 := by
  intro x U hU
  obtain ⟨a, b, hxab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hU
  refine ⟨Set.Ioo a b, Ioo_mem_nhds hxab.1 hxab.2, hsub, ?_⟩
  rw [frontier_Ioo (hxab.1.trans hxab.2)]
  exact smallIndDimLE_zero_of_discrete _

end GaloisForLFunctions
