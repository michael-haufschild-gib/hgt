import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Clopen
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UrysohnsLemma

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

/-- The inclusion of one subset into a larger one is an inducing map. -/
theorem isInducing_inclusion {X : Type*} [TopologicalSpace X] {s t : Set X} (h : s ⊆ t) :
    IsInducing (Set.inclusion h) :=
  IsInducing.of_comp (continuous_inclusion h) continuous_subtype_val IsInducing.subtypeVal

/-- **Subset monotonicity.**  A smaller subspace has dimension at most that of a larger one:
`s ⊆ t → ind ↥t ≤ n → ind ↥s ≤ n`. -/
theorem SmallIndDimLE.subset {X : Type*} [TopologicalSpace X] {s t : Set X} (h : s ⊆ t) {n : ℕ}
    (hd : SmallIndDimLE (↥t) n) : SmallIndDimLE (↥s) n :=
  SmallIndDimLE.of_isInducing (isInducing_inclusion h) hd

/-- Dimension transfers backwards along a topological embedding. -/
theorem SmallIndDimLE.of_isEmbedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsEmbedding f) {n : ℕ} (h : SmallIndDimLE Y n) : SmallIndDimLE X n :=
  SmallIndDimLE.of_isInducing hf.toIsInducing h

/-- Small inductive dimension is a topological invariant, as an equivalence. -/
theorem smallIndDimLE_congr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {n : ℕ} : SmallIndDimLE X n ↔ SmallIndDimLE Y n :=
  ⟨SmallIndDimLE.of_homeomorph e, SmallIndDimLE.of_homeomorph e.symm⟩

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

/-- **Product with a zero-dimensional space preserves the dimension bound:**
`ind Y ≤ 0 → ind X ≤ m → ind (X × Y) ≤ m`.  This is the `ind Y = 0` case of the addition theorem
`ind (X × Y) ≤ ind X + ind Y`, proved by induction on `m`: a clopen neighbourhood `W` in `Y` makes
the product frontier `frontier V ×ˢ closure W`, whose dimension the inductive hypothesis controls
(via subspace monotonicity into `↥(frontier V) × Y` and the product-subtype homeomorphism). -/
theorem smallIndDimLE_prod_of_zero_right {Y : Type*} [TopologicalSpace Y]
    (hY : SmallIndDimLE Y 0) :
    ∀ {m : ℕ} {X : Type*} [TopologicalSpace X], SmallIndDimLE X m → SmallIndDimLE (X × Y) m := by
  intro m
  induction m with
  | zero => intro X _ hX; exact smallIndDimLE_prod_zero hX hY
  | succ m ih =>
      intro X _ hX
      rintro ⟨x, y⟩ U hU
      rw [nhds_prod_eq, Filter.mem_prod_iff] at hU
      obtain ⟨A, hA, B, hB, hAB⟩ := hU
      obtain ⟨V, hVnhds, hVA, hVdim⟩ := hX x A hA
      obtain ⟨W, hWnhds, hWB, hWfr⟩ := hY y B hB
      refine ⟨V ×ˢ W, ?_, (Set.prod_mono hVA hWB).trans hAB, ?_⟩
      · rw [nhds_prod_eq]; exact Filter.prod_mem_prod hVnhds hWnhds
      · rw [frontier_prod_eq, hWfr, Set.prod_empty, Set.empty_union]
        have hprodY : SmallIndDimLE (↥(frontier V) × Y) m := ih hVdim
        have hind : SmallIndDimLE (↥(frontier V) × ↥(closure W)) m :=
          SmallIndDimLE.of_isInducing (IsInducing.id.prodMap IsInducing.subtypeVal) hprodY
        exact SmallIndDimLE.of_homeomorph
          (Homeomorph.Set.prod (frontier V) (closure W)).symm hind

/-- `L` **separates** `C` from `D`: it is closed, and its complement splits into two disjoint open
sets, one containing `C` and the other `D`.  Separators of small dimension are the mechanism behind
the sum/addition theorems of dimension theory (the hard core of `ind(X×Y) ≤ ind X + ind Y`). -/
def IsSeparator {X : Type*} [TopologicalSpace X] (L C D : Set X) : Prop :=
  IsClosed L ∧ ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ C ⊆ U ∧ D ⊆ V ∧ Lᶜ = U ∪ V

/-- The frontier of an open set `V` separates `V` from the complement of its closure.  This is the
canonical separator produced by the frontier appearing in the definition of small inductive
dimension. -/
theorem isSeparator_frontier {X : Type*} [TopologicalSpace X] {V : Set X} (hV : IsOpen V) :
    IsSeparator (frontier V) V (closure V)ᶜ := by
  refine ⟨isClosed_frontier, V, (closure V)ᶜ, hV, isClosed_closure.isOpen_compl, ?_,
    subset_rfl, subset_rfl, ?_⟩
  · rw [Set.disjoint_compl_right_iff_subset]; exact subset_closure
  · rw [frontier, hV.interior_eq, Set.diff_eq, Set.compl_inter, compl_compl, Set.union_comm]

/-- The frontier of an **arbitrary** set separates its interior from the complement of its closure.
This is the separator produced directly by a neighbourhood `V` in the small-inductive-dimension
definition (whose `V` need not be open). -/
theorem isSeparator_frontier_interior {X : Type*} [TopologicalSpace X] (V : Set X) :
    IsSeparator (frontier V) (interior V) (closure V)ᶜ := by
  refine ⟨isClosed_frontier, interior V, (closure V)ᶜ, isOpen_interior,
    isClosed_closure.isOpen_compl, ?_, subset_rfl, subset_rfl, ?_⟩
  · rw [Set.disjoint_compl_right_iff_subset]; exact interior_subset.trans subset_closure
  · rw [frontier, Set.diff_eq, Set.compl_inter, compl_compl, Set.union_comm]

/-- A separator stays a separator when its two sides shrink. -/
theorem IsSeparator.mono {X : Type*} [TopologicalSpace X] {L C D C' D' : Set X}
    (h : IsSeparator L C D) (hC : C' ⊆ C) (hD : D' ⊆ D) : IsSeparator L C' D' := by
  obtain ⟨hL, U, V, hU, hV, hUV, hCU, hDV, hLc⟩ := h
  exact ⟨hL, U, V, hU, hV, hUV, hC.trans hCU, hD.trans hDV, hLc⟩

/-- Separation is symmetric in its two sides. -/
theorem IsSeparator.symm {X : Type*} [TopologicalSpace X] {L C D : Set X}
    (h : IsSeparator L C D) : IsSeparator L D C := by
  obtain ⟨hL, U, V, hU, hV, hUV, hCU, hDV, hLc⟩ := h
  exact ⟨hL, V, U, hV, hU, hUV.symm, hDV, hCU, by rw [hLc, Set.union_comm]⟩

/-- In a regular space, a point in an open set has a neighbourhood whose closure stays inside it. -/
theorem exists_closure_subset_of_regular {X : Type*} [TopologicalSpace X] [RegularSpace X]
    {x : X} {U : Set X} (hU : IsOpen U) (hx : x ∈ U) : ∃ V ∈ nhds x, closure V ⊆ U := by
  obtain ⟨N, hNmem, hNclosed, hNU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds hx)
  exact ⟨N, hNmem, by rw [hNclosed.closure_eq]; exact hNU⟩

/-- **Forward separator characterization.**  In a regular space, if `ind X ≤ n+1` then any point `x`
and closed set `C` not containing it are separated by a set `L` of small inductive dimension `≤ n`.
This is the reformulation of small inductive dimension that drives the closed sum theorem. -/
theorem exists_separator_of_smallIndDimLE {X : Type*} [TopologicalSpace X] [RegularSpace X] {n : ℕ}
    (h : SmallIndDimLE X (n + 1)) {x : X} {C : Set X} (hC : IsClosed C) (hxC : x ∉ C) :
    ∃ L : Set X, IsSeparator L {x} C ∧ SmallIndDimLE (↥L) n := by
  obtain ⟨U₀, hU₀mem, hU₀closure⟩ := exists_closure_subset_of_regular hC.isOpen_compl hxC
  obtain ⟨V, hVmem, hVU₀, hVdim⟩ := h x U₀ hU₀mem
  refine ⟨frontier V, ?_, hVdim⟩
  refine (isSeparator_frontier_interior V).mono
    (Set.singleton_subset_iff.mpr (mem_interior_iff_mem_nhds.mpr hVmem)) ?_
  have : closure V ⊆ Cᶜ := (closure_mono hVU₀).trans hU₀closure
  rwa [Set.subset_compl_comm] at this

/-- **Reverse separator characterization.**  In a regular space, if every point and disjoint closed
set can be separated by a set of small inductive dimension `≤ n`, then `ind X ≤ n+1`.  Together with
`exists_separator_of_smallIndDimLE` this is the separator characterization of small inductive
dimension. -/
theorem smallIndDimLE_succ_of_separators {X : Type*} [TopologicalSpace X] [RegularSpace X] {n : ℕ}
    (H : ∀ (x : X) (C : Set X), IsClosed C → x ∉ C →
      ∃ L : Set X, IsSeparator L {x} C ∧ SmallIndDimLE (↥L) n) :
    SmallIndDimLE X (n + 1) := by
  intro x U hU
  have hxint : x ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
  obtain ⟨L, ⟨_, U₁, V₁, hU₁open, hV₁open, hdisj, hxU₁, hCV₁, hLc⟩, hLdim⟩ :=
    H x (interior U)ᶜ isOpen_interior.isClosed_compl (by simpa using hxint)
  have hU₁V₁c : U₁ ⊆ V₁ᶜ := hdisj.subset_compl_right
  refine ⟨U₁, hU₁open.mem_nhds (Set.singleton_subset_iff.mp hxU₁), ?_, ?_⟩
  · have hV₁c : V₁ᶜ ⊆ interior U := by
      intro z hz; by_contra hzU; exact hz (hCV₁ hzU)
    exact (hU₁V₁c.trans hV₁c).trans interior_subset
  · have hfrL : frontier U₁ ⊆ L := by
      have hcl : closure U₁ ⊆ V₁ᶜ := closure_minimal hU₁V₁c hV₁open.isClosed_compl
      intro z hz
      rw [frontier, Set.mem_sdiff, hU₁open.interior_eq] at hz
      have hzUV : z ∉ U₁ ∪ V₁ := fun h => h.elim hz.2 (fun hv => hcl hz.1 hv)
      rw [← hLc] at hzUV
      exact not_not.mp hzUV
    exact SmallIndDimLE.subset hfrL hLdim

/-- **Separators are level sets of continuous functions.**  For a continuous real function `f` and a
value `c`, the level set `f⁻¹{c}` separates `{f < c}` from `{f > c}`.  This is the bridge between
Urysohn separating functions and separators that powers the enlargement step of the closed sum
theorem in a normal space. -/
theorem isSeparator_of_continuous {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) (c : ℝ) :
    IsSeparator (f ⁻¹' {c}) (f ⁻¹' Set.Iio c) (f ⁻¹' Set.Ioi c) := by
  refine ⟨isClosed_singleton.preimage hf, f ⁻¹' Set.Iio c, f ⁻¹' Set.Ioi c,
    isOpen_Iio.preimage hf, isOpen_Ioi.preimage hf,
    Disjoint.preimage f
      (Set.disjoint_left.2 (fun x hx hx' => (Set.mem_Iio.mp hx).asymm (Set.mem_Ioi.mp hx'))),
    subset_rfl, subset_rfl, ?_⟩
  ext x
  simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
    Set.mem_Iio, Set.mem_Ioi]
  exact ne_iff_lt_or_gt

/-- **Separators exist between disjoint closed sets** (in a normal space).  Urysohn's lemma supplies
a continuous `f : X → ℝ` that is `0` on `C` and `1` on `D`; the level set `f⁻¹{1/2}` is a separator.
This is the existence input for the enlargement step of the closed sum theorem. -/
theorem exists_isSeparator_of_disjoint_closed {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {C D : Set X} (hC : IsClosed C) (hD : IsClosed D) (hCD : Disjoint C D) :
    ∃ L : Set X, IsSeparator L C D := by
  obtain ⟨f, hfC, hfD, _⟩ := exists_continuous_zero_one_of_isClosed hC hD hCD
  refine ⟨⇑f ⁻¹' {1 / 2}, (isSeparator_of_continuous f.continuous (1 / 2)).mono ?_ ?_⟩
  · intro x hx
    simp only [Set.mem_preimage, Set.mem_Iio]
    have hfx : f x = 0 := hfC hx
    rw [hfx]; norm_num
  · intro x hx
    simp only [Set.mem_preimage, Set.mem_Ioi]
    have hfx : f x = 1 := hfD hx
    rw [hfx]; norm_num

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
