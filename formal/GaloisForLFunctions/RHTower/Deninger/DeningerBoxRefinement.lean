import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Compactness.Compact

/-!
# Refining a cover of a profinite-by-compact product by clopen boxes

On a product whose first factor is compact Hausdorff and totally disconnected, every open cover is
refined by a finite family of boxes whose first sides are clopen: the product basis gives an open
box inside a member of the cover, the clopen basis of the profinite factor shrinks its first side
to a clopen set, and compactness of the product extracts a finite subfamily.

Together with the refinement of a finite clopen cover to a finite clopen partition, this is the
combinatorial input to the transverse partition of unity on a packet.

* `deningerClopenBox` : a clopen box inside a member of the cover around each point.
* `deningerBoxRefinement` : the finite clopen-box refinement.
-/

namespace RHTower

open Set TopologicalSpace

section BoxRefinement

variable {B S : Type*} [TopologicalSpace B] [CompactSpace B] [T2Space B]
  [TotallyDisconnectedSpace B] [TopologicalSpace S] [CompactSpace S] {κ : Type*}

omit [CompactSpace S] in
/-- **Around every point there is a clopen box inside a member of the cover.**  The product basis
gives an open box, and the clopen basis of the profinite factor shrinks its first side. -/
theorem deningerClopenBox {U : κ → Set (B × S)} (hU : ∀ j, IsOpen (U j))
    (hcov : ∀ p : B × S, ∃ j, p ∈ U j) (p : B × S) :
    ∃ (C : Set B) (W : Set S) (j : κ),
      IsClopen C ∧ IsOpen W ∧ p.1 ∈ C ∧ p.2 ∈ W ∧ C ×ˢ W ⊆ U j := by
  obtain ⟨j, hj⟩ := hcov p
  obtain ⟨V, W, hV, hW, hpV, hpW, hsub⟩ :=
    (isOpen_prod_iff.mp (hU j)) p.1 p.2 (by simpa using hj)
  obtain ⟨C, hCclopen, hpC, hCV⟩ :=
    isTopologicalBasis_isClopen.exists_subset_of_mem_open hpV hV
  exact ⟨C, W, j, hCclopen, hW, hpC, hpW,
    fun q hq => hsub ⟨hCV hq.1, hq.2⟩⟩

/-- **A cover of a profinite-by-compact product is refined by finitely many clopen boxes.** -/
theorem deningerBoxRefinement {U : κ → Set (B × S)} (hU : ∀ j, IsOpen (U j))
    (hcov : ∀ p : B × S, ∃ j, p ∈ U j) :
    ∃ (T : Finset (B × S)) (C : B × S → Set B) (W : B × S → Set S) (f : B × S → κ),
      (∀ q, IsClopen (C q)) ∧ (∀ q, IsOpen (W q))
        ∧ (∀ q, (C q) ×ˢ (W q) ⊆ U (f q))
        ∧ ∀ p : B × S, ∃ q ∈ T, p ∈ (C q) ×ˢ (W q) := by
  classical
  choose C W f hCclopen hWopen hmemC hmemW hbox using deningerClopenBox hU hcov
  have hopen : ∀ q : B × S, IsOpen ((C q) ×ˢ (W q)) :=
    fun q => (hCclopen q).isOpen.prod (hWopen q)
  have hcover : (univ : Set (B × S)) ⊆ ⋃ q : B × S, (C q) ×ˢ (W q) := by
    intro p _
    exact mem_iUnion.mpr ⟨p, ⟨hmemC p, hmemW p⟩⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover _ hopen hcover
  refine ⟨T, C, W, f, hCclopen, hWopen, hbox, fun p => ?_⟩
  obtain ⟨q, hqT, hq⟩ := Set.mem_iUnion₂.mp (hT (mem_univ p))
  exact ⟨q, hqT, hq⟩

end BoxRefinement

end RHTower
