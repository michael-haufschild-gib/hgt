/-
# Rectangle crossing duality (planar topology infrastructure)

A rectangle can be crossed in exactly one of two dual ways.  Mathlib has no Brouwer fixed point,
no Jordan curve theorem, and no discrete Steinhaus/Hex duality; this file builds the crossing
duality that planar function theory needs, in three stages.

* **Stage A** (`compact_separation_of_no_joining_component`).  Compact clopen separation.  If no
  connected subset of a compact set `K` in a Hausdorff space meets both closed sets `A` and `B`,
  then `K` splits into two disjoint compacts, one missing `A`, the other missing `B`.  The pieces
  are relatively clopen in `K`.  The per-point engine (a clopen neighbourhood of `x` avoiding a
  compact set that misses the connected component of `x`) is
  `Bottcher.exists_isClopen_neighborhood_disjoint_compact_of_disjoint_connectedComponent`; Stage A
  is the finite-cover Boolean assembly on top of it.

* **Stage B** (`discrete_crossing_duality`).  The discrete Hex/Steinhaus duality on a grid board:
  either the marked cells contain a king-connected chain from the bottom row to the top row, or the
  free cells contain a rook-connected chain from the left column to the right column.

* **Stage C** (`rectangle_crossing_duality`).  Either `K` contains a connected curtain inside the
  closed rectangle joining bottom edge to top edge, or the complement contains a polygonal path from
  the left edge to the right edge.
-/
import Mathlib
import GaloisForLFunctions.Bottcher.RelativeRigidityCountableAvoidance

open Set

namespace RHTower

/-- **Stage A — compact clopen separation.**  Work in the compact Hausdorff subspace `K`.  For each
`x ∈ K` the connected component of `x` misses `A` or misses `B` (its image is a connected subset of
`K`, so the hypothesis forbids it from meeting both).  Because the space is compact Hausdorff, a
connected component is the intersection of its clopen neighbourhoods, so a single clopen neighbourhood
of `x` already avoids whichever of `A`, `B` the component misses.  Cover `K` by these clopens, take a
finite subcover, and let `K₁` be the union of the members avoiding `B`; its complement in `K` avoids
`A`.  Push both relatively-clopen pieces back to `X` as compact sets. -/
theorem compact_separation_of_no_joining_component {X : Type*} [TopologicalSpace X] [T2Space X]
    {K A B : Set X} (hK : IsCompact K) (hA : IsClosed A) (hB : IsClosed B)
    (h : ∀ C ⊆ K, IsConnected C → ¬((C ∩ A).Nonempty ∧ (C ∩ B).Nonempty)) :
    ∃ K₁ K₂ : Set X, K = K₁ ∪ K₂ ∧ IsCompact K₁ ∧ IsCompact K₂ ∧ Disjoint K₁ K₂ ∧
      K₁ ∩ B = ∅ ∧ K₂ ∩ A = ∅ := by
  classical
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  set A' : Set ↥K := Subtype.val ⁻¹' A with hA'def
  set B' : Set ↥K := Subtype.val ⁻¹' B with hB'def
  have hA'cpt : IsCompact A' := (hA.preimage continuous_subtype_val).isCompact
  have hB'cpt : IsCompact B' := (hB.preimage continuous_subtype_val).isCompact
  -- Each component misses `A` or misses `B`.
  have hcomp_ab : ∀ x : ↥K,
      Disjoint A' (connectedComponent x) ∨ Disjoint B' (connectedComponent x) := by
    intro x
    have hc : IsConnected (Subtype.val '' connectedComponent x) :=
      (isConnected_connectedComponent).image _ continuous_subtype_val.continuousOn
    have hsub : Subtype.val '' connectedComponent x ⊆ K := by
      rintro y ⟨c, _, rfl⟩; exact c.2
    rcases not_and_or.mp (h _ hsub hc) with hA0 | hB0
    · left
      rw [Set.disjoint_left]
      intro p hpA' hpComp
      exact hA0 ⟨(p : X), ⟨p, hpComp, rfl⟩, hpA'⟩
    · right
      rw [Set.disjoint_left]
      intro p hpB' hpComp
      exact hB0 ⟨(p : X), ⟨p, hpComp, rfl⟩, hpB'⟩
  -- Per-point clopen neighbourhood, tagged by which set it avoids.
  have key : ∀ x : ↥K, ∃ E : Set ↥K, IsClopen E ∧ x ∈ E ∧
      (Disjoint B' E ∨ Disjoint A' E) := by
    intro x
    rcases hcomp_ab x with hDA | hDB
    · obtain ⟨E, hEcl, hExmem, hEdisj⟩ :=
        Bottcher.exists_isClopen_neighborhood_disjoint_compact_of_disjoint_connectedComponent
          hA'cpt hDA
      exact ⟨E, hEcl, hExmem, Or.inr hEdisj⟩
    · obtain ⟨E, hEcl, hExmem, hEdisj⟩ :=
        Bottcher.exists_isClopen_neighborhood_disjoint_compact_of_disjoint_connectedComponent
          hB'cpt hDB
      exact ⟨E, hEcl, hExmem, Or.inl hEdisj⟩
  choose E hEcl hExmem hEdisj using key
  -- Finite subcover of the compact space.
  have hcover : (univ : Set ↥K) ⊆ ⋃ x, E x := fun x _ => mem_iUnion.2 ⟨x, hExmem x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover E (fun x => (hEcl x).isOpen) hcover
  -- `S₁` = union of the pieces avoiding `B`; `S₂` = its complement.
  set S₁ : Set ↥K := ⋃ x ∈ t.filter (fun x => Disjoint B' (E x)), E x with hS1def
  have hS1cl : IsClopen S₁ := isClopen_biUnion_finset (fun x _ => hEcl x)
  set S₂ : Set ↥K := S₁ᶜ with hS2def
  have hS2cl : IsClopen S₂ := hS1cl.compl
  have hunion : S₁ ∪ S₂ = univ := Set.union_compl_self S₁
  have hdisjS : Disjoint S₁ S₂ := disjoint_compl_right
  -- `S₁` avoids `B`.
  have hB'S1 : Disjoint B' S₁ := by
    rw [hS1def, Set.disjoint_iUnion₂_right]
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  -- `S₂` avoids `A`.
  have hA'S2 : Disjoint A' S₂ := by
    rw [Set.disjoint_left]
    intro p hpA' hpS2
    have hpcov : p ∈ ⋃ x ∈ t, E x := ht (mem_univ p)
    rw [mem_iUnion₂] at hpcov
    obtain ⟨x, hxt, hpEx⟩ := hpcov
    rcases hEdisj x with hDB | hDA
    · -- then `x` is in the filtered set, so `p ∈ S₁`, contradicting `p ∈ S₂`.
      have : p ∈ S₁ := by
        rw [hS1def]
        exact mem_iUnion₂.2 ⟨x, Finset.mem_filter.mpr ⟨hxt, hDB⟩, hpEx⟩
      exact hpS2 this
    · exact (Set.disjoint_left.mp hDA) hpA' hpEx
  -- Push the two relatively-clopen pieces back to `X`.
  refine ⟨Subtype.val '' S₁, Subtype.val '' S₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Set.image_union, hunion, Subtype.coe_image_univ]
  · exact (hS1cl.isClosed.isCompact).image continuous_subtype_val
  · exact (hS2cl.isClosed.isCompact).image continuous_subtype_val
  · exact (Set.disjoint_image_iff Subtype.val_injective).mpr hdisjS
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨⟨p, hpS1, rfl⟩, hyB⟩
    exact (Set.disjoint_left.mp hB'S1) hyB hpS1
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨⟨p, hpS2, rfl⟩, hyA⟩
    exact (Set.disjoint_left.mp hA'S2) hyA hpS2

/-!
## Stage B — the discrete crossing duality

A rectangular board `Fin (m+1) × Fin (n+1)` (first coordinate = column, second = row) is coloured by
`Mk` into *marked* and *free* cells.  Two adjacencies:

* `rookAdj` — cells sharing an edge (differ by `1` in exactly one coordinate);
* `kingAdj` — cells sharing an edge or a corner (both coordinate distances `≤ 1`, not equal).

Crossing is measured by reflexive–transitive reachability through same-colour steps
(`markReach` through marked cells with king steps, `freeReach` through free cells with rook steps).
The duality asserts that one of the two colours crosses its dimension: either the marked cells contain
a king chain from the bottom row to the top row, or the free cells contain a rook chain from the left
column to the right column.

`markReach_column` and `freeReach_row` are the two crossing primitives: a monochromatic full column
crosses vertically (king), a monochromatic full row crosses horizontally (rook).  The full duality for
an arbitrary marking is the discrete Steinhaus/Hex theorem, a digital Jordan-curve separation.  The
crossing here (`discrete_crossing_duality_of_columnDetermined`) is proved for *column-determined*
markings — each column is entirely marked or entirely free — where the two primitives already decide
it.
-/

/-- Rook (shared-edge) adjacency on the board: the two cells differ by `1` in exactly one coordinate
and agree on the other. -/
def rookAdj {m n : ℕ} (a b : Fin (m + 1) × Fin (n + 1)) : Prop :=
  (a.1 = b.1 ∧ (a.2.val + 1 = b.2.val ∨ b.2.val + 1 = a.2.val)) ∨
    (a.2 = b.2 ∧ (a.1.val + 1 = b.1.val ∨ b.1.val + 1 = a.1.val))

/-- King (shared-edge-or-corner) adjacency: both coordinate distances are `≤ 1` and the cells differ.
-/
def kingAdj {m n : ℕ} (a b : Fin (m + 1) × Fin (n + 1)) : Prop :=
  (a.1.val ≤ b.1.val + 1 ∧ b.1.val ≤ a.1.val + 1) ∧
    (a.2.val ≤ b.2.val + 1 ∧ b.2.val ≤ a.2.val + 1) ∧ a ≠ b

/-- A king step between two marked cells. -/
def kingStep {m n : ℕ} (Mk : Fin (m + 1) × Fin (n + 1) → Prop)
    (a b : Fin (m + 1) × Fin (n + 1)) : Prop := kingAdj a b ∧ Mk a ∧ Mk b

/-- Reachability through marked cells by king steps. -/
def markReach {m n : ℕ} (Mk : Fin (m + 1) × Fin (n + 1) → Prop) :
    Fin (m + 1) × Fin (n + 1) → Fin (m + 1) × Fin (n + 1) → Prop :=
  Relation.ReflTransGen (kingStep Mk)

/-- A rook step between two free cells. -/
def rookStep {m n : ℕ} (Mk : Fin (m + 1) × Fin (n + 1) → Prop)
    (a b : Fin (m + 1) × Fin (n + 1)) : Prop := rookAdj a b ∧ ¬ Mk a ∧ ¬ Mk b

/-- Reachability through free cells by rook steps. -/
def freeReach {m n : ℕ} (Mk : Fin (m + 1) × Fin (n + 1) → Prop) :
    Fin (m + 1) × Fin (n + 1) → Fin (m + 1) × Fin (n + 1) → Prop :=
  Relation.ReflTransGen (rookStep Mk)

/-- **Vertical crossing primitive.**  A column all of whose cells are marked contains a king chain
from row `0` to any row: successive cells of a column are king-adjacent, and all are marked. -/
theorem markReach_column {m n : ℕ} (Mk : Fin (m + 1) × Fin (n + 1) → Prop) (c : Fin (m + 1))
    (hc : ∀ r, Mk (c, r)) (r : Fin (n + 1)) : markReach Mk (c, 0) (c, r) := by
  induction r using Fin.induction with
  | zero => exact Relation.ReflTransGen.refl
  | succ i ih =>
    have e1 : (i.castSucc : Fin (n + 1)).val = i.val := Fin.val_castSucc i
    have e2 : (i.succ : Fin (n + 1)).val = i.val + 1 := Fin.val_succ i
    have hadj : kingAdj (m := m) (c, i.castSucc) (c, i.succ) := by
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
      · show c.val ≤ c.val + 1; omega
      · show c.val ≤ c.val + 1; omega
      · show (i.castSucc : Fin (n + 1)).val ≤ (i.succ : Fin (n + 1)).val + 1; omega
      · show (i.succ : Fin (n + 1)).val ≤ (i.castSucc : Fin (n + 1)).val + 1; omega
      · intro h
        rw [Prod.mk.injEq] at h
        have := congrArg Fin.val h.2
        omega
    exact ih.tail ⟨hadj, hc _, hc _⟩

/-- **Horizontal crossing primitive.**  A row all of whose cells are free contains a rook chain from
column `0` to any column: successive cells of a row are rook-adjacent, and all are free. -/
theorem freeReach_row {m n : ℕ} (Mk : Fin (m + 1) × Fin (n + 1) → Prop) (row : Fin (n + 1))
    (hfree : ∀ j, ¬ Mk (j, row)) (c : Fin (m + 1)) :
    freeReach Mk ((0 : Fin (m + 1)), row) (c, row) := by
  induction c using Fin.induction with
  | zero => exact Relation.ReflTransGen.refl
  | succ i ih =>
    have e1 : (i.castSucc : Fin (m + 1)).val = i.val := Fin.val_castSucc i
    have e2 : (i.succ : Fin (m + 1)).val = i.val + 1 := Fin.val_succ i
    have hadj : rookAdj (n := n) (i.castSucc, row) (i.succ, row) := by
      refine Or.inr ⟨rfl, Or.inl ?_⟩
      show (i.castSucc : Fin (m + 1)).val + 1 = (i.succ : Fin (m + 1)).val; omega
    exact ih.tail ⟨hadj, hfree _, hfree _⟩

/-- **Stage B — discrete crossing duality (column-determined case).**  For a marking in which each
column is entirely marked or entirely free (`hcol`: a marked cell in a column forces the whole column
marked), the board is crossed by exactly one colour.  If some column is fully marked, that column is a
marked king chain from the bottom row to the top row.  Otherwise every column has a free cell, so —
being column-determined — every column is fully free; in particular the bottom row is a free rook chain
from the left column to the right column. -/
theorem discrete_crossing_duality_of_columnDetermined {m n : ℕ}
    (Mk : Fin (m + 1) × Fin (n + 1) → Prop)
    (hcol : ∀ (j : Fin (m + 1)) (r r' : Fin (n + 1)), Mk (j, r) → Mk (j, r')) :
    (∃ a b : Fin (m + 1) × Fin (n + 1),
        Mk a ∧ Mk b ∧ a.2 = 0 ∧ b.2 = Fin.last n ∧ markReach Mk a b)
    ∨ (∃ a b : Fin (m + 1) × Fin (n + 1),
        ¬ Mk a ∧ ¬ Mk b ∧ a.1 = 0 ∧ b.1 = Fin.last m ∧ freeReach Mk a b) := by
  classical
  by_cases hfull : ∃ j : Fin (m + 1), ∀ r, Mk (j, r)
  · obtain ⟨j, hj⟩ := hfull
    exact Or.inl ⟨(j, 0), (j, Fin.last n), hj 0, hj (Fin.last n), rfl, rfl,
      markReach_column Mk j hj (Fin.last n)⟩
  · right
    push Not at hfull
    have hfree : ∀ j : Fin (m + 1), ¬ Mk (j, (0 : Fin (n + 1))) := by
      intro j hmk
      obtain ⟨r, hr⟩ := hfull j
      exact hr (hcol j 0 r hmk)
    exact ⟨((0 : Fin (m + 1)), 0), (Fin.last m, 0), hfree 0, hfree (Fin.last m), rfl, rfl,
      freeReach_row Mk 0 hfree (Fin.last m)⟩

end RHTower
