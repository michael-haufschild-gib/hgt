import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace

/-! A closed cut that misses a point of each irreducible component lowers
Krull dimension. Iterating such choices gives an empty intersection. -/

noncomputable section

open Set Topology TopologicalSpace TopologicalSpace.IrreducibleCloseds Order

namespace GlobalTheory.SchemeCohomology

/-- For an open cover, a chain of irreducible closed sets is visible on any
member containing a point of its smallest term. -/
theorem topologicalKrullDim_lt_of_openCover {X : Type*} [TopologicalSpace X]
    {ι : Type*} (U : ι → Opens X) (hcov : ⨆ i, U i = ⊤) (d : ℕ)
    (hU : ∀ i, topologicalKrullDim (U i) < d) : topologicalKrullDim X < d := by
  apply krullDim_lt_coe_iff.mpr
  intro p
  obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, U i from hcov.symm ▸ trivial)
  let E := orderIsoOfIsOpenEmbedding (Subtype.val : U i → X) (U i).isOpen.isOpenEmbedding_subtypeVal
  let f (j : Fin (p.length + 1)) : IrreducibleCloseds (U i) :=
    E.symm ⟨p j, ⟨⟨x, hi⟩, p.head_le j hx⟩⟩
  have hf : StrictMono f := fun a b h => E.symm.strictMono (p.strictMono h)
  let q : LTSeries (IrreducibleCloseds (U i)) := LTSeries.mk p.length f hf
  exact krullDim_lt_coe_iff.mp (hU i) q

/-- If no component of the ambient space is contained in a closed subset,
any irreducible chain in the subset extends by one term in the ambient space. -/
theorem topologicalKrullDim_closedCut_lt {X : Type*} [TopologicalSpace X] {Z : Set X}
    (hZ : IsClosed Z) (hcut : ∀ C ∈ irreducibleComponents X, ¬ C ⊆ Z)
    (d : ℕ) (hd : topologicalKrullDim X < (d + 1 : ℕ)) : topologicalKrullDim Z < d := by
  apply krullDim_lt_coe_iff.mpr
  intro p
  let g := map (Subtype.val : Z → X) continuous_subtype_val
  have hg : StrictMono g := map_strictMono_of_isInducing IsInducing.subtypeVal
  let q := p.map g hg
  have hqZ : (q.last : Set X) ⊆ Z :=
    closure_minimal (fun _ hx => by obtain ⟨x, _, rfl⟩ := hx; exact x.2) hZ
  obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (q.last : Set X) q.last.isIrreducible
  let C' : IrreducibleCloseds X := ⟨C, hC.1, isClosed_of_mem_irreducibleComponents C hC⟩
  have hlt : q.last < C' :=
    lt_of_le_of_ne hsub fun e => hcut C hC (by
      change (C' : Set X) ⊆ Z
      rw [← e]
      exact hqZ)
  have hlen := krullDim_lt_coe_iff.mp hd (q.snoc C' hlt)
  simpa [q] using hlen

private theorem isEmpty_of_topologicalKrullDim_lt_zero {X : Type*} [TopologicalSpace X]
    (h : topologicalKrullDim X < 0) : IsEmpty X := by
  refine ⟨fun x => ?_⟩
  let Z : IrreducibleCloseds X :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  exact (not_le_of_gt h) (krullDim_nonneg_iff.mpr ⟨Z⟩)

/-- If each cut can avoid any prescribed finite set of points, then d
successive cuts suffice on a Noetherian space of dimension less than d. -/
theorem exists_cuts_empty_intersection {F : Type*} (d : ℕ) (V : Fin d → Set F)
    {X : Type*} [TopologicalSpace X] [NoetherianSpace X] (Z : F → Set X)
    (hclosed : ∀ f, IsClosed (Z f)) (hd : topologicalKrullDim X < d)
    (havoid : ∀ j (S : Finset X), ∃ f ∈ V j, ∀ x ∈ S, x ∉ Z f) :
    ∃ f : Fin d → F, (∀ j, f j ∈ V j) ∧ ∀ x : X, ∃ j, x ∉ Z (f j) := by
  induction d generalizing X with
  | zero =>
    letI := isEmpty_of_topologicalKrullDim_lt_zero hd
    exact ⟨Fin.elim0, fun j => Fin.elim0 j, isEmptyElim⟩
  | succ d ih =>
    classical
    letI : Fintype (irreducibleComponents X) :=
      NoetherianSpace.finite_irreducibleComponents.fintype
    choose x hx using fun C : irreducibleComponents X => C.2.1.nonempty
    obtain ⟨f, hf, hfx⟩ := havoid 0 (Finset.univ.image x)
    have hcut (C : Set X) (hC : C ∈ irreducibleComponents X) : ¬ C ⊆ Z f :=
      fun h => hfx (x ⟨C, hC⟩) (Finset.mem_image_of_mem x (Finset.mem_univ _)) (h (hx ⟨C, hC⟩))
    have hdim := topologicalKrullDim_closedCut_lt (hclosed f) hcut d hd
    obtain ⟨g, hg, hge⟩ := ih (fun j => V j.succ)
      (fun a => Subtype.val ⁻¹' Z a) (fun a => (hclosed a).preimage continuous_subtype_val)
      hdim (fun j S => by
        obtain ⟨a, ha, h⟩ := havoid j.succ (S.image Subtype.val)
        exact ⟨a, ha, fun y hy => h y.1 (Finset.mem_image_of_mem _ hy)⟩)
    refine ⟨Fin.cons f g, Fin.cases hf hg, fun y => ?_⟩
    by_cases hy : y ∈ Z f
    · obtain ⟨j, hj⟩ := hge ⟨y, hy⟩
      exact ⟨j.succ, hj⟩
    · exact ⟨0, hy⟩

end GlobalTheory.SchemeCohomology
