import GaloisForLFunctions.HTGeometry.SolomonDescentStep

/-!
# Frames of a subspace and the rank of a coatom

Over a division ring the frames of a subspace are its bases: the lines spanned by the vectors of a
basis are independent atoms whose join is the subspace.  So a subspace of dimension `r` has a frame
indexed by any type with `r` elements, and the coatoms produced by the Solomon--Tits cover have
dimension one less, which is what lets the induction on the rank run.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite Module

universe u

section

variable {K V : Type u} [DivisionRing K] [AddCommGroup V] [Module K V] {ι : Type u}

/-- **The frame of a subspace given by a basis of it**: the lines of the basis vectors. -/
noncomputable def frameOfBasis {U : Submodule K V} (b : Basis ι K ↥U) :
    LatticeFrame (Submodule K V) ι U where
  atom i := (K ∙ (b i : ↥U)).map U.subtype
  isAtom i := by
    refine Submodule.isAtom_iff_finrank_eq_one.2 ?_
    have hb : (b i : ↥U) ≠ 0 := b.ne_zero i
    have hmap : finrank K ((K ∙ (b i : ↥U)).map U.subtype) = finrank K (K ∙ (b i : ↥U)) :=
      (Submodule.equivMapOfInjective U.subtype U.injective_subtype _).symm.finrank_eq
    rw [hmap, finrank_span_singleton hb]
  indep :=
    LinearMap.iSupIndep_map U.subtype U.injective_subtype
      b.linearIndependent.iSupIndep_span_singleton
  sup_eq := by
    rw [← Submodule.map_iSup]
    have hspan : (⨆ i, K ∙ (b i : ↥U)) = ⊤ := by
      rw [← Submodule.span_range_eq_iSup]
      exact b.span_eq
    rw [hspan, Submodule.map_subtype_top]

variable [FiniteDimensional K V]

/-- **A subspace has a frame indexed by any type of its dimension.** -/
theorem nonempty_frame_of_finrank [Finite ι] {U : Submodule K V}
    (h : Nat.card ι = finrank K ↥U) : Nonempty (LatticeFrame (Submodule K V) ι U) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = finrank K ↥U := by rwa [← Nat.card_eq_fintype_card]
  exact ⟨frameOfBasis ((Module.finBasis K ↥U).reindex
    (Fintype.equivFinOfCardEq hcard).symm)⟩

end

/-! ## The rank of a coatom of the cover -/

section Rank

variable {K V : Type u} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {κ : Type u} {W p : κ → Submodule K V}

/-- **A coatom of the cover has dimension one less than its component.** -/
theorem finrank_famCoverTop (hp : ∀ a, IsAtom (p a)) (c : famCoverIndex W p) :
    finrank K ↥(famCoverTop c) + 1 = finrank K ↥(W (Subtype.val c).1) := by
  have hspan : famCoverTop c ⊔ p (Subtype.val c).1 = W (Subtype.val c).1 := c.2.2
  have hlt : famCoverTop c < W (Subtype.val c).1 := c.2.1
  have hinf : famCoverTop c ⊓ p (Subtype.val c).1 = ⊥ :=
    disjoint_iff.1 ((LatticeFrame.disjoint_of_isAtom_of_lt (hp _) hlt hspan).symm)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (famCoverTop c) (p (Subtype.val c).1)
  rw [hspan, hinf, finrank_bot, add_zero,
    Submodule.isAtom_iff_finrank_eq_one.1 (hp (Subtype.val c).1)] at hsum
  exact hsum.symm

end Rank

end GaloisForLFunctions.HTGeometry
