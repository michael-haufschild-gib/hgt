import GaloisForLFunctions.HTGeometry.FamilyCoverConnected
import GaloisForLFunctions.HTGeometry.FamilySSetMapMono

/-!
# Injectivity in degree zero for the family cover

The degree-one case of the Solomon--Tits step needs the degree-zero homology of the disjoint union
of the intersections to inject into that of the disjoint union of the pieces.  It does, because each
piece collapses onto the chosen element of its intersection: that collapse is a retraction of the
inclusion up to homology, and the resulting self-map of the intersections is componentwise constant,
hence homologically the identity — which is the connectedness of the smaller family, transported
along the order isomorphism that identifies the intersections with it.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u

variable {L : Type u} [Lattice L] [BoundedOrder L] [IsModularLattice L] {ι : Type u} {W p : ι → L}

omit [IsModularLattice L] in
/-- The intersections of the cover sit inside the pieces. -/
theorem famCoverInter_subset (c : famCoverIndex W p) :
    famCoverBase W p ∩ generalStar (famCoverCentre W p c)
      ⊆ generalStar (famCoverCentre W p c) := Set.inter_subset_right

/-- Collapsing each piece onto the chosen element of its intersection. -/
def famPieceCollapse (hp : ∀ a, IsAtom (p a)) (v : famCoverIndex W p → properPart L)
    (hv : ∀ c, v c ∈ properBelow (famCoverTop c)) :
    famPoset (fun c : famCoverIndex W p => generalStar (famCoverCentre W p c))
      →o famPoset (fun c : famCoverIndex W p =>
        famCoverBase W p ∩ generalStar (famCoverCentre W p c)) where
  toFun q :=
    ⟨((Subtype.val q).1,
      ⟨((Subtype.val (Subtype.val q).1).1, v (Subtype.val q).1),
        lt_trans (hv (Subtype.val q).1) (famCoverTop_lt (Subtype.val q).1)⟩),
      (mem_famCoverInter hp).2 ⟨rfl, hv (Subtype.val q).1⟩⟩
  monotone' q q' h := by
    obtain ⟨hidx, -⟩ := famPoset_le_iff.1 h
    refine ⟨hidx, ?_⟩
    refine famPoset_le_iff.2 ⟨?_, ?_⟩
    · show ((Subtype.val (Subtype.val q).1).1 : ι) = ((Subtype.val (Subtype.val q').1).1 : ι)
      rw [hidx]
    · show ((v (Subtype.val q).1 : properPart L) : L) ≤ ((v (Subtype.val q').1 : properPart L) : L)
      rw [hidx]

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- **The collapse is a retraction of the inclusion, up to homology**, once the componentwise
constant self-map of the intersections is homologically the identity. -/
theorem mono_famPosetNerveMap_famCoverInter (hp : ∀ a, IsAtom (p a))
    (v : famCoverIndex W p → properPart L) (hv : ∀ c, v c ∈ properBelow (famCoverTop c))
    (R : C)
    (hconst : SSet.homologyMap (nerveFunctor.map (Monotone.functor
      ((famPieceCollapse hp v hv).comp
        (famPosetMap (famCoverInter_subset (W := W) (p := p)))).monotone).toCatHom) R 0 = 𝟙 _) :
    Mono (SSet.homologyMap
      (famPosetNerveMap (famCoverInter_subset (W := W) (p := p))) R 0) := by
  have hm := mono_homologyMap_nerve_of_comp_id
    (famPosetMap (famCoverInter_subset (W := W) (p := p))) (famPieceCollapse hp v hv) R 0 hconst
  exact hm

/-- **Injectivity in degree zero for the Mayer--Vietoris map of the family cover.** -/
theorem mono_homologyMap_mvFamChainFst_zero (hp : ∀ a, IsAtom (p a))
    (v : famCoverIndex W p → properPart L) (hv : ∀ c, v c ∈ properBelow (famCoverTop c))
    (R : C)
    (hconst : SSet.homologyMap (nerveFunctor.map (Monotone.functor
      ((famPieceCollapse hp v hv).comp
        (famPosetMap (famCoverInter_subset (W := W) (p := p)))).monotone).toCatHom) R 0 = 𝟙 _) :
    Mono (HomologicalComplex.homologyMap (mvFamChainFst (nerve (famBuilding W)) R
      (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p))) 0) := by
  refine mono_homologyMap_mvFamChainFst_of_right _ R _ _ 0 ?_
  refine mono_homologyMap_famSSetMap_congr
    (funext (fun c => famCoverBaseSub_inter_pieceSub (W := W) (p := p) c))
    (fun _ => inf_le_right)
    (fun c => nerveSubcomplex_mono (famCoverInter_subset (W := W) (p := p) c)) R 0 ?_
  exact mono_homologyMap_famSSetMap_of_nerve (famCoverInter_subset (W := W) (p := p)) R 0
    (mono_famPosetNerveMap_famCoverInter hp v hv R hconst)

/-- **The componentwise collapse is homologically the identity**, because it is so on the smaller
family and the two are identified by an order isomorphism. -/
theorem homologyMap_famPieceCollapse_eq_id (hp : ∀ a, IsAtom (p a))
    (v : famCoverIndex W p → properPart L) (hv : ∀ c, v c ∈ properBelow (famCoverTop c))
    (p' : famCoverIndex W p → L) (hp' : ∀ c, IsAtom (p' c))
    (hp'W : ∀ c, p' c ≤ famCoverTop c) (R : C)
    (hsmall : SSet.homologyMap (famAtomMap hp' hp'W) R 0 = 𝟙 _) :
    SSet.homologyMap (nerveFunctor.map (Monotone.functor
      ((famPieceCollapse hp v hv).comp
        (famPosetMap (famCoverInter_subset (W := W) (p := p)))).monotone).toCatHom) R 0 = 𝟙 _ := by
  have hconj := homologyMap_nerve_eq_id_of_orderIso (famCoverInterOrderIso hp)
    (famAtomCentre hp' hp'W) R 0 hsmall
  refine homologyMap_nerve_eq_id_of_comp _ (orderIsoConj (famCoverInterOrderIso hp)
    (famAtomCentre hp' hp'W)) ?_ R 0 hconj
  refine OrderHom.ext _ _ (funext (fun x => ?_))
  rfl

/-- **Degree one of the Solomon--Tits step.**  With a chosen element below each coatom, and atoms and
chosen elements one level further down, the disjoint union has no homology in degree one. -/
theorem isZero_homology_famBuilding_one (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a)
    [Nonempty (famCoverIndex W p)]
    (v : famCoverIndex W p → properPart L) (hv : ∀ c, v c ∈ properBelow (famCoverTop c))
    (p' : famCoverIndex W p → L) (hp' : ∀ c, IsAtom (p' c))
    (hp'W : ∀ c, p' c ≤ famCoverTop c) (R : C)
    (hsmall : SSet.homologyMap (famAtomMap hp' hp'W) R 0 = 𝟙 _) :
    Limits.IsZero ((nerve (famBuilding W)).homology R 1) :=
  isZero_homology_famBuilding_of_mono hp hpW R 1 0 rfl le_rfl
    (mono_homologyMap_mvFamChainFst_zero hp v hv R
      (homologyMap_famPieceCollapse_eq_id hp v hv p' hp' hp'W R hsmall))

end

end GaloisForLFunctions.HTGeometry
