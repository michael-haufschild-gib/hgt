import GaloisForLFunctions.HTGeometry.FamilyBuildingStep

/-!
# The disjoint union of interval buildings is connected component by component

In degree zero the Mayer--Vietoris map onto the union is an epimorphism on homology, so it is enough
to see that the componentwise map to the atoms acts as the identity after restriction to the base
and to the pieces.

On the base that is immediate: the base folds onto the atoms, so the fold is the identity on homology
in every degree.  On a piece it is a chain of four comparisons: an element of the star is below its
centre, the centre is above the chosen element of the intersection, that element joins with the atom
inside the interval — because it does not span — and the atom is below that join.  Each comparison of
monotone maps gives a homotopy of the induced maps of order complexes.

The hypothesis is exactly that each intersection is nonempty: the interval below each coatom must
contain something, which is what fails only in the degenerate ranks.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u c

variable {L : Type u} [Lattice L] [BoundedOrder L] [IsModularLattice L] {ι : Type u} {W p : ι → L}

omit [IsModularLattice L] in
/-- In a nonempty component the atom is strictly below the top. -/
theorem atom_lt_famTop (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a) (q : famBuilding W) :
    p (Subtype.val q).1 < W (Subtype.val q).1 := by
  refine lt_of_le_of_ne (hpW _) (fun heq => ?_)
  have hlt : ((Subtype.val q).2 : L) < p (Subtype.val q).1 := heq ▸ q.2
  exact absurd ((hp _).lt_iff.1 hlt) (ne_of_gt (Subtype.val q).2.2.1)

/-- Sending every element of the disjoint union to the atom of its own component. -/
def famAtomCentre (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a) :
    famBuilding W →o famBuilding W where
  toFun q :=
    ⟨((Subtype.val q).1,
      ⟨p (Subtype.val q).1, (hp _).1.bot_lt,
        lt_of_lt_of_le (atom_lt_famTop hp hpW q) le_top⟩), atom_lt_famTop hp hpW q⟩
  monotone' q q' h := by
    obtain ⟨hidx, -⟩ := famPoset_le_iff.1 h
    refine ⟨hidx, ?_⟩
    show p (Subtype.val q).1 ≤ p (Subtype.val q').1
    rw [hidx]

/-- The atom map, as a map of order complexes. -/
def famAtomMap (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a) :
    nerve (famBuilding W) ⟶ nerve (famBuilding W) :=
  nerveFunctor.map (Monotone.functor (famAtomCentre hp hpW).monotone).toCatHom

/-- The inclusion of the base into the disjoint union. -/
def famBuildingBaseIncl : (famCoverBase W p : Type u) →o famBuilding W where
  toFun x := x
  monotone' _ _ h := h

omit [IsModularLattice L] in
/-- **The atom map restricted to the base is the base's own fold onto the atoms.** -/
theorem famBuildingBaseIncl_comp_atomCentre (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a) :
    (famAtomCentre hp hpW).comp (famBuildingBaseIncl (W := W) (p := p))
      = (famBuildingBaseIncl (W := W) (p := p)).comp (famBaseCentre hp hpW) := rfl

/-- The chosen element of an intersection lies in the base. -/
theorem chosen_mem_base (v : famCoverIndex W p → properPart L)
    (hv : ∀ c, v c ∈ properBelow (famCoverTop c)) (hp : ∀ a, IsAtom (p a))
    (c : famCoverIndex W p) :
    v c ∈ notSpanningBelow (W (Subtype.val c).1) (p (Subtype.val c).1) := by
  have h := hv c
  rw [← notSpanningBelow_inter_star (hp (Subtype.val c).1) c.2] at h
  exact h.1

/-- The centre of a piece, as a map from the disjoint union of the pieces. -/
def piecesToCentre : famPoset (fun c : famCoverIndex W p =>
    generalStar (famCoverCentre W p c)) →o famBuilding W where
  toFun q := famCoverCentre W p (Subtype.val q).1
  monotone' q q' h := by
    obtain ⟨hidx, -⟩ := famPoset_le_iff.1 h
    refine famPoset_le_iff.2 ⟨?_, ?_⟩
    · show (Subtype.val (famCoverCentre W p (Subtype.val q).1)).1
        = (Subtype.val (famCoverCentre W p (Subtype.val q').1)).1
      rw [hidx]
    · show ((Subtype.val (famCoverCentre W p (Subtype.val q).1)).2 : properPart L)
        ≤ (Subtype.val (famCoverCentre W p (Subtype.val q').1)).2
      rw [hidx]

/-- The chosen element of the intersection, as a map from the disjoint union of the pieces. -/
def piecesToChosen (v : famCoverIndex W p → properPart L)
    (hv : ∀ c, v c ∈ properBelow (famCoverTop c)) :
    famPoset (fun c : famCoverIndex W p =>
      generalStar (famCoverCentre W p c)) →o famBuilding W where
  toFun q :=
    ⟨((Subtype.val (Subtype.val q).1).1, v (Subtype.val q).1),
      lt_trans (hv (Subtype.val q).1) (famCoverTop_lt (Subtype.val q).1)⟩
  monotone' q q' h := by
    obtain ⟨hidx, -⟩ := famPoset_le_iff.1 h
    refine ⟨?_, ?_⟩
    · show ((Subtype.val (Subtype.val q).1).1 : ι) = ((Subtype.val (Subtype.val q').1).1 : ι)
      rw [hidx]
    · show v (Subtype.val q).1 ≤ v (Subtype.val q').1
      rw [hidx]

/-- The join of the chosen element with the atom, as a map from the disjoint union of the pieces. -/
def piecesToJoin (v : famCoverIndex W p → properPart L)
    (hv : ∀ c, v c ∈ properBelow (famCoverTop c)) (hp : ∀ a, IsAtom (p a))
    (hpW : ∀ a, p a ≤ W a) :
    famPoset (fun c : famCoverIndex W p =>
      generalStar (famCoverCentre W p c)) →o famBuilding W where
  toFun q :=
    ⟨((Subtype.val (Subtype.val q).1).1,
      ⟨((v (Subtype.val q).1 : properPart L) : L) ⊔ p (Subtype.val (Subtype.val q).1).1,
        lt_of_lt_of_le (v (Subtype.val q).1).2.1 le_sup_left,
        lt_of_lt_of_le (lt_of_le_of_ne (sup_le (le_of_lt (chosen_mem_base v hv hp _).1)
          (hpW _)) (chosen_mem_base v hv hp _).2) le_top⟩),
      lt_of_le_of_ne (sup_le (le_of_lt (chosen_mem_base v hv hp _).1) (hpW _))
        (chosen_mem_base v hv hp _).2⟩
  monotone' q q' h := by
    obtain ⟨hidx, -⟩ := famPoset_le_iff.1 h
    refine ⟨?_, ?_⟩
    · show ((Subtype.val (Subtype.val q).1).1 : ι) = ((Subtype.val (Subtype.val q').1).1 : ι)
      rw [hidx]
    · show ((v (Subtype.val q).1 : properPart L) : L) ⊔ p (Subtype.val (Subtype.val q).1).1
        ≤ ((v (Subtype.val q').1 : properPart L) : L) ⊔ p (Subtype.val (Subtype.val q').1).1
      rw [hidx]

section Comparisons

variable (v : famCoverIndex W p → properPart L) (hv : ∀ c, v c ∈ properBelow (famCoverTop c))
  (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a)

/-- An element of a piece lies below the piece's centre. -/
theorem piecesProj_le_centre (hp : ∀ a, IsAtom (p a))
    (q : famPoset (fun c : famCoverIndex W p => generalStar (famCoverCentre W p c))) :
    famPosetProj (fun c : famCoverIndex W p => generalStar (famCoverCentre W p c)) q
      ≤ piecesToCentre q := by
  obtain ⟨hidx, hstar⟩ := mem_generalStar_famCoverCentre.1 q.2
  refine ⟨hidx, ?_⟩
  refine le_of_mem_generalStar_spanningBelow (hp _) ((Subtype.val q).1).2 ?_ hstar
  rw [← hidx]
  exact ((Subtype.val q).2).2

omit [IsModularLattice L] in
/-- The chosen element of an intersection lies below the piece's centre. -/
theorem piecesChosen_le_centre (q : famPoset (fun c : famCoverIndex W p =>
    generalStar (famCoverCentre W p c))) :
    piecesToChosen v hv q ≤ piecesToCentre q :=
  ⟨rfl, le_of_lt (hv (Subtype.val q).1)⟩

/-- The chosen element lies below its join with the atom. -/
theorem piecesChosen_le_join (q : famPoset (fun c : famCoverIndex W p =>
    generalStar (famCoverCentre W p c))) :
    piecesToChosen v hv q ≤ piecesToJoin v hv hp hpW q :=
  ⟨rfl, le_sup_left⟩

/-- The atom of the component lies below that join. -/
theorem piecesAtom_le_join (q : famPoset (fun c : famCoverIndex W p =>
    generalStar (famCoverCentre W p c))) :
    (famAtomCentre hp hpW).comp
        (famPosetProj (fun c : famCoverIndex W p => generalStar (famCoverCentre W p c))) q
      ≤ piecesToJoin v hv hp hpW q := by
  obtain ⟨hidx, -⟩ := mem_generalStar_famCoverCentre.1 q.2
  refine ⟨hidx, ?_⟩
  show p (Subtype.val (Subtype.val q).2).1
    ≤ ((v (Subtype.val q).1 : properPart L) : L) ⊔ p (Subtype.val (Subtype.val q).1).1
  rw [hidx]
  exact le_sup_right

end Comparisons

section Homology

variable {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Preadditive C]
  [CategoryWithHomology C]

omit [IsModularLattice L] in
/-- The inclusion of the base's order complex is the nerve of the inclusion of posets. -/
theorem nerveSubcomplexIso_inv_comp_base_ι :
    (nerveSubcomplexIso (famCoverBase W p)).inv ≫ (nerveSubcomplex (famCoverBase W p)).ι
      = nerveFunctor.map (Monotone.functor (famBuildingBaseIncl (W := W) (p := p)).monotone).toCatHom :=
  rfl

omit [IsModularLattice L] in
/-- **On the base the atom map acts as the identity on homology.** -/
theorem homologyMap_base_atom (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a) (R : C) (n : ℕ) :
    SSet.homologyMap (nerveSubcomplex (famCoverBase W p)).ι R n
        ≫ SSet.homologyMap (nerveFunctor.map
          (Monotone.functor (famAtomCentre hp hpW).monotone).toCatHom) R n
      = SSet.homologyMap (nerveSubcomplex (famCoverBase W p)).ι R n := by
  have hι : (nerveSubcomplex (famCoverBase W p)).ι
      = (nerveSubcomplexIso (famCoverBase W p)).hom ≫ nerveFunctor.map
        (Monotone.functor (famBuildingBaseIncl (W := W) (p := p)).monotone).toCatHom := by
    rw [← nerveSubcomplexIso_inv_comp_base_ι]
    exact (Iso.hom_inv_id_assoc _ _).symm
  have hcomp : nerveFunctor.map
        (Monotone.functor (famBuildingBaseIncl (W := W) (p := p)).monotone).toCatHom
      ≫ nerveFunctor.map (Monotone.functor (famAtomCentre hp hpW).monotone).toCatHom
      = nerveFunctor.map (Monotone.functor (famBaseCentre hp hpW).monotone).toCatHom
        ≫ nerveFunctor.map
          (Monotone.functor (famBuildingBaseIncl (W := W) (p := p)).monotone).toCatHom := by
    rw [← nerveFunctor.map_comp, ← nerveFunctor.map_comp]
    exact congrArg (fun f : (famCoverBase W p : Type u) →o famBuilding W =>
      nerveFunctor.map (Monotone.functor f.monotone).toCatHom)
      (famBuildingBaseIncl_comp_atomCentre hp hpW)
  have key : (nerveSubcomplex (famCoverBase W p)).ι
        ≫ nerveFunctor.map (Monotone.functor (famAtomCentre hp hpW).monotone).toCatHom
      = (nerveSubcomplexIso (famCoverBase W p)).hom
        ≫ nerveFunctor.map (Monotone.functor (famBaseCentre hp hpW).monotone).toCatHom
        ≫ nerveFunctor.map
          (Monotone.functor (famBuildingBaseIncl (W := W) (p := p)).monotone).toCatHom :=
    (congrArg (fun f => f ≫ nerveFunctor.map
        (Monotone.functor (famAtomCentre hp hpW).monotone).toCatHom) hι).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun g => (nerveSubcomplexIso (famCoverBase W p)).hom ≫ g) hcomp))
  calc SSet.homologyMap (nerveSubcomplex (famCoverBase W p)).ι R n
        ≫ SSet.homologyMap (nerveFunctor.map
          (Monotone.functor (famAtomCentre hp hpW).monotone).toCatHom) R n
      = SSet.homologyMap ((nerveSubcomplex (famCoverBase W p)).ι
          ≫ nerveFunctor.map (Monotone.functor (famAtomCentre hp hpW).monotone).toCatHom) R n :=
        (SSet.homologyMap_comp _ _ _ _ _ R n).symm
    _ = SSet.homologyMap ((nerveSubcomplexIso (famCoverBase W p)).hom
          ≫ nerveFunctor.map (Monotone.functor (famBaseCentre hp hpW).monotone).toCatHom
          ≫ nerveFunctor.map
            (Monotone.functor (famBuildingBaseIncl (W := W) (p := p)).monotone).toCatHom) R n :=
        congrArg (fun f => SSet.homologyMap f R n) key
    _ = SSet.homologyMap (nerveSubcomplexIso (famCoverBase W p)).hom R n
          ≫ SSet.homologyMap (nerveFunctor.map
            (Monotone.functor (famBaseCentre hp hpW).monotone).toCatHom) R n
          ≫ SSet.homologyMap (nerveFunctor.map
            (Monotone.functor (famBuildingBaseIncl (W := W) (p := p)).monotone).toCatHom) R n := by
        rw [SSet.homologyMap_comp _ _ _ _ _ R n]
        exact congrArg (fun f => SSet.homologyMap (nerveSubcomplexIso (famCoverBase W p)).hom R n ≫ f)
          (SSet.homologyMap_comp _ _ _ _ _ R n)
    _ = SSet.homologyMap (nerveSubcomplexIso (famCoverBase W p)).hom R n
          ≫ SSet.homologyMap (nerveFunctor.map
            (Monotone.functor (famBuildingBaseIncl (W := W) (p := p)).monotone).toCatHom) R n := by
        rw [homologyMap_nerve_eq_id_of_dominated (famBaseJoin hpW) (famBaseCentre hp hpW)
          (fun x => ⟨rfl, le_sup_left⟩) (fun x => ⟨rfl, le_sup_right⟩) R n]
        exact congrArg (fun f => SSet.homologyMap (nerveSubcomplexIso (famCoverBase W p)).hom R n ≫ f)
          (Category.id_comp _)
    _ = SSet.homologyMap ((nerveSubcomplexIso (famCoverBase W p)).hom
          ≫ nerveFunctor.map
            (Monotone.functor (famBuildingBaseIncl (W := W) (p := p)).monotone).toCatHom) R n :=
        (SSet.homologyMap_comp _ _ _ _ _ R n).symm
    _ = SSet.homologyMap (nerveSubcomplex (famCoverBase W p)).ι R n :=
        congrArg (fun f => SSet.homologyMap f R n) hι.symm

/-- **On the pieces the atom map agrees with the projection, on homology.**  The chain of four
comparisons: below the centre, above the chosen element, into its join with the atom, and above the
atom. -/
theorem homologyMap_pieces_atom (v : famCoverIndex W p → properPart L)
    (hv : ∀ c, v c ∈ properBelow (famCoverTop c)) (hp : ∀ a, IsAtom (p a))
    (hpW : ∀ a, p a ≤ W a) (R : C) (n : ℕ) :
    SSet.homologyMap (nerveFunctor.map (Monotone.functor
        ((famAtomCentre hp hpW).comp (famPosetProj (fun c : famCoverIndex W p =>
          generalStar (famCoverCentre W p c)))).monotone).toCatHom) R n
      = SSet.homologyMap (nerveFunctor.map (Monotone.functor
        (famPosetProj (fun c : famCoverIndex W p =>
          generalStar (famCoverCentre W p c))).monotone).toCatHom) R n := by
  have h₁ := (nerveHomotopyOfLE (famPosetProj (fun c : famCoverIndex W p =>
      generalStar (famCoverCentre W p c))) (piecesToCentre (W := W) (p := p))
      (piecesProj_le_centre hp)).congr_homologyMap R n
  have h₂ := (nerveHomotopyOfLE (piecesToChosen v hv) (piecesToCentre (W := W) (p := p))
      (piecesChosen_le_centre v hv)).congr_homologyMap R n
  have h₃ := (nerveHomotopyOfLE (piecesToChosen v hv) (piecesToJoin v hv hp hpW)
      (piecesChosen_le_join v hv hp hpW)).congr_homologyMap R n
  have h₄ := (nerveHomotopyOfLE ((famAtomCentre hp hpW).comp
      (famPosetProj (fun c : famCoverIndex W p => generalStar (famCoverCentre W p c))))
      (piecesToJoin v hv hp hpW) (piecesAtom_le_join v hv hp hpW)).congr_homologyMap R n
  rw [h₄, ← h₃, h₂, ← h₁]

end Homology

section EmptyCase

variable {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Preadditive C]
  [CategoryWithHomology C]

omit [IsModularLattice L] in
/-- With no spanning element, every element of the disjoint union lies in the base. -/
theorem mem_famCoverBase_of_isEmpty [IsEmpty (famCoverIndex W p)] (q : famBuilding W) :
    q ∈ famCoverBase W p := by
  by_contra hq
  exact IsEmpty.false (⟨((Subtype.val q).1, (Subtype.val q).2), ⟨q.2, by
    by_contra hcon
    exact hq ⟨q.2, hcon⟩⟩⟩ : famCoverIndex W p)

/-- The fold onto the atoms, on all of the disjoint union, available when nothing spans. -/
def famJoinAll (hpW : ∀ a, p a ≤ W a)
    [IsEmpty (famCoverIndex W p)] : famBuilding W →o famBuilding W where
  toFun q :=
    ⟨((Subtype.val q).1,
      ⟨((Subtype.val q).2 : L) ⊔ p (Subtype.val q).1,
        lt_of_lt_of_le (Subtype.val q).2.2.1 le_sup_left,
        lt_of_lt_of_le (base_join_lt hpW (mem_famCoverBase_of_isEmpty q)) le_top⟩),
      base_join_lt hpW (mem_famCoverBase_of_isEmpty q)⟩
  monotone' q q' h := by
    obtain ⟨hidx, hle⟩ := famPoset_le_iff.1 h
    refine ⟨hidx, ?_⟩
    show ((Subtype.val q).2 : L) ⊔ p (Subtype.val q).1
      ≤ ((Subtype.val q').2 : L) ⊔ p (Subtype.val q').1
    rw [hidx]
    exact sup_le_sup_right hle _

omit [IsModularLattice L] in
/-- **Connectedness when nothing spans**: the whole disjoint union folds onto the atoms. -/
theorem homologyMap_famAtomMap_eq_id_of_isEmpty (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a)
    [IsEmpty (famCoverIndex W p)] (R : C) (n : ℕ) :
    SSet.homologyMap (famAtomMap hp hpW) R n = 𝟙 _ :=
  homologyMap_nerve_eq_id_of_dominated (famJoinAll hpW) (famAtomCentre hp hpW)
    (fun _ => ⟨rfl, le_sup_left⟩) (fun _ => ⟨rfl, le_sup_right⟩) R n

end EmptyCase

section Assembly

variable {C : Type c} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- **The disjoint union of interval buildings is connected component by component.**  The map
sending each element to the atom of its own component is the identity on degree-zero homology, as
soon as every coatom of every component has something strictly below it. -/
theorem homologyMap_famAtomMap_eq_id (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a)
    (v : famCoverIndex W p → properPart L) (hv : ∀ c, v c ∈ properBelow (famCoverTop c))
    [Nonempty (famCoverIndex W p)] (R : C) :
    SSet.homologyMap (famAtomMap hp hpW) R 0 = 𝟙 _ := by
  haveI hisoι : IsIso ((famSup (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
      (famCoverPieceSub (W := W) (p := p))).ι) := by
    have htop : famSup (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
        (famCoverPieceSub (W := W) (p := p)) = ⊤ := famCoverBaseSub_sup_iSup
    rw [htop]
    infer_instance
  haveI hisoh : IsIso (SSet.homologyMap ((famSup (nerve (famBuilding W))
      (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p))).ι) R 0) := by
    change IsIso ((SSet.homologyFunctor R 0).map _)
    infer_instance
  haveI hepi := epi_homologyMap_mvFamChainSnd_zero (nerve (famBuilding W)) R
    (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p))
    (fun a b hab => famCoverPieceSub_inter_le hp a b hab)
  refine sub_eq_zero.1 (zero_of_epi_comp
    (HomologicalComplex.homologyMap (mvFamChainSnd (nerve (famBuilding W)) R
        (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p))) 0
      ≫ SSet.homologyMap ((famSup (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
        (famCoverPieceSub (W := W) (p := p))).ι) R 0) ?_)
  rw [Category.assoc]
  have hbase : SSet.homologyMap (nerveSubcomplex (famCoverBase W p)).ι R 0
      ≫ SSet.homologyMap (famAtomMap hp hpW) R 0
      = SSet.homologyMap (nerveSubcomplex (famCoverBase W p)).ι R 0 :=
    homologyMap_base_atom hp hpW R 0
  have hpieces : SSet.homologyMap (nerveFunctor.map (Monotone.functor (famPosetProj
        (fun c : famCoverIndex W p => generalStar (famCoverCentre W p c))).monotone).toCatHom) R 0
      ≫ SSet.homologyMap (famAtomMap hp hpW) R 0
      = SSet.homologyMap (nerveFunctor.map (Monotone.functor (famPosetProj
        (fun c : famCoverIndex W p => generalStar (famCoverCentre W p c))).monotone).toCatHom) R 0 :=
    (SSet.homologyMap_comp _ _ _ _ _ R 0).symm.trans (homologyMap_pieces_atom v hv hp hpW R 0)
  have hA0 : HomologicalComplex.homologyMap (SSet.chainComplexMap (SSet.Subcomplex.homOfLE
        (le_famSup_base (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
          (famCoverPieceSub (W := W) (p := p)))) R) 0
      ≫ (SSet.homologyMap ((famSup (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
          (famCoverPieceSub (W := W) (p := p))).ι) R 0
        ≫ (SSet.homologyMap (famAtomMap hp hpW) R 0 - 𝟙 _)) = 0 := by
    have h1 : HomologicalComplex.homologyMap (SSet.chainComplexMap (SSet.Subcomplex.homOfLE
          (le_famSup_base (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
            (famCoverPieceSub (W := W) (p := p)))) R) 0
        ≫ SSet.homologyMap ((famSup (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
          (famCoverPieceSub (W := W) (p := p))).ι) R 0
        = SSet.homologyMap (nerveSubcomplex (famCoverBase W p)).ι R 0 :=
      (SSet.homologyMap_comp _ _ _ _ _ R 0).symm.trans
        (congrArg (fun f => SSet.homologyMap f R 0) (SSet.Subcomplex.homOfLE_ι _))
    rw [← Category.assoc, h1]
    exact (Preadditive.comp_sub _ _ _).trans
      (sub_eq_zero.2 (hbase.trans (Category.comp_id _).symm))
  have hB0 : HomologicalComplex.homologyMap (SSet.chainComplexMap
        (famSSetHom (famCoverPieceSub (W := W) (p := p))
          (famSup (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
            (famCoverPieceSub (W := W) (p := p)))
          (le_famSup_piece (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
            (famCoverPieceSub (W := W) (p := p)))) R) 0
      ≫ (SSet.homologyMap ((famSup (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
          (famCoverPieceSub (W := W) (p := p))).ι) R 0
        ≫ (SSet.homologyMap (famAtomMap hp hpW) R 0 - 𝟙 _)) = 0 := by
    have hnat : famSSetHom (famCoverPieceSub (W := W) (p := p))
          (famSup (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
            (famCoverPieceSub (W := W) (p := p)))
          (le_famSup_piece (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
            (famCoverPieceSub (W := W) (p := p)))
          ≫ (famSup (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
            (famCoverPieceSub (W := W) (p := p))).ι
        = (famPosetNerveIso (fun c : famCoverIndex W p =>
            generalStar (famCoverCentre W p c))).hom
          ≫ nerveFunctor.map (Monotone.functor (famPosetProj
            (fun c : famCoverIndex W p => generalStar (famCoverCentre W p c))).monotone).toCatHom :=
      (Iso.inv_comp_eq _).1 rfl
    have h2 : HomologicalComplex.homologyMap (SSet.chainComplexMap
          (famSSetHom (famCoverPieceSub (W := W) (p := p))
            (famSup (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
              (famCoverPieceSub (W := W) (p := p)))
            (le_famSup_piece (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
              (famCoverPieceSub (W := W) (p := p)))) R) 0
        ≫ SSet.homologyMap ((famSup (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
          (famCoverPieceSub (W := W) (p := p))).ι) R 0
        = SSet.homologyMap (famPosetNerveIso (fun c : famCoverIndex W p =>
            generalStar (famCoverCentre W p c))).hom R 0
          ≫ SSet.homologyMap (nerveFunctor.map (Monotone.functor (famPosetProj
            (fun c : famCoverIndex W p => generalStar (famCoverCentre W p c))).monotone).toCatHom)
            R 0 :=
      (SSet.homologyMap_comp _ _ _ _ _ R 0).symm.trans
        ((congrArg (fun f => SSet.homologyMap f R 0) hnat).trans
          (SSet.homologyMap_comp _ _ _ _ _ R 0))
    have hz : SSet.homologyMap (nerveFunctor.map (Monotone.functor (famPosetProj
          (fun c : famCoverIndex W p => generalStar (famCoverCentre W p c))).monotone).toCatHom) R 0
        ≫ (SSet.homologyMap (famAtomMap hp hpW) R 0 - 𝟙 _) = 0 :=
      (Preadditive.comp_sub _ _ _).trans
        (sub_eq_zero.2 (hpieces.trans (Category.comp_id _).symm))
    rw [← Category.assoc, h2]
    refine (Category.assoc _ _ _).trans ?_
    exact (congrArg (fun t => SSet.homologyMap (famPosetNerveIso (fun c : famCoverIndex W p =>
      generalStar (famCoverCentre W p c))).hom R 0 ≫ t) hz).trans comp_zero
  rw [mvFamChainSnd, biprod.desc_eq, HomologicalComplex.homologyMap_add, Preadditive.add_comp,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp, Category.assoc,
    Category.assoc, HomologicalComplex.homologyMap_neg, Preadditive.neg_comp, hA0, hB0,
    neg_zero, comp_zero, comp_zero, add_zero]

end Assembly

end GaloisForLFunctions.HTGeometry
