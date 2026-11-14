import GaloisForLFunctions.HTGeometry.FamilyCoverBaseVanishing
import GaloisForLFunctions.HTGeometry.FamilyCoverIntersection
import GaloisForLFunctions.HTGeometry.FamilyStarVanishing
import GaloisForLFunctions.HTGeometry.SimplicialMayerVietorisFamily

/-!
# The Solomon--Tits induction step, for a family of intervals at once

The cover of the disjoint union of interval buildings, fed to the Mayer--Vietoris sequence of a base
with arbitrarily many pieces.  The base is locally conical, the pieces are a disjoint union of stars,
and the intersections form the disjoint union of the interval buildings below the coatoms.  So the
homology of the disjoint union in degree `i` vanishes as soon as the same disjoint union one coatom
step down has no homology in degree `i - 1`.

That is the induction step in the form the induction consumes: hypothesis and conclusion are the same
statement, about a family.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u c

variable {L : Type u} [Lattice L] [BoundedOrder L] [IsModularLattice L] {ι : Type u} {W p : ι → L}

/-- The base of the cover, as a subcomplex of the order complex. -/
abbrev famCoverBaseSub : (nerve (famBuilding W)).Subcomplex := nerveSubcomplex (famCoverBase W p)

/-- The pieces of the cover, as subcomplexes of the order complex. -/
abbrev famCoverPieceSub (c : famCoverIndex W p) : (nerve (famBuilding W)).Subcomplex :=
  nerveSubcomplex (generalStar (famCoverCentre W p c))

omit [IsModularLattice L] in
theorem famCoverBaseSub_sup_iSup :
    (famCoverBaseSub (W := W) (p := p)) ⊔ ⨆ c : famCoverIndex W p, famCoverPieceSub c = ⊤ :=
  nerveSubcomplex_sup_iSup_eq_top (fun n x => by
    rcases famChain_mem_base_or_star n x with h | ⟨c, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, hc⟩)

theorem famCoverPieceSub_inter_le (hp : ∀ a, IsAtom (p a)) (c c' : famCoverIndex W p)
    (hcc : c ≠ c') :
    famCoverPieceSub c ⊓ famCoverPieceSub c' ≤ (famCoverBaseSub (W := W) (p := p)) := by
  rw [famCoverPieceSub, famCoverPieceSub, famCoverBaseSub, ← nerveSubcomplex_inter]
  exact nerveSubcomplex_mono (famCoverPiece_inter_subset_base hp hcc)

omit [IsModularLattice L] in
theorem famCoverBaseSub_inter_pieceSub (c : famCoverIndex W p) :
    (famCoverBaseSub (W := W) (p := p)) ⊓ famCoverPieceSub c
      = nerveSubcomplex (famCoverBase W p ∩ generalStar (famCoverCentre W p c)) := by
  rw [famCoverBaseSub, famCoverPieceSub, ← nerveSubcomplex_inter]

/-- **The disjoint union of the intersections has the homology of the smaller family.** -/
noncomputable def famCoverInterHomologyIso (hp : ∀ a, IsAtom (p a)) {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (j : ℕ) :
    (famSSet (fun c : famCoverIndex W p =>
        (famCoverBaseSub (W := W) (p := p)) ⊓ famCoverPieceSub c)).homology R j
      ≅ (nerve (famBuilding (fun c : famCoverIndex W p => famCoverTop c))).homology R j := by
  refine Iso.trans ?_ ((SSet.homologyFunctor R j).mapIso (famCoverInterNerveIso hp))
  refine Iso.trans ?_ (famPosetHomologyIso
    (fun c : famCoverIndex W p => famCoverBase W p ∩ generalStar (famCoverCentre W p c)) R j)
  exact eqToIso (by rw [funext (fun c => famCoverBaseSub_inter_pieceSub c)])

section

variable {C : Type c} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

omit [Abelian C] [HasCoproducts C] in
/-- A map out of a zero object is a monomorphism. -/
theorem mono_of_isZero_src {X Y : C} (hX : Limits.IsZero X) (f : X ⟶ Y) : Mono f :=
  ⟨fun {_} g h _ => hX.eq_of_tgt g h⟩

omit [IsModularLattice L] in
/-- **When no element spans, the cover is the base alone.**  The disjoint union is then locally
conical and has no homology above degree zero. -/
theorem isZero_homology_famBuilding_of_isEmpty (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a)
    [IsEmpty (famCoverIndex W p)] (R : C) (i : ℕ) (hi : 1 ≤ i) :
    Limits.IsZero ((nerve (famBuilding W)).homology R i) := by
  have htop : nerveSubcomplex (famCoverBase W p) = (⊤ : (nerve (famBuilding W)).Subcomplex) := by
    have h := famCoverBaseSub_sup_iSup (W := W) (p := p)
    rwa [iSup_of_empty, sup_bot_eq] at h
  have hbase := isZero_homology_famCoverBase hp hpW R i hi
  rw [htop] at hbase
  exact Limits.IsZero.of_iso hbase
    ((SSet.homologyFunctor R i).mapIso (SSet.Subcomplex.topIso (nerve (famBuilding W))).symm)

/-- **The induction step, in injectivity form.**  If the Mayer--Vietoris map is injective on homology
in degree `j`, the disjoint union has no homology in degree `i`. -/
theorem isZero_homology_famBuilding_of_mono (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a)
    [Nonempty (famCoverIndex W p)] (R : C) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j)
    (hi : 1 ≤ i)
    (hmono : Mono (HomologicalComplex.homologyMap
      (mvFamChainFst (nerve (famBuilding W)) R (famCoverBaseSub (W := W) (p := p))
        (famCoverPieceSub (W := W) (p := p))) j)) :
    Limits.IsZero ((nerve (famBuilding W)).homology R i) := by
  have hzero := isZero_homology_famSup (nerve (famBuilding W)) R
    (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p))
    (fun c c' hcc => famCoverPieceSub_inter_le hp c c' hcc) i j hij
    (isZero_homology_famCoverBase hp hpW R i hi)
    (isZero_homology_famSSet_generalStar (famCoverCentre W p) R i hi) hmono
  rw [show famSup (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
      (famCoverPieceSub (W := W) (p := p)) = ⊤ from famCoverBaseSub_sup_iSup] at hzero
  exact Limits.IsZero.of_iso hzero
    ((SSet.homologyFunctor R i).mapIso (SSet.Subcomplex.topIso (nerve (famBuilding W))).symm)

/-- **The induction step.**  If the disjoint union of the interval buildings below the coatoms has no
homology in degree `j`, the disjoint union one step up has none in degree `i`. -/
theorem isZero_homology_famBuilding_of_isZero (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a)
    [Nonempty (famCoverIndex W p)] (R : C) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j)
    (hi : 1 ≤ i)
    (hinter : Limits.IsZero
      ((nerve (famBuilding (fun c : famCoverIndex W p => famCoverTop c))).homology R j)) :
    Limits.IsZero ((nerve (famBuilding W)).homology R i) := by
  have hzeroInter : Limits.IsZero
      ((famSSet (fun c : famCoverIndex W p =>
        (famCoverBaseSub (W := W) (p := p)) ⊓ famCoverPieceSub c)).homology R j) :=
    Limits.IsZero.of_iso hinter (famCoverInterHomologyIso hp R j)
  refine isZero_homology_famBuilding_of_mono hp hpW R i j hij hi ?_
  exact mono_homologyMap_mvFamChainFst_of_right _ R _ _ j (mono_of_isZero_src hzeroInter _)

end

end GaloisForLFunctions.HTGeometry
