import GaloisForLFunctions.HTGeometry.BuildingSpanningCover
import GaloisForLFunctions.HTGeometry.FamilyStarVanishing
import GaloisForLFunctions.HTGeometry.SimplicialMayerVietorisFamily

/-!
# The Solomon--Tits induction step

Assembling the cover of the order complex of the proper part of a bounded modular lattice by the
elements that do not span with a fixed atom together with the stars of the elements that do:

* the base is conically contractible, by joining with the atom;
* the disjoint union of the pieces is a disjoint union of cones, so it has no homology above degree
  zero;
* the pieces meet each other only inside the base, so the many-piece Mayer--Vietoris sequence
  applies with no finiteness assumption on how many pieces there are;
* the base meets a piece exactly in the elements strictly below that coatom.

What is left to the induction is the last term: the disjoint union of the order complexes of the
intervals below the coatoms, one step smaller than the lattice one started with.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u w

variable {L : Type u} [Lattice L] [BoundedOrder L]

/-- The elements that span with `p`, as an index type. -/
abbrev spanningIndex (p : L) : Type u := {V : properPart L // V ∈ spanning p}

/-- The base of the cover: the full subcomplex on the elements that do not span with `p`. -/
def nerveCoverBase (p : L) : (nerve (properPart L)).Subcomplex := nerveSubcomplex (notSpanning p)

/-- The pieces of the cover: the stars of the elements that do span with `p`. -/
def coverPiece (p : L) (a : spanningIndex p) : (nerve (properPart L)).Subcomplex :=
  nerveSubcomplex (generalStar (a : properPart L))

theorem coverPiece_eq (p : L) :
    coverPiece p = fun a : spanningIndex p => nerveSubcomplex (generalStar (a : properPart L)) :=
  rfl

/-- **The base and the pieces cover.** -/
theorem nerveCoverBase_sup_iSup_coverPiece (p : L) :
    nerveCoverBase p ⊔ ⨆ a : spanningIndex p, coverPiece p a = ⊤ :=
  nerveSubcomplex_notSpanning_sup_iSup_star p

/-- The fold of the base onto the atom. -/
theorem notSpanning_join_mem {p : L} {U : properPart L} (hU : U ∈ notSpanning p) :
    (⟨U.1 ⊔ p, lt_of_lt_of_le U.2.1 le_sup_left, lt_of_le_of_ne le_top hU⟩ :
      properPart L) ∈ notSpanning p := by
  show (U.1 ⊔ p) ⊔ p ≠ ⊤
  rw [sup_assoc, sup_idem]
  exact hU

/-- Joining with the atom stays inside the base and dominates. -/
def notSpanningJoinAtom (p : L) :
    (notSpanning p : Type u) →o (notSpanning p : Type u) where
  toFun U := ⟨⟨U.1.1 ⊔ p, lt_of_lt_of_le U.1.2.1 le_sup_left, lt_of_le_of_ne le_top U.2⟩,
    notSpanning_join_mem U.2⟩
  monotone' U U' h := by
    show U.1.1 ⊔ p ≤ U'.1.1 ⊔ p
    exact sup_le_sup_right h p

/-- **The base of the cover is contractible.**  Everything that fails to span with `p` retracts onto
`p` by joining with it. -/
theorem isZero_homology_nerveCoverBase {p : L} (hp : IsAtom p) (hptop : p < ⊤)
    {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Preadditive C]
    [CategoryWithHomology C] (R : C) (i : ℕ) (hi : 1 ≤ i) :
    Limits.IsZero (((nerveCoverBase p : (nerve (properPart L)).Subcomplex) : SSet.{u}).homology R i) := by
  refine Limits.IsZero.of_iso ?_ (nerveSubcomplexHomologyIso _ R i)
  refine isZero_homology_of_conical
    (⟨⟨p, hp.1.bot_lt, hptop⟩, by
      show p ⊔ p ≠ ⊤
      rw [sup_idem]
      exact ne_of_lt hptop⟩ : (notSpanning p : Type u))
    (notSpanningJoinAtom p) (fun U => ?_) (fun U => ?_) R i hi
  · show U.1.1 ≤ U.1.1 ⊔ p
    exact le_sup_left
  · show p ≤ U.1.1 ⊔ p
    exact le_sup_right

/-- **The disjoint union of the pieces has no homology above degree zero.** -/
theorem isZero_homology_famSSet_coverPiece (p : L)
    {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C]
    (R : C) (i : ℕ) (hi : 1 ≤ i) :
    Limits.IsZero ((famSSet (coverPiece p)).homology R i) := by
  rw [coverPiece_eq]
  exact isZero_homology_famSSet_generalStar (fun a : spanningIndex p => (a : properPart L)) R i hi

variable [IsModularLattice L]

/-- **Two pieces meet only inside the base.** -/
theorem coverPiece_inter_le_nerveCoverBase {p : L} (hp : IsAtom p) (a b : spanningIndex p) (hab : a ≠ b) :
    coverPiece p a ⊓ coverPiece p b ≤ nerveCoverBase p := by
  rw [coverPiece, coverPiece, nerveCoverBase, ← nerveSubcomplex_inter]
  exact nerveSubcomplex_mono (star_inter_star_subset_notSpanning hp a.2 b.2
    (fun h => hab (Subtype.ext h)))

/-- **The base meets a piece exactly in the elements strictly below its centre.** -/
theorem nerveCoverBase_inter_coverPiece {p : L} (hp : IsAtom p) (a : spanningIndex p) :
    nerveCoverBase p ⊓ coverPiece p a
      = nerveSubcomplex {U : properPart L | U < (a : properPart L)} := by
  rw [nerveCoverBase, coverPiece, ← nerveSubcomplex_inter, notSpanning_inter_star hp a.2]

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- **The Solomon--Tits induction step.**  If the map out of the disjoint union of the order
complexes of the intervals below the spanning coatoms is injective on homology in degree `j`, the
whole order complex has no homology in degree `i`. -/
theorem isZero_homology_nerve_properPart {p : L} (hp : IsAtom p) (hptop : p < ⊤)
    [Nonempty (spanningIndex p)] (R : C) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j)
    (hi : 1 ≤ i)
    (hmono : Mono (HomologicalComplex.homologyMap
      (mvFamChainFst (nerve (properPart L)) R (nerveCoverBase p) (coverPiece p)) j)) :
    Limits.IsZero ((nerve (properPart L)).homology R i) := by
  have hzero := isZero_homology_famSup (nerve (properPart L)) R (nerveCoverBase p) (coverPiece p)
    (fun a b hab => coverPiece_inter_le_nerveCoverBase hp a b hab) i j hij
    (isZero_homology_nerveCoverBase hp hptop R i hi)
    (isZero_homology_famSSet_coverPiece p R i hi) hmono
  rw [show famSup (nerve (properPart L)) (nerveCoverBase p) (coverPiece p) = ⊤ from
    nerveCoverBase_sup_iSup_coverPiece p] at hzero
  exact Limits.IsZero.of_iso hzero
    ((SSet.homologyFunctor R i).mapIso (SSet.Subcomplex.topIso (nerve (properPart L))).symm)

end

end GaloisForLFunctions.HTGeometry
