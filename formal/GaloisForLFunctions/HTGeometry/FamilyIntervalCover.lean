import GaloisForLFunctions.HTGeometry.IntervalSpanningCover
import GaloisForLFunctions.HTGeometry.FamilyPosetNerve

/-!
# The cover of a disjoint union of interval buildings

The Solomon--Tits induction produces, from one building, a whole family of smaller ones — the
intervals below the coatoms — so the statement it can be run on is one about a *family* of
intervals at once.  Their disjoint union is a poset, and the cover of each component assembles into
a cover of the disjoint union:

* the base collects, in each component, the elements that do not span that component's top with that
  component's atom;
* there is one piece for each component together with a coatom of it, and the piece is the star of
  that coatom **in the disjoint union**, so a disjoint union of pieces is a disjoint union of stars;
* two pieces meet only inside the base — in different components they do not meet at all;
* the base meets a piece exactly in the interval below its centre, again inside one component.

The last item is what makes the induction close: the intersections form a disjoint union of interval
buildings, one coatom step smaller, which is another instance of the same statement.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Simplicial Opposite

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L] {ι : Type u} (W p : ι → L)

/-- The disjoint union of the buildings of the intervals below a family of elements. -/
abbrev famBuilding : Type u := famPoset (fun a : ι => properBelow (W a))

/-- The index of the pieces: a component together with a coatom of it. -/
abbrev famCoverIndex : Type u :=
  {c : ι × properPart L // c.2 ∈ spanningBelow (W c.1) (p c.1)}

/-- The centre of a piece, as an element of the disjoint union. -/
abbrev famCoverCentre (c : famCoverIndex W p) : famBuilding W :=
  ⟨((Subtype.val c).1, (Subtype.val c).2), c.2.1⟩

/-- The base of the cover: componentwise, the elements that do not span. -/
def famCoverBase : Set (famBuilding W) :=
  {q | (Subtype.val q).2 ∈ notSpanningBelow (W (Subtype.val q).1) (p (Subtype.val q).1)}

variable {W p}

theorem mem_famCoverBase {q : famBuilding W} :
    q ∈ famCoverBase W p ↔
      (Subtype.val q).2 ∈ notSpanningBelow (W (Subtype.val q).1) (p (Subtype.val q).1) := Iff.rfl

theorem mem_generalStar_famCoverCentre {c : famCoverIndex W p} {q : famBuilding W} :
    q ∈ generalStar (famCoverCentre W p c) ↔
      (Subtype.val q).1 = (Subtype.val c).1
        ∧ (Subtype.val q).2 ∈ generalStar (Subtype.val c).2 := by
  constructor
  · rintro (h | h)
    · exact ⟨(famPoset_le_iff.1 h).1, Or.inl (famPoset_le_iff.1 h).2⟩
    · exact ⟨(famPoset_le_iff.1 h).1.symm, Or.inr (famPoset_le_iff.1 h).2⟩
  · rintro ⟨hidx, hle | hle⟩
    · exact Or.inl (famPoset_le_iff.2 ⟨hidx, hle⟩)
    · exact Or.inr (famPoset_le_iff.2 ⟨hidx.symm, hle⟩)

/-- **Every chain of the disjoint union lies in the base or in a single piece.** -/
theorem famChain_mem_base_or_star (n : SimplexCategoryᵒᵖ)
    (x : (nerve (famBuilding W)).obj n) :
    (∀ i, x.obj i ∈ famCoverBase W p) ∨
      ∃ c : famCoverIndex W p, ∀ i, x.obj i ∈ generalStar (famCoverCentre W p c) := by
  by_cases hsp : ∃ i, (Subtype.val (x.obj i)).2
      ∈ spanningBelow (W (Subtype.val (x.obj i)).1) (p (Subtype.val (x.obj i)).1)
  · obtain ⟨i, hi⟩ := hsp
    refine Or.inr ⟨⟨((Subtype.val (x.obj i)).1, (Subtype.val (x.obj i)).2), hi⟩, fun j => ?_⟩
    rcases le_total i j with hij | hij
    · exact Or.inr (leOfHom (x.map (homOfLE hij)))
    · exact Or.inl (leOfHom (x.map (homOfLE hij)))
  · exact Or.inl (fun i => ⟨(x.obj i).2, fun hcon => hsp ⟨i, ⟨(x.obj i).2, hcon⟩⟩⟩)

variable [IsModularLattice L]

/-- **Two pieces meet only inside the base.**  In different components they do not meet at all. -/
theorem famCoverPiece_inter_subset_base (hp : ∀ a, IsAtom (p a)) {c c' : famCoverIndex W p}
    (hne : c ≠ c') :
    generalStar (famCoverCentre W p c) ∩ generalStar (famCoverCentre W p c')
      ⊆ famCoverBase W p := by
  rintro q ⟨hq, hq'⟩
  obtain ⟨hidx, hstar⟩ := mem_generalStar_famCoverCentre.1 hq
  obtain ⟨hidx', hstar'⟩ := mem_generalStar_famCoverCentre.1 hq'
  have hcc : (Subtype.val c).1 = (Subtype.val c').1 := hidx ▸ hidx'
  have hc'2 : (Subtype.val c').2 ∈ spanningBelow (W (Subtype.val c).1) (p (Subtype.val c).1) := by
    rw [hcc]
    exact c'.2
  have hUne : (Subtype.val c).2 ≠ (Subtype.val c').2 := by
    intro hUU
    exact hne (Subtype.ext (Prod.ext hcc hUU))
  refine mem_famCoverBase.2 ?_
  rw [hidx]
  refine starBelow_inter_starBelow (hp (Subtype.val c).1) c.2 hc'2 hUne ⟨?_, hstar, hstar'⟩
  rw [← hidx]
  exact q.2

/-- **The base meets a piece exactly in the interval below its centre.** -/
theorem famCoverBase_inter_piece (hp : ∀ a, IsAtom (p a)) (c : famCoverIndex W p) :
    famCoverBase W p ∩ generalStar (famCoverCentre W p c)
      = {q : famBuilding W | (Subtype.val q).1 = (Subtype.val c).1
          ∧ (Subtype.val q).2 ∈ properBelow ((Subtype.val c).2 : L)} := by
  ext q
  constructor
  · rintro ⟨hbase, hstar⟩
    obtain ⟨hidx, hcomp⟩ := mem_generalStar_famCoverCentre.1 hstar
    refine ⟨hidx, ?_⟩
    rw [← notSpanningBelow_inter_star (hp (Subtype.val c).1) c.2]
    refine ⟨?_, hcomp⟩
    have hb := mem_famCoverBase.1 hbase
    rwa [hidx] at hb
  · rintro ⟨hidx, hbelow⟩
    have hmem : (Subtype.val q).2 ∈ notSpanningBelow (W (Subtype.val c).1) (p (Subtype.val c).1)
        ∩ generalStar (Subtype.val c).2 := by
      rw [notSpanningBelow_inter_star (hp (Subtype.val c).1) c.2]
      exact hbelow
    refine ⟨mem_famCoverBase.2 ?_, mem_generalStar_famCoverCentre.2 ⟨hidx, hmem.2⟩⟩
    rw [hidx]
    exact hmem.1

end GaloisForLFunctions.HTGeometry
