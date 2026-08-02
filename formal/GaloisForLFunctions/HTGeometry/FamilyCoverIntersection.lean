import GaloisForLFunctions.HTGeometry.FamilyIntervalCover

/-!
# The intersections of the family cover are again a family of interval buildings

The base meets each piece in the interval below that piece's centre, inside that piece's component.
So the disjoint union of the intersections, over all pieces, is the disjoint union of the buildings
of the intervals below the coatoms — an instance of the same kind of object the cover was applied to,
one coatom step smaller.

That order isomorphism is what closes the Solomon--Tits induction: the Mayer--Vietoris term the
sequence produces is the next instance of the statement being proved.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Simplicial Opposite

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L] {ι : Type u} {W p : ι → L}

/-- The tops of the smaller buildings: the coatoms indexing the pieces. -/
abbrev famCoverTop (c : famCoverIndex W p) : L := ((Subtype.val c).2 : L)

theorem famCoverTop_lt (c : famCoverIndex W p) : famCoverTop c < W (Subtype.val c).1 := c.2.1

variable [IsModularLattice L]

theorem mem_famCoverInter (hp : ∀ a, IsAtom (p a)) {c : famCoverIndex W p} {q : famBuilding W} :
    q ∈ famCoverBase W p ∩ generalStar (famCoverCentre W p c) ↔
      (Subtype.val q).1 = (Subtype.val c).1
        ∧ (Subtype.val q).2 ∈ properBelow (famCoverTop c) :=
  Set.ext_iff.1 (famCoverBase_inter_piece hp c) q

/-- **The disjoint union of the intersections is the disjoint union of the interval buildings below
the coatoms.** -/
def famCoverInterOrderIso (hp : ∀ a, IsAtom (p a)) :
    famPoset (fun c : famCoverIndex W p =>
        famCoverBase W p ∩ generalStar (famCoverCentre W p c))
      ≃o famBuilding (fun c : famCoverIndex W p => famCoverTop c) where
  toFun r :=
    ⟨((Subtype.val r).1, (Subtype.val (Subtype.val r).2).2), by
      have h : (Subtype.val r).2 ∈ famCoverBase W p
          ∩ generalStar (famCoverCentre W p (Subtype.val r).1) := r.2
      exact ((mem_famCoverInter hp).1 h).2⟩
  invFun r :=
    ⟨((Subtype.val r).1,
      ⟨((Subtype.val (Subtype.val r).1).1, (Subtype.val r).2),
        lt_trans r.2 (famCoverTop_lt (Subtype.val r).1)⟩), by
      show (⟨((Subtype.val (Subtype.val r).1).1, (Subtype.val r).2),
          lt_trans r.2 (famCoverTop_lt (Subtype.val r).1)⟩ : famBuilding W)
        ∈ famCoverBase W p ∩ generalStar (famCoverCentre W p (Subtype.val r).1)
      exact (mem_famCoverInter hp).2 ⟨rfl, r.2⟩⟩
  left_inv r := by
    have h : (Subtype.val r).2 ∈ famCoverBase W p
        ∩ generalStar (famCoverCentre W p (Subtype.val r).1) := r.2
    refine Subtype.ext (Prod.ext rfl ?_)
    exact Subtype.ext (Prod.ext ((mem_famCoverInter hp).1 h).1.symm rfl)
  right_inv _ := rfl
  map_rel_iff' {r r'} := by
    have h : (Subtype.val r).2 ∈ famCoverBase W p
        ∩ generalStar (famCoverCentre W p (Subtype.val r).1) := r.2
    have h' : (Subtype.val r').2 ∈ famCoverBase W p
        ∩ generalStar (famCoverCentre W p (Subtype.val r').1) := r'.2
    constructor
    · rintro ⟨hc, hle⟩
      have hc' : (Subtype.val r).1 = (Subtype.val r').1 := hc
      have hle' : (Subtype.val (Subtype.val r).2).2 ≤ (Subtype.val (Subtype.val r').2).2 := hle
      refine famPoset_le_iff.2 ⟨hc', famPoset_le_iff.2 ⟨?_, hle'⟩⟩
      rw [((mem_famCoverInter hp).1 h).1, ((mem_famCoverInter hp).1 h').1, hc']
    · rintro ⟨hc, hle⟩
      exact ⟨hc, (famPoset_le_iff.1 hle).2⟩

/-- **And therefore the same order complex.** -/
noncomputable def famCoverInterNerveIso (hp : ∀ a, IsAtom (p a)) :
    nerveFunctor.obj (Cat.of (famPoset (fun c : famCoverIndex W p =>
        famCoverBase W p ∩ generalStar (famCoverCentre W p c))))
      ≅ nerveFunctor.obj (Cat.of (famBuilding (fun c : famCoverIndex W p => famCoverTop c))) :=
  orderIsoNerveIso (famCoverInterOrderIso hp)

end GaloisForLFunctions.HTGeometry
