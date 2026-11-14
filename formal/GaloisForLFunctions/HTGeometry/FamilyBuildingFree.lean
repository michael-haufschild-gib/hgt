import GaloisForLFunctions.HTGeometry.FamilyCoverBaseComponents
import GaloisForLFunctions.HTGeometry.FamilyTopHomologyEmbedding
import GaloisForLFunctions.HTGeometry.FamilyBuildingVanishing

/-!
# The homology of a family of buildings is free

The cover of a disjoint union of interval buildings has a locally conical base and stars for pieces,
so above degree zero the Mayer--Vietoris sequence relates its homology in degree `i` to the homology
of the disjoint union one coatom step down in degree `i - 1`, and the relation is an isomorphism as
soon as both degrees are positive.  At the bottom, degree one, the sequence identifies the homology
with the kernel of the degree-zero map from the intersections into the pieces, and that kernel is a
coproduct of copies of the coefficients: the component of an intersection inside the base is the atom
of its own component, so it is already determined by the piece containing it.

The conclusion needs no rank hypothesis at all: in every positive degree the homology of a disjoint
union of interval buildings of a modular lattice with atoms below every nonzero element is free.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u c

section

variable {C : Type c} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- A zero object is free: it is the coproduct over the empty index. -/
theorem IsFreeOver.of_isZero {R Z : C} (h : Limits.IsZero Z) : IsFreeOver.{v, c, u} R Z := by
  refine ⟨PEmpty.{u + 1}, ⟨h.iso ?_⟩⟩
  rw [Limits.IsZero.iff_id_eq_zero]
  exact Sigma.hom_ext _ _ fun i => i.elim

end

section

variable {L : Type u} [Lattice L] [BoundedOrder L] [IsModularLattice L] {ι : Type u} {W p : ι → L}
variable {C : Type c} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- The component of the base attached to a component of the pieces: the atom of that component. -/
noncomputable def famCoverBaseComponent (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a) :
    SSet.π₀ (famSSet (famCoverPieceSub (W := W) (p := p)))
      → SSet.π₀ ((famCoverBaseSub (W := W) (p := p) :
          (nerve (famBuilding W)).Subcomplex) : SSet.{u}) :=
  famSSetPi0Lift fun c =>
    SSet.π₀.mk (nerveSubcomplexVertex (famCoverAtomElt hp hpW c)
      (famCoverAtomElt_mem_base hp hpW c))

omit [IsModularLattice L] in
/-- **The component of an intersection inside the base is determined by its piece.** -/
theorem famCoverBaseComponent_apply (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a)
    (x : (famSSet fun c : famCoverIndex W p =>
      (famCoverBaseSub (W := W) (p := p)) ⊓ famCoverPieceSub c) _⦋0⦌) :
    famCoverBaseComponent hp hpW
        (SSet.π₀.mk ((famInterPieceHom (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
          (famCoverPieceSub (W := W) (p := p))).app _ x))
      = SSet.π₀.mk ((famInterBaseHom (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
          (famCoverPieceSub (W := W) (p := p))).app _ x) := by
  have hq : ((x.2 : (nerve (famBuilding W)) _⦋0⦌)).obj 0 ∈ famCoverBase W p := x.2.2.1 0
  have hstar : ((x.2 : (nerve (famBuilding W)) _⦋0⦌)).obj 0
      ∈ generalStar (famCoverCentre W p x.1) := x.2.2.2 0
  have hidx : (Subtype.val (((x.2 : (nerve (famBuilding W)) _⦋0⦌)).obj 0)).1
      = (Subtype.val x.1).1 := (mem_generalStar_famCoverCentre.1 hstar).1
  refine Eq.trans ?_ (congrArg SSet.π₀.mk (nerveSubcomplexVertex_eq _)).symm
  exact (pi0_base_eq_atom hp hpW x.1 hq hidx).symm

/-- **The first homology of a disjoint union of interval buildings is free.** -/
theorem isFreeOver_homology_famBuilding_one (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a)
    [Nonempty (famCoverIndex W p)] (R : C) :
    IsFreeOver.{v, c, u} R ((nerve (famBuilding W)).homology R 1) := by
  refine IsFreeOver.of_iso ?_ (famSupHomologyIso (W := W) (p := p) R 1)
  exact isFreeOver_homology_famSup_one (nerve (famBuilding W)) R
    (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p))
    (fun c c' hcc => famCoverPieceSub_inter_le hp c c' hcc)
    (isZero_homology_famCoverBase hp hpW R 1 le_rfl)
    (isZero_homology_famSSet_generalStar (famCoverCentre W p) R 1 le_rfl)
    (famCoverBaseComponent hp hpW) (famCoverBaseComponent_apply hp hpW)

/-- **The homology of a disjoint union of interval buildings is free in every positive degree.**
The descent replaces the family by the family of intervals below the coatoms and drops the degree by
one; at the bottom the Mayer--Vietoris kernel is a coproduct of copies of the coefficients. -/
theorem isFreeOver_homology_famBuilding
    (hatomic : ∀ V : L, ⊥ < V → ∃ q, IsAtom q ∧ q ≤ V) (R : C) :
    ∀ (i : ℕ), 1 ≤ i → ∀ (ι : Type u) (W : ι → L), (∀ a, ⊥ < W a) →
      IsFreeOver.{v, c, u} R ((nerve (famBuilding W)).homology R i) := by
  classical
  intro i
  induction i with
  | zero => intro h; exact absurd h (by omega)
  | succ n ih =>
      intro _ ι W hbot
      choose p hp hpW using fun a => hatomic (W a) (hbot a)
      rcases isEmpty_or_nonempty (famCoverIndex W p) with hem | hne
      · exact IsFreeOver.of_isZero
          (isZero_homology_famBuilding_of_isEmpty hp hpW R (n + 1) (by omega))
      · rcases Nat.eq_zero_or_pos n with rfl | hn
        · exact isFreeOver_homology_famBuilding_one hp hpW R
        · haveI := isIso_famTopEmbedding (W := W) (p := p) hp hpW R (n + 1) n rfl (by omega)
            (by omega)
          refine IsFreeOver.of_iso ?_ (asIso (famTopEmbedding (W := W) (p := p) hp R
            (n + 1) n rfl))
          exact ih (by omega) _ (fun c : famCoverIndex W p => famCoverTop c)
            (fun c => (Subtype.val c).2.2.1)

/-- **The homology of the order complex of the proper part of a modular lattice is free in every
positive degree.** -/
theorem isFreeOver_homology_properPart
    (hatomic : ∀ V : L, ⊥ < V → ∃ q, IsAtom q ∧ q ≤ V) (R : C) (i : ℕ) (hi : 1 ≤ i)
    (hbot : (⊥ : L) < ⊤) :
    IsFreeOver.{v, c, u} R ((nerve (properPart L)).homology R i) := by
  have h := isFreeOver_homology_famBuilding hatomic R i hi PUnit.{u + 1} (fun _ => (⊤ : L))
    (fun _ => hbot)
  exact IsFreeOver.of_iso h
    ((SSet.homologyFunctor R i).mapIso (orderIsoNerveIso (famBuildingPUnitOrderIso (L := L))).symm)

end

end GaloisForLFunctions.HTGeometry
