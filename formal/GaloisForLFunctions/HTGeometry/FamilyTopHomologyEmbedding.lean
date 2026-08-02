import GaloisForLFunctions.HTGeometry.FamilyBuildingStep

/-!
# The homology of a family of buildings embeds into the next rank down

Above degree zero the base of the cover and the disjoint union of its pieces have no homology at
all, so the Mayer--Vietoris sequence makes the connecting map injective: the homology of the
disjoint union of interval buildings in degree `i` embeds into the homology, in degree `i - 1`, of
the disjoint union of the interval buildings below the coatoms.

Below the top degree this says nothing new — both sides vanish.  In the top degree it is the only
structure the sequence gives, and it is the inductive skeleton of the rank of the Steinberg module:
the top homology of a building of rank `r` embeds into the top homology of the disjoint union of the
buildings of rank `r - 1` indexed by the coatoms.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u

variable {L : Type u} [Lattice L] [BoundedOrder L] [IsModularLattice L] {ι : Type u} {W p : ι → L}

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- The homology of the union of the cover is the homology of the whole order complex. -/
noncomputable def famSupHomologyIso (R : C) (i : ℕ) :
    (nerve (famBuilding W)).homology R i
      ≅ (((famSup (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
        (famCoverPieceSub (W := W) (p := p)) : (nerve (famBuilding W)).Subcomplex) :
        SSet.{u}).chainComplex R).homology i :=
  (SSet.homologyFunctor R i).mapIso (SSet.Subcomplex.topIso (nerve (famBuilding W))).symm
    ≪≫ eqToIso (by
      have htop : famSup (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
          (famCoverPieceSub (W := W) (p := p)) = ⊤ := famCoverBaseSub_sup_iSup
      rw [htop]
      rfl)

/-- **The connecting map of the cover**, read as a map from the homology of the order complex to the
homology of the disjoint union of the buildings below the coatoms. -/
noncomputable def famTopEmbedding (hp : ∀ a, IsAtom (p a)) [Nonempty (famCoverIndex W p)]
    (R : C) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (nerve (famBuilding W)).homology R i
      ⟶ (nerve (famBuilding (fun c : famCoverIndex W p => famCoverTop c))).homology R j :=
  (famSupHomologyIso R i).hom
    ≫ (mvFamChainShortExact (nerve (famBuilding W)) R (famCoverBaseSub (W := W) (p := p))
        (famCoverPieceSub (W := W) (p := p))
        (fun a b hab => famCoverPieceSub_inter_le hp a b hab)).δ i j hij
    ≫ (famCoverInterHomologyIso hp R j).hom

/-- **The embedding is injective.**  Everything in the middle of the Mayer--Vietoris sequence
vanishes above degree zero, so the connecting map is a monomorphism. -/
theorem mono_famTopEmbedding (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a)
    [Nonempty (famCoverIndex W p)] (R : C) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j)
    (hi : 1 ≤ i) : Mono (famTopEmbedding (W := W) (p := p) hp R i j hij) := by
  have hmid : Limits.IsZero
      ((((famCoverBaseSub (W := W) (p := p) : (nerve (famBuilding W)).Subcomplex) :
        SSet.{u}).chainComplex R
      ⊞ (famSSet (famCoverPieceSub (W := W) (p := p))).chainComplex R).homology i) :=
    isZero_homology_biprod _ _ i (isZero_homology_famCoverBase hp hpW R i hi)
      (isZero_homology_famSSet_generalStar (famCoverCentre W p) R i hi)
  rw [famTopEmbedding]
  refine @mono_comp _ _ _ _ _ _ inferInstance _
    (@mono_comp _ _ _ _ _ _ ?_ _ inferInstance)
  exact ((mvFamChainShortExact (nerve (famBuilding W)) R (famCoverBaseSub (W := W) (p := p))
    (famCoverPieceSub (W := W) (p := p))
    (fun a b hab => famCoverPieceSub_inter_le hp a b hab)).homology_exact₃ i j hij).mono_g
    (hmid.eq_zero_of_src _)

/-- **In the top degree the embedding is an isomorphism.**  Both ends of the Mayer--Vietoris
sequence around the connecting map vanish above degree zero, so it is injective and surjective: the
homology of a family of buildings in degree `i` *is* the homology of the family below the coatoms in
degree `i - 1`, as soon as both degrees are positive. -/
theorem isIso_famTopEmbedding (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a)
    [Nonempty (famCoverIndex W p)] (R : C) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j)
    (hi : 1 ≤ i) (hj : 1 ≤ j) :
    IsIso (famTopEmbedding (W := W) (p := p) hp R i j hij) := by
  haveI := mono_famTopEmbedding hp hpW R i j hij hi
  have hmidj : Limits.IsZero
      ((((famCoverBaseSub (W := W) (p := p) : (nerve (famBuilding W)).Subcomplex) :
          SSet.{u}).chainComplex R
        ⊞ (famSSet (famCoverPieceSub (W := W) (p := p))).chainComplex R).homology j) :=
    isZero_homology_biprod _ _ j (isZero_homology_famCoverBase hp hpW R j hj)
      (isZero_homology_famSSet_generalStar (famCoverCentre W p) R j hj)
  haveI hepi : Epi (famTopEmbedding (W := W) (p := p) hp R i j hij) := by
    rw [famTopEmbedding]
    refine @epi_comp _ _ _ _ _ _ inferInstance _ (@epi_comp _ _ _ _ _ _ ?_ _ inferInstance)
    exact ((mvFamChainShortExact (nerve (famBuilding W)) R (famCoverBaseSub (W := W) (p := p))
      (famCoverPieceSub (W := W) (p := p))
      (fun a b hab => famCoverPieceSub_inter_le hp a b hab)).homology_exact₁ i j hij).epi_f
      (hmidj.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

end

end GaloisForLFunctions.HTGeometry
