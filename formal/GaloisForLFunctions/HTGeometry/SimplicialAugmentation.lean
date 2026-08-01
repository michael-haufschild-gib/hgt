import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero

/-!
# The augmentation of simplicial homology is natural

Degree-zero homology carries an augmentation to the coefficients, which is an isomorphism for a
connected simplicial set.  It is natural in the simplicial set, and homology in degree zero is
determined by the classes of the vertices, which is what makes the augmentation usable: a map between
connected simplicial sets induces an isomorphism on degree-zero homology.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [CategoryWithHomology C]

variable {X Y : SSet.{w}} (R : C)

/-- The homology class of a vertex. -/
noncomputable def zeroCycle (X : SSet.{w}) (R : C) (x : X _⦋0⦌) : R ⟶ X.homology R 0 :=
  (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
    (X.chainComplex R).homologyπ 0

theorem zeroCycle_comp_homology₀ε (x : X _⦋0⦌) :
    zeroCycle X R x ≫ X.homology₀ε R = 𝟙 R := by
  rw [zeroCycle, Category.assoc]
  exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε X R x

theorem zeroCycle_comp_homology₀Iso (x : X _⦋0⦌) :
    zeroCycle X R x ≫ (X.homology₀Iso R).hom
      = Sigma.ι (fun _ : SSet.π₀ X => R) (SSet.π₀.mk x) := by
  rw [zeroCycle, Category.assoc]
  exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom X R x

/-- **Degree-zero homology is determined by the classes of the vertices.** -/
theorem homology₀_hom_ext {T : C} {f g : X.homology R 0 ⟶ T}
    (h : ∀ x : X _⦋0⦌, zeroCycle X R x ≫ f = zeroCycle X R x ≫ g) : f = g := by
  rw [← cancel_epi (X.homology₀Iso R).inv]
  refine Sigma.hom_ext _ _ (fun c => ?_)
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective c
  have key : Sigma.ι (fun _ : SSet.π₀ X => R) (SSet.π₀.mk x) ≫ (X.homology₀Iso R).inv
      = zeroCycle X R x := by
    rw [← zeroCycle_comp_homology₀Iso R x, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, key, ← Category.assoc, key]
  exact h x

/-- **The class of a vertex is natural.** -/
theorem zeroCycle_comp_homologyMap (f : X ⟶ Y) (x : X _⦋0⦌) :
    zeroCycle X R x ≫ SSet.homologyMap f R 0 = zeroCycle Y R (f.app _ x) := by
  have hcyc : (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
      HomologicalComplex.cyclesMap (SSet.chainComplexMap f R) 0
      = (Y.chainComplex R).liftCycles (Y.ιChainComplex (f.app _ x)) 0 (by simp) (by simp) := by
    rw [← cancel_mono ((Y.chainComplex R).iCycles 0), Category.assoc,
      HomologicalComplex.cyclesMap_i, ← Category.assoc, HomologicalComplex.liftCycles_i,
      HomologicalComplex.liftCycles_i, SSet.ι_chainComplexMap_f]
  rw [zeroCycle, Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc, hcyc,
    zeroCycle]

/-- **The augmentation is natural.** -/
theorem homologyMap_comp_homology₀ε (f : X ⟶ Y) :
    SSet.homologyMap f R 0 ≫ Y.homology₀ε R = X.homology₀ε R := by
  refine homology₀_hom_ext R (fun x => ?_)
  rw [← Category.assoc, zeroCycle_comp_homologyMap, zeroCycle_comp_homology₀ε,
    zeroCycle_comp_homology₀ε]

/-- **A map between connected simplicial sets is an isomorphism on degree-zero homology.**  Both
augmentations are isomorphisms and the square commutes. -/
theorem isIso_homologyMap_zero (f : X ⟶ Y) [X.IsConnected] [Y.IsConnected] :
    IsIso (SSet.homologyMap f R 0) := by
  have h := homologyMap_comp_homology₀ε R f
  have : SSet.homologyMap f R 0 = X.homology₀ε R ≫ inv (Y.homology₀ε R) := by
    rw [← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [this]
  infer_instance

/-- **And in particular a monomorphism**, which is what a Mayer--Vietoris vanishing argument
consumes in degree zero. -/
theorem mono_homologyMap_zero (f : X ⟶ Y) [X.IsConnected] [Y.IsConnected] :
    Mono (SSet.homologyMap f R 0) := by
  haveI := isIso_homologyMap_zero R f
  infer_instance

end GaloisForLFunctions.HTGeometry
