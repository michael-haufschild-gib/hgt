import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Comparing the nerve of a product with the product of nerves

Simplicial sets are cartesian monoidal, so the tensor is the categorical product, and the two
projections of a product of categories give a canonical comparison map from the nerve of the product
to the tensor of the nerves.

This is the map whose inverse turns a functor out of `C × [1]` into a homotopy of simplicial sets,
which is what a deformation retraction of a poset amounts to.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe u

/-- **The comparison map.**  The nerve of a product maps to the tensor of the nerves, by the two
projections. -/
noncomputable def nerveProductComparison (C D : Type u) [SmallCategory C] [SmallCategory D] :
    nerveFunctor.obj (Cat.of (C × D)) ⟶
      nerveFunctor.obj (Cat.of C) ⊗ nerveFunctor.obj (Cat.of D) :=
  lift (nerveFunctor.map (CategoryTheory.Prod.fst C D).toCatHom)
    (nerveFunctor.map (CategoryTheory.Prod.snd C D).toCatHom)

/-- Its first component is the nerve of the first projection. -/
theorem nerveProductComparison_fst (C D : Type u) [SmallCategory C] [SmallCategory D] :
    nerveProductComparison C D ≫ fst _ _
      = nerveFunctor.map (CategoryTheory.Prod.fst C D).toCatHom := by
  simp [nerveProductComparison]

/-- Its second component is the nerve of the second projection. -/
theorem nerveProductComparison_snd (C D : Type u) [SmallCategory C] [SmallCategory D] :
    nerveProductComparison C D ≫ snd _ _
      = nerveFunctor.map (CategoryTheory.Prod.snd C D).toCatHom := by
  simp [nerveProductComparison]

/-- **The nerve preserves limits**, being a right adjoint.  So the comparison map above is an
isomorphism, which is what turns a functor out of a product into a map out of a tensor. -/
noncomputable instance : Limits.PreservesLimits nerveFunctor.{u, u} :=
  nerveAdjunction.rightAdjoint_preservesLimits

/-- **A product of categories is a binary product in `Cat`.**  A functor into a product is the pair
of its components, and it is determined by them. -/
noncomputable def catProdIsLimit (C D : Type u) [SmallCategory C] [SmallCategory D] :
    IsLimit (BinaryFan.mk (P := Cat.of (C × D)) (CategoryTheory.Prod.fst C D).toCatHom
      (CategoryTheory.Prod.snd C D).toCatHom) :=
  BinaryFan.IsLimit.mk _
    (fun {_} f g => (f.toFunctor.prod' g.toFunctor).toCatHom)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ h1 h2 => by subst h1; subst h2; rfl)

/-- **The nerve carries it to a binary product of simplicial sets**, the nerve being a right
adjoint. -/
noncomputable def nerveProdIsLimit (C D : Type u) [SmallCategory C] [SmallCategory D] :
    IsLimit (BinaryFan.mk (nerveFunctor.map (CategoryTheory.Prod.fst C D).toCatHom)
      (nerveFunctor.map (CategoryTheory.Prod.snd C D).toCatHom)) :=
  mapIsLimitOfPreservesOfIsLimit nerveFunctor _ _ (catProdIsLimit C D)

/-- **The comparison map is an isomorphism.**  Both its source and its target are binary products
of the same two nerves, and it commutes with the projections. -/
instance isIso_nerveProductComparison (C D : Type u) [SmallCategory C] [SmallCategory D] :
    IsIso (nerveProductComparison C D) := by
  have h : nerveProductComparison C D
      = (IsLimit.conePointUniqueUpToIso (nerveProdIsLimit C D)
          (tensorProductIsBinaryProduct (nerveFunctor.obj (Cat.of C))
            (nerveFunctor.obj (Cat.of D)))).hom := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [nerveProductComparison_fst]
      have h1 := IsLimit.conePointUniqueUpToIso_hom_comp (nerveProdIsLimit C D)
        (tensorProductIsBinaryProduct (nerveFunctor.obj (Cat.of C))
          (nerveFunctor.obj (Cat.of D))) ⟨WalkingPair.left⟩
      simp only [BinaryFan.π_app_left, BinaryFan.mk_fst] at h1
      exact h1.symm
    · rw [nerveProductComparison_snd]
      have h2 := IsLimit.conePointUniqueUpToIso_hom_comp (nerveProdIsLimit C D)
        (tensorProductIsBinaryProduct (nerveFunctor.obj (Cat.of C))
          (nerveFunctor.obj (Cat.of D))) ⟨WalkingPair.right⟩
      simp only [BinaryFan.π_app_right, BinaryFan.mk_snd] at h2
      exact h2.symm
  rw [h]
  infer_instance

/-- **A functor out of a product induces a map out of the tensor of the nerves.**  This is the shape
a homotopy of simplicial sets takes: with `D` the interval, a functor `C × [1] ⥤ E` becomes a map
`nerve C ⊗ Δ[1] ⟶ nerve E`.

The comparison being an isomorphism is the only input, and it holds because the nerve preserves
limits and `Cat` has products. -/
noncomputable def nerveTensorMap (C D E : Type u) [SmallCategory C] [SmallCategory D]
    [SmallCategory E] (F : CategoryTheory.Functor (C × D) E) :
    nerveFunctor.obj (Cat.of C) ⊗ nerveFunctor.obj (Cat.of D) ⟶ nerveFunctor.obj (Cat.of E) :=
  inv (nerveProductComparison C D) ≫ nerveFunctor.map F.toCatHom

theorem nerveProductComparison_comp_nerveTensorMap (C D E : Type u) [SmallCategory C]
    [SmallCategory D] [SmallCategory E] (F : CategoryTheory.Functor (C × D) E) :
    nerveProductComparison C D ≫ nerveTensorMap C D E F = nerveFunctor.map F.toCatHom := by
  rw [nerveTensorMap, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

end GaloisForLFunctions.HTGeometry
