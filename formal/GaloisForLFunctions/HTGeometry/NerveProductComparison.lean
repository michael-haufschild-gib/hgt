import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
# Comparing the nerve of a product with the product of nerves

Simplicial sets are cartesian monoidal, so the tensor is the categorical product, and the two
projections of a product of categories give a canonical comparison map from the nerve of the product
to the tensor of the nerves.

This is the map whose inverse turns a functor out of `C × [1]` into a homotopy of simplicial sets,
which is what a deformation retraction of a poset amounts to.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

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

/-- **A functor out of a product induces a map out of the tensor of the nerves.**  This is the shape
a homotopy of simplicial sets takes: with `D` the interval, a functor `C × [1] ⥤ E` becomes a map
`nerve C ⊗ Δ[1] ⟶ nerve E`.

The comparison being an isomorphism is the only input, and it holds because the nerve preserves
limits and `Cat` has products. -/
noncomputable def nerveTensorMap (C D E : Type u) [SmallCategory C] [SmallCategory D]
    [SmallCategory E] [IsIso (nerveProductComparison C D)]
    (F : CategoryTheory.Functor (C × D) E) :
    nerveFunctor.obj (Cat.of C) ⊗ nerveFunctor.obj (Cat.of D) ⟶ nerveFunctor.obj (Cat.of E) :=
  inv (nerveProductComparison C D) ≫ nerveFunctor.map F.toCatHom

theorem nerveProductComparison_comp_nerveTensorMap (C D E : Type u) [SmallCategory C]
    [SmallCategory D] [SmallCategory E] [IsIso (nerveProductComparison C D)]
    (F : CategoryTheory.Functor (C × D) E) :
    nerveProductComparison C D ≫ nerveTensorMap C D E F = nerveFunctor.map F.toCatHom := by
  rw [nerveTensorMap, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

end GaloisForLFunctions.HTGeometry
