import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Degree zero of a simplicial commutative ring preserves pushouts

The positive-cell theorem needs the connective pushout formula
`π₀(A' ⊗^L_A A'') ≅ π₀A' ⊗_{π₀A} π₀A''`.  Stated for `E_∞`-ring spectra it is higher algebra, but
the hypotheses it uses hold for simplicial commutative rings, and there `π₀` is the colimit over the
simplex category — which is a left adjoint, so the formula is a corollary of adjoint functor theory
rather than a theorem about `∞`-categories.

* `simplicialPiZero` : **`π₀` of a simplicial commutative ring.**
* `simplicialPiZeroAdj` : **it is left adjoint to the constant simplicial object.**
* `simplicialPiZero_preservesPushouts` : **hence it preserves pushouts.**
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory CategoryTheory.Limits

/-- **Degree zero of a simplicial commutative ring**, as the colimit over the simplex category. -/
noncomputable def simplicialPiZero : SimplicialObject CommRingCat ⥤ CommRingCat := colim

/-- **`π₀` is left adjoint to the constant simplicial object.** -/
noncomputable def simplicialPiZeroAdj :
    simplicialPiZero ⊣ Functor.const SimplexCategoryᵒᵖ :=
  colimConstAdj

/-- **`π₀` preserves all colimits**, being a left adjoint. -/
noncomputable instance simplicialPiZero_preservesColimits :
    PreservesColimitsOfSize.{0, 0} simplicialPiZero :=
  simplicialPiZeroAdj.leftAdjoint_preservesColimits

/-- **`π₀` preserves pushouts.**  This is the connective pushout formula of the positive-cell
theorem, in the simplicial model: the degree-zero ring of a homotopy pushout is the pushout of the
degree-zero rings. -/
noncomputable instance simplicialPiZero_preservesPushouts :
    PreservesColimitsOfShape WalkingSpan simplicialPiZero :=
  inferInstance

/-- **`π₀` of a homotopy pushout is the pushout of the `π₀`'s.**  This is the connective pushout
formula the positive-cell theorem runs on, stated as a pushout square. -/
theorem simplicialPiZero_map_isPushout {A B C D : SimplicialObject CommRingCat}
    {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {i : C ⟶ D} (H : IsPushout f g h i) :
    IsPushout (simplicialPiZero.map f) (simplicialPiZero.map g)
      (simplicialPiZero.map h) (simplicialPiZero.map i) :=
  Functor.map_isPushout (F := simplicialPiZero) H

/-- **In a pushout square, the leg opposite an isomorphism is an isomorphism.** -/
theorem isIso_of_isPushout_of_isIso {C : Type*} [Category C] {A B X D : C}
    {f : A ⟶ B} {g : A ⟶ X} {h : B ⟶ D} {i : X ⟶ D} (H : IsPushout f g h i) [IsIso g] :
    IsIso h := by
  refine ⟨H.desc (𝟙 B) (inv g ≫ f) (by simp), H.inl_desc _ _ _, ?_⟩
  refine H.hom_ext ?_ ?_
  · rw [← Category.assoc, H.inl_desc, Category.id_comp, Category.comp_id]
  · rw [← Category.assoc, H.inr_desc, Category.assoc, H.w, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp, Category.comp_id]

/-- **Attaching cells that do not change degree zero does not change degree zero.**  If the
augmentation of the attached algebra is a `π₀`-isomorphism, then so is the map from `A` into the
attachment.  This is the positive-cell theorem `(2)`, in the simplicial model, modulo the
connectivity input that makes the augmentation a `π₀`-isomorphism. -/
theorem simplicialPiZero_isIso_of_isPushout {A B C D : SimplicialObject CommRingCat}
    {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {i : C ⟶ D} (H : IsPushout f g h i)
    [IsIso (simplicialPiZero.map g)] : IsIso (simplicialPiZero.map h) :=
  isIso_of_isPushout_of_isIso (simplicialPiZero_map_isPushout H)

/-- **`π₀` of a free construction is again a free construction.**  If `Free` is left adjoint to a
forgetful functor into simplicial commutative rings, then `Free ⋙ π₀` is left adjoint to the
corresponding forgetful functor on constant objects — so it is determined by its values on the
input, and in particular is computed by `π₀` of the input.  This is the connectivity mechanism the
positive-cell theorem needs: a free algebra on an object with vanishing `π₀` has the unit for its
`π₀`. -/
noncomputable def freeCompPiZeroAdj {E : Type*} [Category E]
    {Free : E ⥤ SimplicialObject CommRingCat} {U : SimplicialObject CommRingCat ⥤ E}
    (adj : Free ⊣ U) :
    (Free ⋙ simplicialPiZero) ⊣ (Functor.const SimplexCategoryᵒᵖ ⋙ U) :=
  adj.comp simplicialPiZeroAdj

end GaloisForLFunctions.HTGeometry
