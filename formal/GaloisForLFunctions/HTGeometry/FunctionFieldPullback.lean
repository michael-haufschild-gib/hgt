import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Pullback on function fields

Mathlib defines the function field of an integral scheme as the stalk at its generic point.  This
file supplies the missing contravariant map: a dominant morphism sends generic point to generic
point and therefore induces an injective homomorphism of function fields.
-/

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- A dominant morphism between irreducible schemes sends generic point to generic point. -/
theorem Scheme.Hom.map_genericPoint_of_isDominant
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  have h : IsGenericPoint (f (genericPoint X)) (Set.univ : Set Y) := by
    simpa only [Set.image_univ, f.denseRange.closure_range] using
      (genericPoint_spec X).image f.continuous
  exact h.eq (genericPoint_spec Y)

/-- The image of the source generic point specializes to the target generic point.  Packaging this
specialization avoids equality transports in the functorial pullback construction. -/
theorem Scheme.Hom.dominantGenericSpecializes
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) ⤳ genericPoint Y := by
  rw [f.map_genericPoint_of_isDominant]

/-- Pullback of rational functions along a dominant morphism, realized by specialization to its
image generic point followed by the stalk map. -/
noncomputable def Scheme.Hom.functionFieldPullback
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) [IsDominant f] :
    Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes f.dominantGenericSpecializes ≫
    f.stalkMap (genericPoint X)

/-- Dominant pullback is injective on function fields. -/
theorem Scheme.Hom.functionFieldPullback_injective
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] :
    Function.Injective f.functionFieldPullback :=
  RingHom.injective f.functionFieldPullback.hom

/-- Pullback depends only on the underlying dominant morphism. -/
theorem Scheme.Hom.functionFieldPullback_congr
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f g : X ⟶ Y) [IsDominant f] [IsDominant g] (h : f = g) :
    f.functionFieldPullback = g.functionFieldPullback := by
  subst g
  rfl

/-- Function-field pullback is contravariantly functorial. -/
theorem Scheme.Hom.functionFieldPullback_comp
    {X Y Z : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y] [IrreducibleSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f] [IsDominant g] :
    (f ≫ g).functionFieldPullback =
      g.functionFieldPullback ≫ f.functionFieldPullback := by
  rw [Scheme.Hom.functionFieldPullback, Scheme.Hom.functionFieldPullback,
    Scheme.Hom.functionFieldPullback, Scheme.Hom.stalkMap_comp]
  simp only [Category.assoc]
  rw [← g.stalkSpecializes_stalkMap_assoc
    (f (genericPoint X)) (genericPoint Y) f.dominantGenericSpecializes]
  rw [TopCat.Presheaf.stalkSpecializes_comp_assoc]
  rfl

/-- The identity morphism pulls every rational function back to itself. -/
@[simp]
theorem Scheme.Hom.functionFieldPullback_id
    (X : Scheme.{u}) [IrreducibleSpace X] :
    (𝟙 X : X ⟶ X).functionFieldPullback = 𝟙 X.functionField := by
  rw [Scheme.Hom.functionFieldPullback, Scheme.Hom.stalkMap_id]
  simp

/-- Categorical iteration of a scheme endomorphism. -/
def Scheme.Hom.categoricalIterate {X : Scheme.{u}} (f : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => f.categoricalIterate n ≫ f

@[simp]
theorem Scheme.Hom.categoricalIterate_zero {X : Scheme.{u}} (f : X ⟶ X) :
    f.categoricalIterate 0 = 𝟙 X :=
  rfl

@[simp]
theorem Scheme.Hom.categoricalIterate_succ {X : Scheme.{u}} (f : X ⟶ X) (n : ℕ) :
    f.categoricalIterate (n + 1) = f.categoricalIterate n ≫ f :=
  rfl

/-- Every iterate of a dominant endomorphism is dominant. -/
instance Scheme.Hom.isDominant_categoricalIterate
    {X : Scheme.{u}} (f : X ⟶ X) [IsDominant f] (n : ℕ) :
    IsDominant (f.categoricalIterate n) := by
  induction n with
  | zero => simp only [Scheme.Hom.categoricalIterate_zero]; infer_instance
  | succ n _ => simp only [Scheme.Hom.categoricalIterate_succ]; infer_instance

/-- Pullback along a categorical iterate is the corresponding functional iterate. -/
theorem Scheme.Hom.functionFieldPullback_categoricalIterate_apply
    {X : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ X) [IsDominant f] (n : ℕ) (z : X.functionField) :
    (f.categoricalIterate n).functionFieldPullback z =
      (f.functionFieldPullback : X.functionField → X.functionField)^[n] z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      have hsucc := Scheme.Hom.functionFieldPullback_congr
        (f.categoricalIterate (n + 1)) (f.categoricalIterate n ≫ f)
        (Scheme.Hom.categoricalIterate_succ f n)
      rw [hsucc, Scheme.Hom.functionFieldPullback_comp, CommRingCat.comp_apply, ih]
      simp only [Function.iterate_succ_apply]

/-- An isomorphism of irreducible schemes induces the contravariant isomorphism of function
fields. -/
noncomputable def Scheme.Iso.functionFieldPullbackRingEquiv
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (e : X ≅ Y) : Y.functionField ≃+* X.functionField where
  toFun := e.hom.functionFieldPullback
  invFun := e.inv.functionFieldPullback
  left_inv z := by
    have hcomp := e.inv.functionFieldPullback_comp e.hom
    have hcancel := Scheme.Hom.functionFieldPullback_congr
      (e.inv ≫ e.hom) (𝟙 Y) e.inv_hom_id
    have h := hcomp.symm.trans (hcancel.trans (Scheme.Hom.functionFieldPullback_id Y))
    exact congrArg (fun q : Y.functionField ⟶ Y.functionField => q z) h
  right_inv z := by
    have hcomp := e.hom.functionFieldPullback_comp e.inv
    have hcancel := Scheme.Hom.functionFieldPullback_congr
      (e.hom ≫ e.inv) (𝟙 X) e.hom_inv_id
    have h := hcomp.symm.trans (hcancel.trans (Scheme.Hom.functionFieldPullback_id X))
    exact congrArg (fun q : X.functionField ⟶ X.functionField => q z) h
  map_add' x y := e.hom.functionFieldPullback.hom.map_add x y
  map_mul' x y := e.hom.functionFieldPullback.hom.map_mul x y

/-- Canonical algebra structure from a field to the function field of its spectrum. -/
@[implicit_reducible] noncomputable def Scheme.specFunctionFieldAlgebra
    (K : Type u) [Field K] : Algebra K (Spec (.of K)).functionField := by
  exact RingHom.toAlgebra
    (StructureSheaf.toStalk K (genericPoint (Spec (.of K)))).hom

/-- The function field of the spectrum of a field is canonically that field. -/
noncomputable def Scheme.specFunctionFieldAlgEquiv (K : Type u) [Field K] :=
  letI := Scheme.specFunctionFieldAlgebra K
  letI : IsFractionRing K (Spec (.of K)).functionField :=
    functionField_isFractionRing_of_affine (.of K)
  IsFractionRing.algEquiv K K (Spec (.of K)).functionField

/-- A dominant structure morphism makes the source function field an algebra over the base
function field. -/
@[implicit_reducible] noncomputable def Scheme.Hom.functionFieldAlgebra
    {X S : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace S]
    (s : X ⟶ S) [IsDominant s] :
    Algebra S.functionField X.functionField :=
  RingHom.toAlgebra s.functionFieldPullback.hom

/-- A dominant self-map over `S` pulls rational functions back by an `S`-algebra endomorphism. -/
noncomputable def Scheme.Hom.functionFieldPullbackAlgHomOver
    {X S : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace S]
    (s : X ⟶ S) [IsDominant s]
    (f : X ⟶ X) [IsDominant f] (hf : f ≫ s = s) :=
  letI := s.functionFieldAlgebra
  { toRingHom := f.functionFieldPullback.hom
    commutes' := fun r => by
      have h := f.functionFieldPullback_comp s
      have hfs := Scheme.Hom.functionFieldPullback_congr (f ≫ s) s hf
      change f.functionFieldPullback (s.functionFieldPullback r) =
        s.functionFieldPullback r
      exact congrArg (fun q : S.functionField ⟶ X.functionField => q r)
        (h.symm.trans hfs) :
      X.functionField →ₐ[S.functionField] X.functionField }

end AlgebraicGeometry
