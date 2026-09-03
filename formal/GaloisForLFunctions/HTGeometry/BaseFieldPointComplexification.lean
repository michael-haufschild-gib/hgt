import GaloisForLFunctions.HTGeometry.ComplexPointRationalFunctionEvaluation

/-!
# Complexification of a base-field-valued scheme point

A point of a scheme over a field `k` is algebraic over that base precisely when its complex-valued
point factors through a section `Spec k ⟶ X`.  This module records that factorization without
replacing it by algebraicity of finitely many coordinate values.
-/

namespace AlgebraicGeometry

open CategoryTheory

noncomputable section

/-- A point of a scheme valued in its base field and lying over the identity base point. -/
structure Scheme.BaseFieldPointOver (k : Type) [Field k]
    (X : Scheme) (s : X ⟶ Spec (.of k)) where
  hom : Spec (.of k) ⟶ X
  commutes : hom ≫ s = 𝟙 (Spec (.of k))

/-- Underlying scheme point of a base-field-valued point. -/
def Scheme.BaseFieldPointOver.center
    {k : Type} [Field k] {X : Scheme} {s : X ⟶ Spec (.of k)}
    (p : X.BaseFieldPointOver k s) : X :=
  p.hom (genericPoint (Spec (.of k)))

/-- Scalar extension of a base-field-valued point to a complex-valued point. -/
def Scheme.BaseFieldPointOver.toComplexPoint
    {k : Type} [Field k] [Algebra k ℂ]
    {X : Scheme} {s : X ⟶ Spec (.of k)}
    (p : X.BaseFieldPointOver k s) : X.ComplexPointOver k s where
  hom := Spec.map (CommRingCat.ofHom (algebraMap k ℂ)) ≫ p.hom
  commutes := by
    rw [Category.assoc, p.commutes, Category.comp_id]

/-- The underlying complex point is literally obtained by precomposing with scalar extension. -/
theorem Scheme.BaseFieldPointOver.toComplexPoint_hom
    {k : Type} [Field k] [Algebra k ℂ]
    {X : Scheme} {s : X ⟶ Spec (.of k)}
    (p : X.BaseFieldPointOver k s) :
    p.toComplexPoint.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k ℂ)) ≫ p.hom := rfl

end

end AlgebraicGeometry
