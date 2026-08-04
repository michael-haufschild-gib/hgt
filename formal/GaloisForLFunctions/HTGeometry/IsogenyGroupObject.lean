import GaloisForLFunctions.HTGeometry.IsogenyRegular
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Isogenies of commutative group objects

A morphism of commutative group objects in a cartesian monoidal category acts on the group of
points of every test object, and the abstract notion of isogeny can be imposed there.  A morphism
is a **pointwise isogeny** when every one of these induced maps of point groups is an isogeny.

This is the representable form of "isogeny of group schemes": the group of `T`-points of a group
scheme is a commutative group, a morphism of group schemes acts on `T`-points by a homomorphism,
and asking for finite kernel and cokernel on all `T` is the functor-of-points shadow of finiteness
of the kernel and of faithful flatness.  Pointwise isogenies compose, contain the identity, and
carry the degree function `T ↦ deg (f on T-points)` which is multiplicative in the same way.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace GaloisForLFunctions.HTGeometry

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]

section

variable {G H K : C} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
  [GrpObj K] [IsCommMonObj K]

/-- Postcomposition with a morphism of monoid objects, as a homomorphism of point groups. -/
@[simps]
def pointHom (f : G ⟶ H) [IsMonHom f] (X : C) : (X ⟶ G) →* (X ⟶ H) where
  toFun g := g ≫ f
  map_one' := by
    change (toUnit X ≫ η[G]) ≫ f = toUnit X ≫ η[H]
    rw [Category.assoc, IsMonHom.one_hom]
  map_mul' g₁ g₂ := by
    change (lift g₁ g₂ ≫ μ) ≫ f = lift (g₁ ≫ f) (g₂ ≫ f) ≫ μ
    rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc]
    congr 1
    ext <;> simp

omit [BraidedCategory C] [IsCommMonObj G] in
@[simp]
theorem pointHom_id (X : C) : pointHom (𝟙 G) X = MonoidHom.id (X ⟶ G) := by
  ext g
  simp

omit [BraidedCategory C] [IsCommMonObj G] [IsCommMonObj H] [IsCommMonObj K] in
theorem pointHom_comp (f : G ⟶ H) [IsMonHom f] (g : H ⟶ K) [IsMonHom g] (X : C) :
    pointHom (f ≫ g) X = (pointHom g X).comp (pointHom f X) := by
  ext x
  simp

/-- A morphism of commutative group objects is a **pointwise isogeny** when it induces an isogeny
on the point group of every object. -/
def IsPointwiseIsogeny (f : G ⟶ H) [IsMonHom f] : Prop := ∀ X : C, IsIsogeny (pointHom f X)

namespace IsPointwiseIsogeny

/-- The identity is a pointwise isogeny. -/
theorem id_isPointwiseIsogeny : IsPointwiseIsogeny (𝟙 G) := by
  intro X
  rw [pointHom_id]
  exact IsIsogeny.of_bijective Function.bijective_id

/-- Pointwise isogenies are closed under composition. -/
theorem comp {f : G ⟶ H} [IsMonHom f] {g : H ⟶ K} [IsMonHom g]
    (hf : IsPointwiseIsogeny f) (hg : IsPointwiseIsogeny g) :
    IsPointwiseIsogeny (f ≫ g) := by
  intro X
  rw [pointHom_comp]
  exact (hg X).comp (hf X)

/-- An isomorphism of group objects is a pointwise isogeny. -/
theorem of_isIso (f : G ⟶ H) [IsMonHom f] [IsIso f] : IsPointwiseIsogeny f := by
  intro X
  refine IsIsogeny.of_bijective ⟨fun a b hab => ?_, fun b => ⟨b ≫ inv f, ?_⟩⟩
  · have h : a ≫ f = b ≫ f := hab
    calc a = (a ≫ f) ≫ inv f := by simp
      _ = (b ≫ f) ≫ inv f := by rw [h]
      _ = b := by simp
  · show (b ≫ inv f) ≫ f = b
    simp

end IsPointwiseIsogeny

/-- The **degree function** of a pointwise isogeny: the degree of the induced map on the point
group of each object. -/
noncomputable def pointwiseDegree (f : G ⟶ H) [IsMonHom f] (X : C) : ℚ :=
  (pointHom f X).isogenyDegree

/-- The degree function of a composite is the pointwise product of the degree functions. -/
theorem pointwiseDegree_comp {f : G ⟶ H} [IsMonHom f] {g : H ⟶ K} [IsMonHom g]
    (hf : IsPointwiseIsogeny f) (hg : IsPointwiseIsogeny g) (X : C) :
    pointwiseDegree (f ≫ g) X = pointwiseDegree g X * pointwiseDegree f X := by
  rw [pointwiseDegree, pointHom_comp, MonoidHom.isogenyDegree_comp (hf X) (hg X)]
  rfl

end

end GaloisForLFunctions.HTGeometry
