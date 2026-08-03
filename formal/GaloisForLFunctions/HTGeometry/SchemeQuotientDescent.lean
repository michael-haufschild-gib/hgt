import GaloisForLFunctions.HTGeometry.FunctionFieldPullback
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Scheme quotient descent

A representable quotient is a coequalizer of its scheme relation.  This file packages that exact
universal property and proves descent of morphisms, endomorphisms, and automorphisms.  It does not
replace a quotient by a quotient of point sets: every construction occurs in `Scheme`.
-/

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- Scheme-level quotient presentation of a relation `s,t : R ⇉ X`. -/
structure SchemeQuotientPresentation (R X : Scheme.{u}) (s t : R ⟶ X) where
  quotient : Scheme.{u}
  projection : X ⟶ quotient
  condition : s ≫ projection = t ≫ projection
  isColimit : IsColimit (Cofork.ofπ projection condition)

namespace SchemeQuotientPresentation

variable {R X : Scheme.{u}} {s t : R ⟶ X}
variable (Q : SchemeQuotientPresentation R X s t)

/-- Every scheme morphism constant on the relation descends to the scheme quotient. -/
def desc {Y : Scheme.{u}} (f : X ⟶ Y) (hf : s ≫ f = t ≫ f) : Q.quotient ⟶ Y :=
  Q.isColimit.desc (Cofork.ofπ f hf)

/-- The descended morphism pulls back to the original morphism. -/
@[reassoc]
theorem projection_desc {Y : Scheme.{u}} (f : X ⟶ Y) (hf : s ≫ f = t ≫ f) :
    Q.projection ≫ Q.desc f hf = f := by
  exact Q.isColimit.fac (Cofork.ofπ f hf) WalkingParallelPair.one

/-- Morphisms out of a scheme quotient are determined after pullback to the presenting scheme. -/
theorem hom_ext {Y : Scheme.{u}} {f g : Q.quotient ⟶ Y}
    (h : Q.projection ≫ f = Q.projection ≫ g) : f = g :=
  Cofork.IsColimit.hom_ext Q.isColimit h

/-- A dominant morphism descended from an integral scheme quotient induces the canonical
injective pullback on function fields. -/
noncomputable def descendedFunctionFieldPullback
    {Y : Scheme.{u}} [IsIntegral Q.quotient] [IsIntegral Y]
    (f : X ⟶ Y) (hf : s ≫ f = t ≫ f) [IsDominant (Q.desc f hf)] :
    Y.functionField ⟶ Q.quotient.functionField :=
  (Q.desc f hf).functionFieldPullback

theorem descendedFunctionFieldPullback_injective
    {Y : Scheme.{u}} [IsIntegral Q.quotient] [IsIntegral Y]
    (f : X ⟶ Y) (hf : s ≫ f = t ≫ f) [IsDominant (Q.desc f hf)] :
    Function.Injective (Q.descendedFunctionFieldPullback f hf) :=
  Scheme.Hom.functionFieldPullback_injective (Q.desc f hf)

/-- An endomorphism preserving both legs of the quotient relation descends. -/
def descendEndomorphism (alpha : X ⟶ X) (beta : R ⟶ R)
    (hs : beta ≫ s = s ≫ alpha) (ht : beta ≫ t = t ≫ alpha) :
    Q.quotient ⟶ Q.quotient :=
  Q.desc (alpha ≫ Q.projection) <| by
    rw [← Category.assoc, ← hs, Category.assoc, Q.condition, ← Category.assoc, ht, Category.assoc]

/-- The quotient projection intertwines an endomorphism with its descent. -/
@[reassoc]
theorem projection_descendEndomorphism (alpha : X ⟶ X) (beta : R ⟶ R)
    (hs : beta ≫ s = s ≫ alpha) (ht : beta ≫ t = t ≫ alpha) :
    Q.projection ≫ Q.descendEndomorphism alpha beta hs ht = alpha ≫ Q.projection :=
  Q.projection_desc _ _

/-- Descent sends identity relation maps to the identity quotient map. -/
theorem descendEndomorphism_id :
    Q.descendEndomorphism (𝟙 X) (𝟙 R) (by simp) (by simp) = 𝟙 Q.quotient := by
  apply Q.hom_ext
  calc
    Q.projection ≫ Q.descendEndomorphism (𝟙 X) (𝟙 R) (by simp) (by simp) =
        𝟙 X ≫ Q.projection := Q.projection_descendEndomorphism _ _ _ _
    _ = Q.projection ≫ 𝟙 Q.quotient := by simp

/-- Descent respects composition of relation-preserving endomorphisms. -/
theorem descendEndomorphism_comp
    (alpha₁ alpha₂ : X ⟶ X) (beta₁ beta₂ : R ⟶ R)
    (hs₁ : beta₁ ≫ s = s ≫ alpha₁) (ht₁ : beta₁ ≫ t = t ≫ alpha₁)
    (hs₂ : beta₂ ≫ s = s ≫ alpha₂) (ht₂ : beta₂ ≫ t = t ≫ alpha₂) :
    Q.descendEndomorphism (alpha₁ ≫ alpha₂) (beta₁ ≫ beta₂)
        (by rw [Category.assoc, hs₂, ← Category.assoc, hs₁, Category.assoc])
        (by rw [Category.assoc, ht₂, ← Category.assoc, ht₁, Category.assoc]) =
      Q.descendEndomorphism alpha₁ beta₁ hs₁ ht₁ ≫
        Q.descendEndomorphism alpha₂ beta₂ hs₂ ht₂ := by
  apply Q.hom_ext
  calc
    Q.projection ≫ Q.descendEndomorphism (alpha₁ ≫ alpha₂) (beta₁ ≫ beta₂) _ _ =
        (alpha₁ ≫ alpha₂) ≫ Q.projection :=
      Q.projection_descendEndomorphism _ _ _ _
    _ = alpha₁ ≫ (alpha₂ ≫ Q.projection) := Category.assoc _ _ _
    _ = alpha₁ ≫
        (Q.projection ≫ Q.descendEndomorphism alpha₂ beta₂ hs₂ ht₂) := by
      rw [Q.projection_descendEndomorphism]
    _ = (alpha₁ ≫ Q.projection) ≫ Q.descendEndomorphism alpha₂ beta₂ hs₂ ht₂ :=
      (Category.assoc _ _ _).symm
    _ = (Q.projection ≫ Q.descendEndomorphism alpha₁ beta₁ hs₁ ht₁) ≫
        Q.descendEndomorphism alpha₂ beta₂ hs₂ ht₂ := by
      rw [Q.projection_descendEndomorphism]
    _ = Q.projection ≫
        (Q.descendEndomorphism alpha₁ beta₁ hs₁ ht₁ ≫
          Q.descendEndomorphism alpha₂ beta₂ hs₂ ht₂) := Category.assoc _ _ _

/-- A relation-preserving scheme isomorphism, with relation-preserving inverse, descends to a
scheme isomorphism of the quotient. -/
def descendIso (alpha : X ≅ X) (beta : R ≅ R)
    (hs : beta.hom ≫ s = s ≫ alpha.hom) (ht : beta.hom ≫ t = t ≫ alpha.hom)
    (hsInv : beta.inv ≫ s = s ≫ alpha.inv) (htInv : beta.inv ≫ t = t ≫ alpha.inv) :
    Q.quotient ≅ Q.quotient where
  hom := Q.descendEndomorphism alpha.hom beta.hom hs ht
  inv := Q.descendEndomorphism alpha.inv beta.inv hsInv htInv
  hom_inv_id := by
    apply Q.hom_ext
    calc
      Q.projection ≫
          (Q.descendEndomorphism alpha.hom beta.hom hs ht ≫
            Q.descendEndomorphism alpha.inv beta.inv hsInv htInv) =
          (Q.projection ≫ Q.descendEndomorphism alpha.hom beta.hom hs ht) ≫
            Q.descendEndomorphism alpha.inv beta.inv hsInv htInv :=
        (Category.assoc _ _ _).symm
      _ = (alpha.hom ≫ Q.projection) ≫
          Q.descendEndomorphism alpha.inv beta.inv hsInv htInv := by
        rw [Q.projection_descendEndomorphism]
      _ = alpha.hom ≫
          (Q.projection ≫ Q.descendEndomorphism alpha.inv beta.inv hsInv htInv) :=
        Category.assoc _ _ _
      _ = alpha.hom ≫ (alpha.inv ≫ Q.projection) := by
        rw [Q.projection_descendEndomorphism]
      _ = (alpha.hom ≫ alpha.inv) ≫ Q.projection := (Category.assoc _ _ _).symm
      _ = Q.projection ≫ 𝟙 Q.quotient := by rw [alpha.hom_inv_id]; simp
  inv_hom_id := by
    apply Q.hom_ext
    calc
      Q.projection ≫
          (Q.descendEndomorphism alpha.inv beta.inv hsInv htInv ≫
            Q.descendEndomorphism alpha.hom beta.hom hs ht) =
          (Q.projection ≫ Q.descendEndomorphism alpha.inv beta.inv hsInv htInv) ≫
            Q.descendEndomorphism alpha.hom beta.hom hs ht :=
        (Category.assoc _ _ _).symm
      _ = (alpha.inv ≫ Q.projection) ≫
          Q.descendEndomorphism alpha.hom beta.hom hs ht := by
        rw [Q.projection_descendEndomorphism]
      _ = alpha.inv ≫
          (Q.projection ≫ Q.descendEndomorphism alpha.hom beta.hom hs ht) :=
        Category.assoc _ _ _
      _ = alpha.inv ≫ (alpha.hom ≫ Q.projection) := by
        rw [Q.projection_descendEndomorphism]
      _ = (alpha.inv ≫ alpha.hom) ≫ Q.projection := (Category.assoc _ _ _).symm
      _ = Q.projection ≫ 𝟙 Q.quotient := by rw [alpha.inv_hom_id]; simp

@[simp]
theorem descendIso_hom (alpha : X ≅ X) (beta : R ≅ R)
    (hs : beta.hom ≫ s = s ≫ alpha.hom) (ht : beta.hom ≫ t = t ≫ alpha.hom)
    (hsInv : beta.inv ≫ s = s ≫ alpha.inv) (htInv : beta.inv ≫ t = t ≫ alpha.inv) :
    (Q.descendIso alpha beta hs ht hsInv htInv).hom =
      Q.descendEndomorphism alpha.hom beta.hom hs ht :=
  rfl

/-- A descended quotient automorphism acts contravariantly on the quotient function field. -/
noncomputable def descendIsoFunctionFieldEquiv [IsIntegral Q.quotient]
    (alpha : X ≅ X) (beta : R ≅ R)
    (hs : beta.hom ≫ s = s ≫ alpha.hom) (ht : beta.hom ≫ t = t ≫ alpha.hom)
    (hsInv : beta.inv ≫ s = s ≫ alpha.inv) (htInv : beta.inv ≫ t = t ≫ alpha.inv) :
    Q.quotient.functionField ≃+* Q.quotient.functionField :=
  Scheme.Iso.functionFieldPullbackRingEquiv
    (Q.descendIso alpha beta hs ht hsInv htInv)

end SchemeQuotientPresentation

end AlgebraicGeometry
