import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.Abel

namespace GaloisForLFunctions.HTGeometry

/-!
# Star-multiplicative defect chain law

For a map `φ`, the polarized defect

`Γ_φ(x,y) = φ(x⋆y) - φ(x)⋆φ(y)`

measures failure to preserve the star product.  This file proves that these
defects accumulate covariantly under composition.  The identity is purely
algebraic; positivity for unital completely positive maps is the separate
Kadison--Schwarz parent theorem.

No quantum channel, physical actualization, causal order, spacetime, or force
interpretation is asserted here.
-/

variable {A B C : Type*}
variable [NonUnitalNonAssocRing A] [Star A]
variable [NonUnitalNonAssocRing B] [Star B]
variable [NonUnitalNonAssocRing C] [Star C]

/-- Failure of a map to preserve one polarized star product. -/
def starMultiplicativeDefect (phi : A → B) (x y : A) : B :=
  phi (star x * y) - star (phi x) * phi y

/--
The star-multiplicative defect of a composite is propagated earlier defect
plus defect created by the later map.
-/
theorem starMultiplicativeDefect_comp
    (phi : A → B) (psi : B →+ C) (x y : A) :
    starMultiplicativeDefect (fun z => psi (phi z)) x y =
      psi (starMultiplicativeDefect phi x y) +
        starMultiplicativeDefect psi (phi x) (phi y) := by
  simp only [starMultiplicativeDefect, map_sub]
  abel

/-- Star-product defect normalized by a chosen inverse output order unit. -/
def weightedStarMultiplicativeDefect
    (phi : A → B) (outputOrderInv : B) (x y : A) : B :=
  phi (star x * y) -
    star (phi x) * outputOrderInv * phi y

/--
Defect made by a later additive map when its input and output carry different
inverse order units.
-/
def relativeWeightedStarMultiplicativeDefect
    (psi : B → C) (inputOrderInv : B) (outputOrderInv : C)
    (x y : B) : C :=
  psi (star x * inputOrderInv * y) -
    star (psi x) * outputOrderInv * psi y

/--
Source-changing weighted chain law.  Composite weighted defect is propagated
earlier defect plus later defect relative to the intermediate order unit.
-/
theorem weightedStarMultiplicativeDefect_comp
    (phi : A → B) (psi : B →+ C)
    (intermediateOrderInv : B) (outputOrderInv : C)
    (x y : A) :
    weightedStarMultiplicativeDefect
        (fun z => psi (phi z)) outputOrderInv x y =
      psi (weightedStarMultiplicativeDefect
        phi intermediateOrderInv x y) +
      relativeWeightedStarMultiplicativeDefect
        psi intermediateOrderInv outputOrderInv (phi x) (phi y) := by
  simp only [weightedStarMultiplicativeDefect,
    relativeWeightedStarMultiplicativeDefect, map_sub]
  abel

end GaloisForLFunctions.HTGeometry
