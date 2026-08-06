import GaloisForLFunctions.HTGeometry.RamificationExpansionCriterion
import GaloisForLFunctions.HTGeometry.SchemeMorphismOrderPullback

/-!
# Expansion from the local degree

At a codimension-one point of a scheme the ramification index of a morphism is the rank of the
extension of local rings, provided the residue extension there is trivial.  So the expansion
hypothesis of the horizon theorem is the statement that the morphism has local degree greater than
one along the horizon.

In dimension one that is the whole of the expansion step, since a finite morphism of positive degree
between curves has local degree its degree at a totally invariant point.  In higher dimension the
local degree has to be produced from positivity, which is where the numerical class group enters.
-/

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry Order IsDiscreteValuationRing

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

omit [IsLocallyNoetherian X] in
/-- **The ramification index at a codimension-one point is the local degree.**  Hence it exceeds
one exactly when the morphism is not a local isomorphism there. -/
theorem one_lt_ramification_of_one_lt_finrank (f : X ⟶ X) {z : X}
    [IsDiscreteValuationRing (X.presheaf.stalk z)]
    [IsDiscreteValuationRing (X.presheaf.stalk (f.base z))]
    [Algebra (X.presheaf.stalk (f.base z)) (X.presheaf.stalk z)]
    [Module.Finite (X.presheaf.stalk (f.base z)) (X.presheaf.stalk z)]
    {πw : X.presheaf.stalk (f.base z)} (hπw : Irreducible πw) (e : ℕ)
    (hram : addVal (X.presheaf.stalk z)
      (algebraMap (X.presheaf.stalk (f.base z)) (X.presheaf.stalk z) πw) = (e : ℕ∞))
    {x : X.presheaf.stalk z} (hx : addVal (X.presheaf.stalk z) x = 1)
    (hres : ∀ b : X.presheaf.stalk z, ∃ a : X.presheaf.stalk (f.base z),
      addVal (X.presheaf.stalk z)
        (b - algebraMap (X.presheaf.stalk (f.base z)) (X.presheaf.stalk z) a) ≠ 0)
    (hdvd : algebraMap (X.presheaf.stalk (f.base z)) (X.presheaf.stalk z) πw ∣ x ^ e)
    (hdeg : 1 < Module.finrank (X.presheaf.stalk (f.base z)) (X.presheaf.stalk z)) :
    1 < e :=
  one_lt_ramificationIndex hπw e hram hx hres hdvd hdeg

end GaloisForLFunctions.HTGeometry
