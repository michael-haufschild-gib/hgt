import GaloisForLFunctions.RHTower.SerreQ8RootNumberNegOneGaloisIdentification
import GaloisForLFunctions.RHTower.DeningerQ8ArtinGaloisRealization

/-!
# The concrete Artin representation of Serre's Q8 field

The preceding leaves construct Serre's published degree-eight radical field
and prove its `ℚ`-Galois group is `Q₈`.  This leaf pulls back the unique
two-dimensional symplectic quaternionic representation along that actual
Galois equivalence.  Thus the finite algebraic part of the documented Artin
witness is available without assuming an analytic continuation or a global
epsilon-factor formula.
-/

namespace RHTower

noncomputable section

local notation "K3" => SerreQ8TopField

/-- Serre's literal two-dimensional quaternionic Artin representation. -/
def serreQ8ArtinRepresentation : Representation ℂ Gal(K3/ℚ) Q8Carrier :=
  deningerQ8ArtinRepresentation serreQ8_galoisEquivQ8

theorem serreQ8ArtinRepresentation_apply (g : Gal(K3/ℚ)) (v : Q8Carrier) :
    serreQ8ArtinRepresentation g v =
      deningerQ8Representation (serreQ8_galoisEquivQ8 g) v :=
  rfl

/-- The concrete Artin action preserves the nondegenerate alternating form. -/
theorem serreQ8ArtinRepresentation_preserves_symplectic
    (g : Gal(K3/ℚ)) (p q : Q8Carrier) :
    deningerQ8TransitionSymplectic (serreQ8ArtinRepresentation g p)
      (serreQ8ArtinRepresentation g q) = deningerQ8TransitionSymplectic p q := by
  exact deningerQ8ArtinRepresentation_preserves_symplectic serreQ8_galoisEquivQ8 g p q

/-- The realized Artin carrier has its literal complex dimension two. -/
theorem serreQ8ArtinRepresentation_finrank : Module.finrank ℂ Q8Carrier = 2 :=
  deningerQ8ArtinRepresentation_finrank

/-- The preimage of the central Q8 involution acts by `-1`. -/
theorem serreQ8ArtinRepresentation_central_apply (v : Q8Carrier) :
    serreQ8ArtinRepresentation (serreQ8_galoisEquivQ8.symm (QuaternionGroup.a 2)) v = -v := by
  apply deningerQ8ArtinRepresentation_central_apply serreQ8_galoisEquivQ8
  simp

end

end RHTower
