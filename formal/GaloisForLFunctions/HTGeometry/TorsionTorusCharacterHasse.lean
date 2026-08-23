import GaloisForLFunctions.HTGeometry.ArbitraryFamilyPowerQuotientResidue

/-!
# Hasse detection of torus characters on torsion points

Over `ℂ`, coordinatewise torsion scalings contain roots of every order.  Evaluating a finite-support
monomial character on all such torsion points therefore recovers its complete exponent vector.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe v

/-- Two finite-support exponent vectors agree exactly when their monomial characters agree on all
coordinatewise complex torsion points. -/
theorem complexTorsionTorusMonomialCharacter_congr_hasse_iff
    {ι : Type v} (e f : ι →₀ ℕ) :
    (∀ u : torsionCoordinateScales ℂ ι,
      torsionTorusFamilyMonomialCharacter ℂ ℂ 1 e u =
        torsionTorusFamilyMonomialCharacter ℂ ℂ 1 f u) ↔ e = f := by
  constructor
  · intro h
    apply torsionTorusFamilyMonomialCharacter_injective
      (F := ℂ) (E := ℂ) (ι := ι)
      (containsAllRootsOfUnity_of_isAlgClosed (F := ℂ)) (N := 1) (by omega)
    ext u
    exact h u
  · rintro rfl u
    rfl

end


end GaloisForLFunctions.HTGeometry
