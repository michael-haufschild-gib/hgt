import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.RHTower.DeningerArithmeticCofiniteDivisorQuotient

/-!
# Cofinite divisor Hasse family

Outside-prime residue coordinates form a jointly separating family on the divisor quotient by
the retained prime sector.  For `R = ℤ`, this packages the divisor sequence of `Spec ℤ[S⁻¹]` as a
literal place-indexed Hasse principle.
-/

namespace RHTower

universe u v

noncomputable section

/-- Outside-prime residues jointly determine a divisor modulo the retained prime sector. -/
def deningerCofiniteDivisorQuotientHasseFamily
    (R : Type u) (ι : Type v) [CommRing R] (S : ι → Prop) :
    GaloisForLFunctions.HTGeometry.HasseFamily
      ((ι →₀ R) ⧸ LinearMap.range (deningerInsideDivisorEmbedding (R := R) S))
      (DeningerOutsidePrime S) where
  Local := fun _ => R
  profile := fun q p => deningerCofiniteDivisorQuotientEquiv (R := R) S q p
  profile_injective := by
    intro q r hqr
    apply (deningerCofiniteDivisorQuotientEquiv (R := R) S).injective
    ext p
    exact congrFun hqr p

end
end RHTower
