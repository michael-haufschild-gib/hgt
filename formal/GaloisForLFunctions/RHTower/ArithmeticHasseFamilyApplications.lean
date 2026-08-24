import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.RHTower.OddPrimeCRTHasse
import GaloisForLFunctions.RHTower.EulerCofinalReducedCompletion

/-!
# Arithmetic Hasse-family applications

Two reconstruction principles independent of any specific RH route: finite CRT gluing over
certified odd primes and separation of the Euler source algebra by every radical finite-cutoff
quotient.
-/

namespace RHTower.OddPrimeFamily

noncomputable section

variable {I : Type*} [Fintype I]

/-- Certified odd-prime residue coordinates form a finite Hasse family. -/
def oddPrimeCrtHasseFamily (P : OddPrimeFamily I) :
    GaloisForLFunctions.HTGeometry.HasseFamily (ZMod P.modulus) I where
  Local := fun i => ZMod (P.prime i).1
  profile := fun x i => P.crtEquiv x i
  profile_injective := by
    intro x y hxy
    apply P.crtEquiv.injective
    funext i
    exact congrFun hxy i

end
end RHTower.OddPrimeFamily

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- All radical finite Euler cutoff quotients jointly separate the Euler source algebra. -/
def eulerCofinalQuotientHasseFamily :
    GaloisForLFunctions.HTGeometry.HasseFamily (AddMonoidAlgebra ℂ ℂ) ℕ where
  Local := fun N => AddMonoidAlgebra ℂ ℂ ⧸ eulerJ N
  profile := fun a N => eulerCofinalQuotientMap a N
  profile_injective := by
    intro a b hab
    apply eulerCofinalQuotientMap_injective
    funext N
    exact congrFun hab N

end
end GaloisForLFunctions.RHTower
