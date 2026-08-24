import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.RHTower.WeldChargeProfileHasse
import GaloisForLFunctions.RHTower.DeningerFiniteCyclotomicHasse
import GaloisForLFunctions.RHTower.BurnolCoPoissonMellinHasse
import GaloisForLFunctions.RHTower.ArtinMonomialMultiplicitySeparation
import GaloisForLFunctions.RHTower.FieldOneGlobalAdeleTorsionHasse

/-!
# RHTower profile-valued Hasse applications

Profinite charge, finite cyclotomic, Mellin, monomial-character, and adelic torsion profiles are
registered in the route-neutral `HasseFamily` interface.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

universe u

open GaloisForLFunctions.HTGeometry

/-- All two-power deck charges detect an integer index. -/
def twoPowerWChargeHasseFamily : HasseFamily ℤ ℕ where
  Local := fun k => ZMod (2 ^ k)
  profile := twoPowerWChargeProfile
  profile_injective := twoPowerWChargeProfile_injective

/-- All finite prime-to-`p` Frobenius quotients detect a Deninger packet quotient class. -/
def deningerFiniteCyclotomicHasseFamily (p : Nat.Primes) :
    HasseFamily (_root_.RHTower.DeningerPacketFrobeniusQuotient p)
      (_root_.RHTower.DeningerFiniteFrobeniusStage (p : ℕ)) where
  Local := fun s => _root_.RHTower.DeningerFiniteFrobeniusStageQuotient (p : ℕ) s
  profile := _root_.RHTower.deningerPrimeFiniteStageHasseProfile p
  profile_injective := _root_.RHTower.deningerPrimeFiniteStageHasseProfile_injective p

/-- Right-strip completed Mellin probes detect a Burnol co-Poisson quotient vector. -/
def burnolCoPoissonMellinHasseFamily (b : Set.Ioi (0 : ℝ)) :
    HasseFamily (_root_.RHTower.burnolCoPoissonQuotientSpace (b : ℝ))
      _root_.RHTower.BurnolRightStrip where
  Local := fun _ => ℂ
  profile := _root_.RHTower.burnolCoPoissonMellinProfile b
  profile_injective := _root_.RHTower.burnolCoPoissonMellinProfile_injective b

/-- Multiplicities against all induced linear characters detect a virtual character. -/
def artinMonomialMultiplicityHasseFamily
    (G : Type u) [Group G] [Fintype G] :
    HasseFamily (VirtualCharacter G) (Σ H : Subgroup G, LinearCharacter H) where
  Local := fun _ => ℤ
  profile := monomialMultiplicityProfile G
  profile_injective := monomialMultiplicityProfile_injective G

/-- Every finite torsion preimage together faithfully records a character-neutral adelic class. -/
def fieldOneZeroSumTorsionTowerHasseFamily :
    HasseFamily fieldOneGlobalAdeleClassCharacter.ker ℕ where
  Local := fun n => fieldOneGlobalAdeleClassNTorsionPreimage n
  profile := fun x n => fieldOneGlobalAdeleZeroSumToNTorsionPreimage n x
  profile_injective := by
    intro x y h
    exact fieldOneGlobalAdeleZeroSumToNTorsionPreimage_injective 1 (congrFun h 1)

end
end GaloisForLFunctions.RHTower
