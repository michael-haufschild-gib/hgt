import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeRestrictionHasse

/-!
# Restricted-prime Hasse family

Evaluation at retained arithmetic primes jointly separates the quotient of a weighted prime
section space by the kernel of restriction to a smaller open.
-/

namespace RHTower

open TopologicalSpace

noncomputable section

universe u

variable {E : Nat.Primes → Type u} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
variable (n1 n2 : ∀ p, Seminorm ℝ (E p)) (alpha beta : Nat.Primes → NNReal)

/-- Retained-prime evaluations jointly determine a restricted section quotient. -/
def deningerPrimeRestrictionQuotientHasseFamily
    {U V : Opens (PrimeSpectrum ℤ)} (hVU : V ≤ U) :
    GaloisForLFunctions.HTGeometry.HasseFamily
      (deningerPrimeSections n1 n2 alpha beta U ⧸
        LinearMap.ker (deningerPrimeSectionsRestrictionLinearMap n1 n2 alpha beta U V))
      {p : Nat.Primes // p ∈ deningerPrimeIndex V} where
  Local := fun p => E p.1
  profile := fun q p =>
    (deningerPrimeRestrictionHasseQuotientEquiv n1 n2 alpha beta hVU q).1 p.1
  profile_injective := by
    intro q r hqr
    apply (deningerPrimeRestrictionHasseQuotientEquiv n1 n2 alpha beta hVU).injective
    apply Subtype.ext
    funext p
    classical
    by_cases hp : p ∈ deningerPrimeIndex V
    · exact congrFun hqr ⟨p, hp⟩
    · calc
        (deningerPrimeRestrictionHasseQuotientEquiv n1 n2 alpha beta hVU q).1 p = 0 :=
          (deningerPrimeRestrictionHasseQuotientEquiv n1 n2 alpha beta hVU q).2.1 p hp
        _ = (deningerPrimeRestrictionHasseQuotientEquiv n1 n2 alpha beta hVU r).1 p :=
          ((deningerPrimeRestrictionHasseQuotientEquiv n1 n2 alpha beta hVU r).2.1 p hp).symm

end
end RHTower
