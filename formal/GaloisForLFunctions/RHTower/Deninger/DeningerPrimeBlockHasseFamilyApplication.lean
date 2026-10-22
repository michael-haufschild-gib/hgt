import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeBlockHasse

/-!
# All-prime block Hasse family

A square-summable family of prime-packet restriction maps gives a literal all-prime Hasse family
on global vectors modulo simultaneous prime invisibility.  This is reusable local-place machinery
for Connes/Tate-style decompositions; it does not identify the local packets with an RH source.
-/

namespace RHTower

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Kp : Nat.Primes → Type*}
  [∀ p, NormedAddCommGroup (Kp p)] [∀ p, InnerProductSpace ℝ (Kp p)]

/-- Prime-packet restrictions jointly determine a vector modulo simultaneous prime
invisibility. -/
def deningerPrimeBlockQuotientHasseFamily
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ)) :
    GaloisForLFunctions.HTGeometry.HasseFamily
      (E ⧸ LinearMap.ker (deningerPrimeRestrictionLinearMap restriction hsummable))
      Nat.Primes where
  Local := Kp
  profile := fun q p =>
    (deningerPrimeBlockHasseQuotientEquivRealizedProfiles restriction hsummable q).1 p
  profile_injective := by
    intro q r hqr
    apply (deningerPrimeBlockHasseQuotientEquivRealizedProfiles restriction hsummable).injective
    apply Subtype.ext
    apply Subtype.ext
    funext p
    exact congrFun hqr p

end
end RHTower
