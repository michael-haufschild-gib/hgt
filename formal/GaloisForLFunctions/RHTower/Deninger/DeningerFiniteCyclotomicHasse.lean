import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeFiniteCyclotomicReductionSystem

/-!
# Hasse classification by finite cyclotomic reductions

For a fixed prime `p`, the literal Deninger packet modulo diagonal Frobenius is separated by all
finite prime-to-`p` Frobenius quotients.  This file packages those reductions as one profinite
Hasse profile and identifies packet classes with the profiles actually realized.  In particular,
local triviality at every finite stage is equivalent to global triviality.
-/

namespace RHTower

noncomputable section

/-- Simultaneous finite prime-to-`p` Frobenius reductions of a Deninger packet class. -/
def deningerPrimeFiniteStageHasseProfile (p : Nat.Primes) :
    DeningerPacketFrobeniusQuotient p →*
      ((s : DeningerFiniteFrobeniusStage (p : ℕ)) →
        DeningerFiniteFrobeniusStageQuotient (p : ℕ) s) :=
  MonoidHom.pi fun s => deningerPrimeFiniteStageQuotientReduction p s

/-- A component of the simultaneous profile is the corresponding finite-stage reduction. -/
@[simp] theorem deningerPrimeFiniteStageHasseProfile_apply (p : Nat.Primes)
    (x : DeningerPacketFrobeniusQuotient p)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    deningerPrimeFiniteStageHasseProfile p x s =
      deningerPrimeFiniteStageQuotientReduction p s x := rfl

/-- The complete finite cyclotomic profile loses no packet quotient class. -/
theorem deningerPrimeFiniteStageHasseProfile_injective (p : Nat.Primes) :
    Function.Injective (deningerPrimeFiniteStageHasseProfile p) := by
  intro x y h
  apply deningerPrimeFiniteStageQuotientReduction_jointly_injective p x y
  intro s
  exact congrFun h s

/-- Packet quotient classes are equivalent to the finite cyclotomic profiles that actually
occur. -/
noncomputable def deningerPrimeFiniteStageHasseEquivRealizedProfile (p : Nat.Primes) :
    DeningerPacketFrobeniusQuotient p ≃
      Set.range (deningerPrimeFiniteStageHasseProfile p) :=
  Equiv.ofInjective (deningerPrimeFiniteStageHasseProfile p)
    (deningerPrimeFiniteStageHasseProfile_injective p)

/-- The realized-profile equivalence evaluates as simultaneous finite reduction. -/
@[simp] theorem deningerPrimeFiniteStageHasseEquivRealizedProfile_apply
    (p : Nat.Primes) (x : DeningerPacketFrobeniusQuotient p) :
    (deningerPrimeFiniteStageHasseEquivRealizedProfile p x).1 =
      deningerPrimeFiniteStageHasseProfile p x := rfl

/-- Two packet quotient classes agree exactly when their simultaneous finite profiles agree. -/
theorem deningerPrimeFiniteStageHasseProfile_congr_iff (p : Nat.Primes)
    (x y : DeningerPacketFrobeniusQuotient p) :
    deningerPrimeFiniteStageHasseProfile p x =
      deningerPrimeFiniteStageHasseProfile p y ↔ x = y :=
  (deningerPrimeFiniteStageHasseProfile_injective p).eq_iff

/-- A packet quotient class is trivial exactly when every component of its finite profile is
trivial. -/
theorem deningerPrimeFiniteStageHasseProfile_eq_one_iff (p : Nat.Primes)
    (x : DeningerPacketFrobeniusQuotient p) :
    deningerPrimeFiniteStageHasseProfile p x = 1 ↔ x = 1 := by
  simpa using deningerPrimeFiniteStageHasseProfile_congr_iff p x 1

/-- Pointwise finite-stage equality is equivalent to equality of packet quotient classes. -/
theorem deningerPrimeFiniteStage_congr_hasse_iff (p : Nat.Primes)
    (x y : DeningerPacketFrobeniusQuotient p) :
    (∀ s : DeningerFiniteFrobeniusStage (p : ℕ),
      deningerPrimeFiniteStageQuotientReduction p s x =
        deningerPrimeFiniteStageQuotientReduction p s y) ↔ x = y := by
  constructor
  · exact deningerPrimeFiniteStageQuotientReduction_jointly_injective p x y
  · rintro rfl s
    rfl

end


end RHTower
