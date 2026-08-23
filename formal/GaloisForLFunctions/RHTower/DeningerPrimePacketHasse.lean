import GaloisForLFunctions.RHTower.DeningerPrimeFinitePacketInverseLimit

/-!
# Hasse reconstruction for Deninger prime packets

The literal compact packet quotient is its inverse limit of finite Frobenius quotients.  The
elementwise Hasse API states the consequences directly: finite reductions jointly detect equality
and the neutral class, and every coherent finite local family has a unique global packet lift.
-/

namespace RHTower

noncomputable section

/-- Two global packet classes agree exactly when all finite Frobenius reductions agree. -/
theorem deningerPrimePacket_hasse_eq_iff (p : Nat.Primes)
    (x y : DeningerPacketFrobeniusQuotient p) :
    (∀ s : DeningerFiniteFrobeniusStage (p : ℕ),
      deningerPrimeFiniteStageQuotientReduction p s x =
        deningerPrimeFiniteStageQuotientReduction p s y) ↔ x = y := by
  constructor
  · exact deningerPrimeFiniteStageQuotientReduction_jointly_injective p x y
  · rintro rfl s
    rfl

/-- A global packet class is neutral exactly when every finite Frobenius reduction is neutral. -/
theorem deningerPrimePacket_hasse_eq_one_iff (p : Nat.Primes)
    (x : DeningerPacketFrobeniusQuotient p) :
    x = 1 ↔ ∀ s : DeningerFiniteFrobeniusStage (p : ℕ),
      deningerPrimeFiniteStageQuotientReduction p s x = 1 := by
  rw [← deningerPrimePacket_hasse_eq_iff p x 1]
  simp

/-- Every coherent family of finite Frobenius packet classes has a unique global packet class. -/
theorem deningerPrimePacket_hasse_exists_unique (p : Nat.Primes)
    (y : DeningerPrimeFinitePacketLimit p) :
    ∃! x : DeningerPacketFrobeniusQuotient p,
      ∀ s : DeningerFiniteFrobeniusStage (p : ℕ),
        deningerPrimeFiniteStageQuotientReduction p s x = y.1 s := by
  obtain ⟨x, hx⟩ := deningerPrimePacketToFiniteLimit_surjective p y
  have hxlocal : ∀ s : DeningerFiniteFrobeniusStage (p : ℕ),
      deningerPrimeFiniteStageQuotientReduction p s x = y.1 s := by
    intro s
    exact congrArg (fun z : DeningerPrimeFinitePacketLimit p => z.1 s) hx
  refine ⟨x, hxlocal, ?_⟩
  intro z hz
  apply deningerPrimeFiniteStageQuotientReduction_jointly_injective p z x
  intro s
  exact (hz s).trans (hxlocal s).symm

end


end RHTower
