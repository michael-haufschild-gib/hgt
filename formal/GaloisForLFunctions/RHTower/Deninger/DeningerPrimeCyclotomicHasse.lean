import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.RHTower.Deninger.DeningerPrimePacketCyclotomicTowerAction

/-!
# Cyclotomic-stage Hasse principle for prime packets

An actual Deninger prime-packet unit acts on every arithmetic prime-power root stage away from the
characteristic.  These finite actions jointly recover the packet before quotienting by diagonal
Frobenius, and every unequal pair is separated at one finite cyclotomic stage.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Index of an away-prime arithmetic cyclotomic stage. -/
abbrev DeningerPrimeCyclotomicStageIndex (p : Nat.Primes) :=
  Σ _l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}, ℕ

/-- All arithmetic prime-power cyclotomic actions form a Hasse family for packet units. -/
noncomputable def deningerPrimePacketCyclotomicHasseFamily (p : Nat.Primes) :
    HasseFamily (DeningerPacketUnits p) (DeningerPrimeCyclotomicStageIndex p) where
  Local i := MulAut (DeningerPrimeArithmeticRoots p i.1.1 i.2)
  profile u i := deningerPrimePacketCyclotomicStageAction p i.1 i.2 u
  profile_injective := by
    intro u v h
    apply deningerPrimePacketCyclotomicTowerAction_injective p
    funext l k
    exact congrFun h ⟨l, k⟩

/-- Packet units agree exactly when their actions agree on every away-prime cyclotomic stage. -/
theorem deningerPrimePacketCyclotomic_congr_hasse_iff
    (p : Nat.Primes) (u v : DeningerPacketUnits p) :
    (∀ l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}, ∀ k : ℕ,
      deningerPrimePacketCyclotomicStageAction p l k u =
        deningerPrimePacketCyclotomicStageAction p l k v) ↔ u = v := by
  constructor
  · intro h
    apply deningerPrimePacketCyclotomicTowerAction_injective p
    funext l k
    exact h l k
  · rintro rfl l k
    rfl

/-- Unequal packet units differ on one finite away-prime cyclotomic stage. -/
theorem deningerPrimePacketCyclotomic_ne_iff_exists_stage_ne
    (p : Nat.Primes) (u v : DeningerPacketUnits p) :
    u ≠ v ↔ ∃ l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}, ∃ k : ℕ,
      deningerPrimePacketCyclotomicStageAction p l k u ≠
        deningerPrimePacketCyclotomicStageAction p l k v := by
  rw [(deningerPrimePacketCyclotomicHasseFamily p).ne_iff_exists_local_ne]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.1, i.2, hi⟩
  · rintro ⟨l, k, h⟩
    exact ⟨⟨l, k⟩, h⟩

end

end RHTower
