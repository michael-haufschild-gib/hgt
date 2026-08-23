import GaloisForLFunctions.RHTower.DeningerPrimePacketCyclotomicTowerAction

/-!
# Hasse descent for compatible cyclotomic towers

Packet units are determined by their actions on every finite away-prime cyclotomic stage.  In the
opposite direction, every compatible family of finite-stage actions has a unique global packet
unit.  This packages the existing inverse-limit comparison as a pointwise local--global principle.
-/

namespace RHTower

noncomputable section

/-- Two global packet units agree exactly when their actions agree at every finite cyclotomic
tower stage. -/
theorem deningerPrimePacketCyclotomicTower_congr_hasse_iff
    (p : Nat.Primes) (u v : DeningerPacketUnits p) :
    (∀ (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) (k : ℕ),
      (deningerPrimePacketCompatibleCyclotomicTowerAction p u).val l k =
        (deningerPrimePacketCompatibleCyclotomicTowerAction p v).val l k) ↔ u = v := by
  constructor
  · intro h
    apply deningerPrimePacketCompatibleCyclotomicTowerAction_injective p
    apply Subtype.ext
    funext l k
    exact h l k
  · rintro rfl l k
    rfl

/-- Every compatible collection of finite cyclotomic-stage automorphisms is realized by one unique
global packet unit. -/
theorem deningerCompatibleCyclotomicTower_existsUnique_packet_hasse
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p) :
    ∃! u : DeningerPacketUnits p,
      ∀ (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) (k : ℕ),
        (deningerPrimePacketCompatibleCyclotomicTowerAction p u).val l k = A.val l k := by
  refine ⟨deningerCompatibleCyclotomicTowerToPacket p A, ?_, ?_⟩
  · intro l k
    have h := deningerPrimePacketCompatibleCyclotomicTowerAction_rightInverse p A
    exact congrFun (congrFun (congrArg Subtype.val h) l) k
  · intro u hu
    apply deningerPrimePacketCompatibleCyclotomicTowerAction_injective p
    rw [deningerPrimePacketCompatibleCyclotomicTowerAction_rightInverse p A]
    apply Subtype.ext
    funext l k
    exact hu l k

end


end RHTower
