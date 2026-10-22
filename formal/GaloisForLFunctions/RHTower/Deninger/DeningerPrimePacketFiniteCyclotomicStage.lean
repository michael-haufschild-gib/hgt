import GaloisForLFunctions.RHTower.Deninger.DeningerPacketFrobeniusQuotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Finite cyclotomic stages of the Deninger prime packet

Deninger's transverse packet over a prime `p` is built from automorphisms of the prime-to-`p`
roots of unity modulo arithmetic Frobenius.  This module verifies the concrete finite stages of
the product model `∏_{ℓ ≠ p} ℤ_ℓˣ`.

For every `n`, the automorphism group of the complex `n`-th roots of unity is isomorphic to
`(ZMod n)ˣ`.  If `p` is coprime to `n`, exponentiation by `p` is an explicit automorphism.  At an
away prime `ℓ`, the diagonal `p`-unit in `ℤ_ℓˣ` reduces at every level `ℓ^k` to exactly the unit
`p mod ℓ^k`.  Thus the roots-of-unity Frobenius and the constructed packet unit have the same
finite-level exponent.

This is deliberately not promoted to a profinite comparison theorem.  That last step must build
the coherent inverse limit and prove its pointwise/profinite topology agrees with Deninger's
automorphism-group topology.
-/

namespace RHTower

noncomputable section

/-- Finite cyclotomic stage used by the prime-to-characteristic roots-of-unity packet. -/
abbrev DeningerRootsOfUnityStage (n : ℕ) := rootsOfUnity n ℂ

/-- The complex `n`-th roots of unity have exactly `n` elements. -/
theorem deningerRootsOfUnityStage_card (n : ℕ) [NeZero n] :
    Nat.card (DeningerRootsOfUnityStage n) = n :=
  Complex.card_rootsOfUnity n

/-- Automorphisms of a finite roots-of-unity stage are exactly units modulo its order. -/
noncomputable def deningerRootsOfUnityStageAutEquivUnits (n : ℕ) [NeZero n] :
    MulAut (DeningerRootsOfUnityStage n) ≃* (ZMod n)ˣ :=
  (IsCyclic.mulAutMulEquiv (DeningerRootsOfUnityStage n)).trans
    (Units.mapEquiv
      (ZMod.ringEquivCongr (deningerRootsOfUnityStage_card n)).toMulEquiv)

/-- On a finite commutative group, a power coprime to the group order is an automorphism. -/
noncomputable def deningerCoprimePowerMulAut
    (G : Type*) [CommGroup G] [Finite G]
    (m : ℕ) (hm : (Nat.card G).Coprime m) : MulAut G where
  toEquiv := powCoprime hm
  map_mul' x y := mul_pow x y m

@[simp] theorem deningerCoprimePowerMulAut_apply
    (G : Type*) [CommGroup G] [Finite G]
    (m : ℕ) (hm : (Nat.card G).Coprime m) (x : G) :
    deningerCoprimePowerMulAut G m hm x = x ^ m := rfl

/-- Arithmetic Frobenius on a finite roots-of-unity stage is the explicit `p`-power map. -/
noncomputable def deningerRootsOfUnityStageFrobenius
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n) :
    MulAut (DeningerRootsOfUnityStage n) := by
  have hcard : (Nat.card (DeningerRootsOfUnityStage n)).Coprime p := by
    rw [deningerRootsOfUnityStage_card]
    exact hpn.symm
  exact deningerCoprimePowerMulAut (DeningerRootsOfUnityStage n) p hcard

@[simp] theorem deningerRootsOfUnityStageFrobenius_apply
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n)
    (z : DeningerRootsOfUnityStage n) :
    deningerRootsOfUnityStageFrobenius p n hpn z = z ^ p := rfl

/-- The prime `p` is coprime to every power of an away prime `ℓ`. -/
theorem deningerPrime_coprime_awayPrime_pow
    (p : Nat.Primes) (ℓ : {ℓ : Nat.Primes // (ℓ : ℕ) ≠ (p : ℕ)}) (k : ℕ) :
    (p : ℕ).Coprime ((ℓ.1 : ℕ) ^ k) := by
  exact ((Nat.coprime_primes ℓ.1.2 p.2).mpr ℓ.2).symm.pow_right k

/-- Frobenius on the `ℓ^k` cyclotomic stage of the prime-`p` packet. -/
noncomputable def deningerPrimeCyclotomicStageFrobenius
    (p : Nat.Primes) (ℓ : {ℓ : Nat.Primes // (ℓ : ℕ) ≠ (p : ℕ)}) (k : ℕ) :
    MulAut (DeningerRootsOfUnityStage ((ℓ.1 : ℕ) ^ k)) := by
  letI : NeZero ((ℓ.1 : ℕ) ^ k) :=
    ⟨pow_ne_zero k ℓ.1.2.ne_zero⟩
  exact deningerRootsOfUnityStageFrobenius (p : ℕ) ((ℓ.1 : ℕ) ^ k)
    (deningerPrime_coprime_awayPrime_pow p ℓ k)

@[simp] theorem deningerPrimeCyclotomicStageFrobenius_apply
    (p : Nat.Primes) (ℓ : {ℓ : Nat.Primes // (ℓ : ℕ) ≠ (p : ℕ)}) (k : ℕ)
    (z : DeningerRootsOfUnityStage ((ℓ.1 : ℕ) ^ k)) :
    deningerPrimeCyclotomicStageFrobenius p ℓ k z = z ^ (p : ℕ) := by
  letI : NeZero ((ℓ.1 : ℕ) ^ k) :=
    ⟨pow_ne_zero k ℓ.1.2.ne_zero⟩
  rfl

/-- Every finite reduction of the `ℓ`-adic diagonal packet unit is exactly `p mod ℓ^k`.
This is the finite-level compatibility between the product packet and cyclotomic Frobenius. -/
theorem deningerPacketFrobeniusUnit_toZModPow
    (p : Nat.Primes) (ℓ : {ℓ : Nat.Primes // (ℓ : ℕ) ≠ (p : ℕ)}) (k : ℕ) :
    Units.map (PadicInt.toZModPow (p := (ℓ.1 : ℕ)) k)
        (deningerPacketFrobeniusUnit p ℓ) =
      ZMod.unitOfCoprime (p : ℕ)
        (deningerPrime_coprime_awayPrime_pow p ℓ k) := by
  ext
  simp [deningerPacketFrobeniusUnit, ZMod.unitOfCoprime]

end

end RHTower
