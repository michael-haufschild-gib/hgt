import GaloisForLFunctions.RHTower.DeningerDynSysValuedPointsAffine
import GaloisForLFunctions.HTGeometry.MultiplicativeFractionLift

/-!
# Proposition 13.8: the multiplicative map factors through the residue field

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 13.8.

Conditions 1) and 2) on `P_{y₀}` say that the map is constant on the cosets of its zero set and
nonzero off it.  The zero set is then a prime ideal, the map factors through the quotient, and —
after transporting the values into a field along the inclusion `o ↪ C` — it extends to the
fraction field of that quotient, which is `κ (x)`.  This is the factorisation `P : κ(x) → C` used
in the converse direction of Proposition 13.8.
-/

namespace RHTower

open HTGeometry

universe u

variable {R O C : Type u} [CommRing R] [CommRing O] [IsDomain O] [Field C]

/-- **Deninger, Proposition 13.8.**  A pointed multiplicative map which is constant on the cosets
of its zero set factors through the residue field of the prime it cuts out, once its values are
transported into a field along an injective ring homomorphism. -/
theorem deningerProp138_fractionLift (Q : R →*₀ O) (ha : DeningerAdditiveOnZeros Q)
    (ι : O →+* C) (hι : Function.Injective ι)
    (κ : Type u) [Field κ] [Algebra (R ⧸ deningerZeroIdeal Q ha) κ]
    [IsFractionRing (R ⧸ deningerZeroIdeal Q ha) κ] :
    ∃ P : κ →*₀ C, ∀ f : R,
      P (algebraMap (R ⧸ deningerZeroIdeal Q ha) κ (Ideal.Quotient.mk _ f)) = ι (Q f) := by
  haveI := deningerZeroIdeal_isPrime Q ha
  have hQ : ∀ x : R ⧸ deningerZeroIdeal Q ha,
      (ι.toMonoidWithZeroHom.comp (deningerQuotientLift Q ha)) x = 0 ↔ x = 0 := by
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    show ι (deningerQuotientLift Q ha (Ideal.Quotient.mk _ f)) = 0 ↔ _
    rw [deningerQuotientLift_mk, map_eq_zero_iff _ hι, Ideal.Quotient.eq_zero_iff_mem,
      deningerMem_zeroIdeal]
  refine ⟨multiplicativeFracLift (κ := κ)
    (ι.toMonoidWithZeroHom.comp (deningerQuotientLift Q ha)) hQ, fun f => ?_⟩
  rw [multiplicativeFracLift_algebraMap]
  show ι (deningerQuotientLift Q ha (Ideal.Quotient.mk _ f)) = ι (Q f)
  rw [deningerQuotientLift_mk]

end RHTower
