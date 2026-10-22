import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Homomorphisms out of a ring with only two primes

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), the Remark following
Theorem 15.1.

A rank one valuation ring has only the two prime ideals `0` and the maximal ideal.  Hence a ring
homomorphism from such a ring into a domain has kernel `0` or the maximal ideal: it is either
injective, or it factors through the residue field.
-/

namespace RHTower


variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsDomain S]

/-- **Deninger, the Remark after Theorem 15.1.**  A ring homomorphism out of a local ring whose
only primes are `0` and the maximal ideal, into a domain, is either injective or factors through
the residue field. -/
theorem deningerRingHom_injective_or_factorsResidue
    (hprime : ∀ P : Ideal R, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal R)
    (f : R →+* S) :
    Function.Injective f ∨
      ∃ g : IsLocalRing.ResidueField R →+* S, g.comp (IsLocalRing.residue R) = f := by
  haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  rcases hprime (RingHom.ker f) inferInstance with h | h
  · exact Or.inl ((RingHom.injective_iff_ker_eq_bot f).2 h)
  · refine Or.inr ⟨Ideal.Quotient.lift _ f (fun a ha => ?_), rfl⟩
    have : a ∈ RingHom.ker f := h ▸ ha
    exact this


end RHTower
