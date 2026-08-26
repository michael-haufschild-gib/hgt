import GaloisForLFunctions.HTGeometry.ABHN.FiniteEtale
import Mathlib.RingTheory.Etale.Finite

/-!
# Finite étale algebras over algebraically closed fields split

This file packages the standard product decomposition supplied by formal
étaleness.  The finite-module hypothesis makes the algebra Artinian, so its
prime spectrum is finite; algebraic closedness then identifies every factor
with the base field.
-/

namespace Algebra

universe u v

/-- A finite étale algebra over an algebraically closed field is a finite product of copies of
the base field, indexed by its prime spectrum. -/
theorem nonempty_algEquiv_pi_of_finiteEtale_isAlgClosed
    {K : Type u} {A : Type v} [Field K] [IsAlgClosed K]
    [CommRing A] [Algebra K A] [Etale K A] [Module.Finite K A] :
    Nonempty (A ≃ₐ[K] (PrimeSpectrum A → K)) := by
  classical
  letI : IsArtinianRing A := isArtinian_of_tower K inferInstance
  letI : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  exact ⟨FormallyEtale.equivPiOfIsSepClosed K A⟩

end Algebra
