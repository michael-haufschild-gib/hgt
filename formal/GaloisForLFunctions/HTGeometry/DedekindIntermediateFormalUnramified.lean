import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Unramified.Locus

/-!
# Formal unramifiedness descends through a Dedekind intermediate domain

At every prime of the intermediate Dedekind domain, choose a prime above it in the integral top
domain.  Mathlib's local ramification-index descent then transfers unramifiedness from the top.
-/

namespace Algebra

noncomputable section

universe u v w

/-- A formally unramified integral domain extension descends through a Dedekind intermediate
domain, under the finite-type hypotheses needed by the local unramified criterion. -/
theorem formallyUnramified_of_dedekind_intermediate
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [IsDedekindDomain S] [IsDomain T]
    [Algebra.IsIntegral S T] [FaithfulSMul S T]
    [Algebra.EssFiniteType R S] [Algebra.EssFiniteType R T]
    [FormallyUnramified R T] :
    FormallyUnramified R S := by
  rw [formallyUnramified_iff_forall]
  intro q
  letI : q.asIdeal.IsPrime := q.isPrime
  let Q := (Ideal.nonempty_primesOver (S := T) q.asIdeal).some
  letI : (Q : Ideal T).IsPrime := Q.property.1
  letI : (Q : Ideal T).LiesOver q.asIdeal := Q.property.2
  haveI : IsUnramifiedAt R (Q : Ideal T) := inferInstance
  haveI : Module.IsTorsionFree S T :=
    (Module.isTorsionFree_iff_algebraMap_injective).2
      (FaithfulSMul.algebraMap_injective S T)
  exact IsUnramifiedAt.of_liesOver R q.asIdeal (Q : Ideal T)

end
end Algebra
