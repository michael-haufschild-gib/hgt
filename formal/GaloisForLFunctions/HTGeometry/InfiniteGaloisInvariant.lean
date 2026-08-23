import Mathlib.RingTheory.Invariant.Galois
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.KrullTopology
import GaloisForLFunctions.HTGeometry.DiscreteContinuousSMul

/-!
# Invariance of the integral closure in an infinite Galois extension

In the AKLB setup with `L / K` Galois — not necessarily finite — every `Gal (L / K)`-fixed element
of the integral closure `B` of `A` in `L` lies in `A`: it is fixed, hence lies in `K` by infinite
Galois theory, and it is integral over `A`, hence lies in `A` because `A` is integrally closed.

This is mathlib's `Algebra.isInvariant_of_isGalois` with the finiteness hypothesis removed, which
is what Deninger's Proposition 3.5 needs: there `L` is an algebraic closure of the function field.
-/

namespace HTGeometry

open scoped Pointwise

open MulAction

variable (A K L B : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
  [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  [IsIntegrallyClosed A] [IsIntegralClosure B A L]

/-- **The integral closure in an infinite Galois extension is an invariant extension.** -/
theorem isInvariant_of_isGalois_infinite [Algebra.IsAlgebraic K L] [IsGalois K L] :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    Algebra.IsInvariant A B (L ≃ₐ[K] L) := by
  letI := IsIntegralClosure.MulSemiringAction A K L B
  refine ⟨fun b hb ↦ ?_⟩
  have hfix : ∀ g : L ≃ₐ[K] L, g (algebraMap B L b) = algebraMap B L b := by
    intro g
    exact (algebraMap_galRestrict_apply A g b).symm.trans (congrArg (algebraMap B L) (hb g))
  have hrange : algebraMap B L b ∈ Set.range (algebraMap K L) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (algebraMap B L b)).2 hfix
  obtain ⟨k, hk⟩ := hrange
  have hint : IsIntegral A b := IsIntegralClosure.isIntegral A L b
  rw [← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective B L), ← hk,
    isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective K L)] at hint
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L,
    (FaithfulSMul.algebraMap_injective B L).eq_iff] at hk
  exact ⟨a, hk⟩

omit [IsIntegrallyClosed A] in
/-- The stabiliser of an element of the integral closure is open for the Krull topology. -/
theorem isOpen_stabilizer_integralClosure [Algebra.IsIntegral K L] (b : B) :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    IsOpen (MulAction.stabilizer (L ≃ₐ[K] L) b : Set (L ≃ₐ[K] L)) := by
  letI := IsIntegralClosure.MulSemiringAction A K L B
  have hset : (MulAction.stabilizer (L ≃ₐ[K] L) b : Set (L ≃ₐ[K] L))
      = (MulAction.stabilizer (L ≃ₐ[K] L) (algebraMap B L b) : Set (L ≃ₐ[K] L)) := by
    ext g
    have key : algebraMap B L (g • b) = g (algebraMap B L b) :=
      algebraMap_galRestrict_apply A g b
    constructor
    · intro hg
      have hg' : g • b = b := hg
      show g (algebraMap B L b) = algebraMap B L b
      rw [← key]
      exact congrArg (algebraMap B L) hg'
    · intro hg
      have hg' : g (algebraMap B L b) = algebraMap B L b := hg
      show g • b = b
      refine FaithfulSMul.algebraMap_injective B L ?_
      rw [key]
      exact hg'
  rw [hset]
  exact stabilizer_isOpen_of_isIntegral (algebraMap B L b)

omit [IsIntegrallyClosed A] in
/-- **The Galois action on the integral closure is continuous for the discrete topology.** -/
theorem continuousSMul_integralClosure [Algebra.IsIntegral K L] [TopologicalSpace B]
    [DiscreteTopology B] :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    ContinuousSMul (L ≃ₐ[K] L) B := by
  letI := IsIntegralClosure.MulSemiringAction A K L B
  exact continuousSMul_of_isOpen_stabilizer (isOpen_stabilizer_integralClosure A K L B)

end HTGeometry
