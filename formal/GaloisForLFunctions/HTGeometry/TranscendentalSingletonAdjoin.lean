import GaloisForLFunctions.HTGeometry.ShiftDefectDescent

/-!
# Polynomial presentation of a singleton transcendental adjoin

If `y` is transcendental over a field `k`, polynomial evaluation identifies `k[X]` with the
subalgebra `k[y]`.  This packages the existing injectivity theorem together with the standard
range description of a singleton adjoin, so callers do not repeat the same codomain restriction
and bijectivity proof.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Polynomial evaluation with codomain restricted to the singleton-generated subalgebra. -/
def polynomialToSingletonAdjoinAlgHom (y : K) :
    Polynomial k →ₐ[k] Algebra.adjoin k ({y} : Set K) :=
  (Polynomial.aeval y).codRestrict (Algebra.adjoin k ({y} : Set K)) fun p => by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, rfl⟩

/-- Transcendence makes restricted polynomial evaluation injective. -/
theorem polynomialToSingletonAdjoinAlgHom_injective (y : K)
    (hy : Transcendental k y) :
    Function.Injective (polynomialToSingletonAdjoinAlgHom (k := k) y) := by
  intro p q hpq
  apply _root_.HTGeometry.aeval_injective_of_transcendental hy
  exact congrArg Subtype.val hpq

/-- Every element of a singleton-generated subalgebra is a polynomial in its generator. -/
theorem polynomialToSingletonAdjoinAlgHom_surjective (y : K) :
    Function.Surjective (polynomialToSingletonAdjoinAlgHom (k := k) y) := by
  intro z
  have hz : (z : K) ∈ (Polynomial.aeval y : Polynomial k →ₐ[k] K).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]
    exact z.property
  obtain ⟨p, hp⟩ := hz
  exact ⟨p, Subtype.ext hp⟩

/-- Canonical polynomial presentation of a singleton transcendental adjoin. -/
def transcendentalSingletonAdjoinAlgEquiv (y : K) (hy : Transcendental k y) :
    Polynomial k ≃ₐ[k] Algebra.adjoin k ({y} : Set K) :=
  AlgEquiv.ofBijective (polynomialToSingletonAdjoinAlgHom (k := k) y)
    ⟨polynomialToSingletonAdjoinAlgHom_injective (k := k) y hy,
      polynomialToSingletonAdjoinAlgHom_surjective (k := k) y⟩

end

end GaloisForLFunctions.HTGeometry
