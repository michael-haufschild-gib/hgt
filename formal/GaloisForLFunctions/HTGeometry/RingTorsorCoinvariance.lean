import GaloisForLFunctions.HTGeometry.PositiveDimensionalInvariantGeneration

/-!
# Torsor coinvariance over a coefficient ring

`AffineTorsorCoaction.coinvariant_eq_range` states that the coinvariants of an affine torsor are the
base field, for a torsor whose total object is a *field*.  A Picard--Vessiot ring is not a field --
it is only `σ`-simple, hence a finite product of domains -- so the Galois correspondence needs the
same statement with the total object an arbitrary nonzero algebra.

Faithful flatness of a nonzero algebra over a field is automatic, and mathlib's descent equalizer is
already stated for an arbitrary commutative ring, so the proof carries over verbatim.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Coinvariance over a coefficient ring.**  If the canonical map of a torsor carries the left
embedding to the left embedding and the right embedding to the coaction, then the elements whose
coaction is the left embedding are exactly the base scalars. -/
theorem coinvariant_eq_range_of_canonical
    {K R A : Type*} [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
    [CommRing A] [Algebra K A]
    (coaction : R →ₐ[K] R ⊗[K] A)
    (canonical : (R ⊗[K] R) ≃ₐ[R] (R ⊗[K] A))
    (hleft : ∀ x : R,
      canonical (Algebra.TensorProduct.includeLeft (R := K) (S := R) (A := R) (B := R) x)
        = Algebra.TensorProduct.includeLeft (R := K) (S := R) (A := R) (B := A) x)
    (hright : ∀ x : R,
      canonical (Algebra.TensorProduct.includeRight (R := K) (A := R) (B := R) x) = coaction x) :
    {x : R | coaction x
        = Algebra.TensorProduct.includeLeft (R := K) (S := R) (A := R) (B := A) x}
      = Set.range (algebraMap K R) := by
  ext x
  constructor
  · intro hx
    rw [← Algebra.IsEffective.eqLocus_includeLeft_includeRight
      (Algebra.IsEffective.of_faithfullyFlat K R)]
    change Algebra.TensorProduct.includeLeft (R := K) (S := R) (A := R) (B := R) x
      = Algebra.TensorProduct.includeRight (R := K) (A := R) (B := R) x
    apply canonical.injective
    rw [hleft, hright, hx]
  · rintro ⟨e, rfl⟩
    change coaction (algebraMap K R e)
      = Algebra.TensorProduct.includeLeft (R := K) (S := R) (A := R) (B := A) (algebraMap K R e)
    rw [coaction.commutes]
    simp

end

end GaloisForLFunctions.HTGeometry
