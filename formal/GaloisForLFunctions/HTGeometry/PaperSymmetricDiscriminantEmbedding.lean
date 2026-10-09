import GaloisForLFunctions.HTGeometry.PaperElementarySymmetricNormalSpace
import GaloisForLFunctions.HTGeometry.SymmetricCoefficientNonSquare

/-!
# The native generic discriminant survives in the normal coefficient algebra

The existing discriminant polynomial is transported through the proved
symmetric algebra embedding. Every power remains nonzero. No claim that
its different coefficient degrees form a single initial class is needed.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable (K : Type*) [Field K] (n : ℕ)

/-- The actual normal-coordinate realization of the native generic discriminant polynomial. -/
def paperSymmetricNormalDiscriminant :
    PaperIdealAssociatedGraded (paperElementarySymmetricIdeal K n) :=
  paperElementarySymmetricNormalMap K n (discCoeffPoly K n)

/-- The normal discriminant is the image of the original native Vandermonde square. -/
theorem paperSymmetricNormalDiscriminant_eq_embedding :
    paperSymmetricNormalDiscriminant K n =
      paperSymmetricNormalEmbedding K n
        ⟨vandermondePoly K n * vandermondePoly K n, isSymmetric_sq_vandermondePoly⟩ := rfl

/-- Every power of the native discriminant remains nonzero in the actual normal ring. -/
theorem paperSymmetricNormalDiscriminant_pow_ne_zero (m : ℕ) :
    paperSymmetricNormalDiscriminant K n ^ m ≠ 0 := by
  intro h
  rw [paperSymmetricNormalDiscriminant_eq_embedding, ← map_pow] at h
  have he := (paperSymmetricNormalEmbedding_eq_zero_iff K n _).mp h
  have hv : vandermondePoly K n ≠ 0 := vandermondeProd_ne_zero MvPolynomial.X_injective
  exact pow_ne_zero m (mul_ne_zero hv hv) he

end

end GaloisForLFunctions.HTGeometry
