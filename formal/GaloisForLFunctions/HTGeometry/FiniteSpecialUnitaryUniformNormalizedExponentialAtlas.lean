import GaloisForLFunctions.HTGeometry.FiniteUnitaryUniformExponentialAtlas
import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryNormalization

/-!
# A uniform normalized-exponential atlas for finite special unitary groups

Successive determinant-normalized partial products telescope.  Combining this identity with the
uniform finite-unitary exponential factorization gives a fixed-length, exact global factorization
of every finite special unitary matrix by normalized exponential increments.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Normalize the successive increments of a finite-unitary word, relative to an initial partial
product.  This does not assume that determinant normalization is multiplicative. -/
def finiteSpecialUnitaryNormalizedIncrements
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι)
    (P : Matrix.unitaryGroup ι ℂ) : List (Matrix.unitaryGroup ι ℂ) →
      List (Matrix.specialUnitaryGroup ι ℂ)
  | [] => []
  | U :: Us =>
      (specialUnitaryNormalize i0 P)⁻¹ * specialUnitaryNormalize i0 (P * U) ::
        finiteSpecialUnitaryNormalizedIncrements i0 (P * U) Us

/-- Successive normalized increments telescope to the normalization of the full product. -/
theorem finiteSpecialUnitaryNormalizedIncrements_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι)
    (P : Matrix.unitaryGroup ι ℂ) (Us : List (Matrix.unitaryGroup ι ℂ)) :
    (finiteSpecialUnitaryNormalizedIncrements i0 P Us).prod =
      (specialUnitaryNormalize i0 P)⁻¹ * specialUnitaryNormalize i0 (P * Us.prod) := by
  induction Us generalizing P with
  | nil => simp [finiteSpecialUnitaryNormalizedIncrements]
  | cons U Us ih =>
    simp only [finiteSpecialUnitaryNormalizedIncrements, List.prod_cons]
    rw [ih]
    group

/-- A fixed finite number of normalized self-adjoint exponential increments reaches every finite
special-unitary matrix.  The number depends only on the finite matrix dimension. -/
theorem exists_finiteSpecialUnitary_uniform_normalized_exponential_prod
    (ι : Type*) [Fintype ι] [DecidableEq ι] (i0 : ι) :
    ∃ N : ℕ, ∀ S : Matrix.specialUnitaryGroup ι ℂ,
      ∃ K : Fin N → selfAdjoint (Matrix ι ι ℂ),
        (finiteSpecialUnitaryNormalizedIncrements i0 1
          (List.ofFn fun i => selfAdjoint.expUnitary (K i))).prod = S := by
  obtain ⟨N, hN⟩ := exists_finiteUnitary_uniform_expUnitary_prod ι
  refine ⟨N, fun S => ?_⟩
  obtain ⟨K, hK⟩ := hN (specialUnitaryToUnitary S)
  refine ⟨K, ?_⟩
  rw [finiteSpecialUnitaryNormalizedIncrements_prod, hK]
  have hnormOne : specialUnitaryNormalize i0 (1 : Matrix.unitaryGroup ι ℂ) =
      (1 : Matrix.specialUnitaryGroup ι ℂ) := by
    change specialUnitaryNormalize i0 (specialUnitaryToUnitary
      (1 : Matrix.specialUnitaryGroup ι ℂ)) = 1
    exact specialUnitaryNormalize_toUnitary i0 1
  rw [hnormOne]
  simp only [inv_one, one_mul]
  exact specialUnitaryNormalize_toUnitary i0 S

end

end GaloisForLFunctions.HTGeometry
