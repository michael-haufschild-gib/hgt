import GaloisForLFunctions.HTGeometry.PaperIntegralDiscriminant
import GaloisForLFunctions.HTGeometry.PaperSymmetricDiscriminantEmbedding

/-!
# The integral generic discriminant in the actual normal ring

The source Rees-kernel embedding retains the generic discriminant and all
its powers over every commutative base ring. Vanishing occurs precisely
for the zero base ring. Over fields this agrees with the existing native
normal discriminant.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable (K : Type*) [CommRing K] (n : ℕ)

/-- The integral coefficient discriminant realized in the actual associated graded ring. -/
def paperIntegralNormalDiscriminant :
    PaperIdealAssociatedGraded (paperElementarySymmetricIdeal K n) :=
  paperElementarySymmetricNormalMap K n (paperIntegralDiscriminantPolynomial K n)

/-- The normal discriminant is the embedded square of the native permutation-action Vandermonde. -/
theorem paperIntegralNormalDiscriminant_eq_embedding :
    paperIntegralNormalDiscriminant K n =
      paperSymmetricNormalEmbedding K n
        ⟨vandermonde K n ^ 2, (mem_symmetricSubalgebra _).mpr (isSymmetric_vandermonde_sq K n)⟩ := by
  apply congrArg (paperElementarySymmetricNormalMap K n)
  change paperIntegralDiscriminantPolynomial K n =
    (MvPolynomial.esymmAlgEquiv (Fin n) K (Fintype.card_fin n)).symm
      ⟨vandermonde K n ^ 2, (mem_symmetricSubalgebra _).mpr (isSymmetric_vandermonde_sq K n)⟩
  apply (MvPolynomial.esymmAlgEquiv (Fin n) K (Fintype.card_fin n)).injective
  apply Subtype.ext
  rw [AlgEquiv.apply_symm_apply, MvPolynomial.esymmAlgEquiv_apply,
    esymmAlgHom_apply, paperIntegralDiscriminantPolynomial_spec,
    paperUniversalVandermonde_eq_native]
  exact (pow_two _).symm

/-- Every discriminant power survives in the actual normal ring unless the base ring is zero. -/
theorem paperIntegralNormalDiscriminant_pow_eq_zero_iff (m : ℕ) :
    paperIntegralNormalDiscriminant K n ^ m = 0 ↔ (1 : K) = 0 := by
  rw [paperIntegralNormalDiscriminant, ← map_pow,
    paperElementarySymmetricNormalMap_eq_zero_iff,
    paperIntegralDiscriminantPolynomial_pow_eq_zero_iff]

/-- The integral normal realization specializes to the original field-level normal discriminant. -/
theorem paperIntegralNormalDiscriminant_eq_native (F : Type*) [Field F] (d : ℕ) :
    paperIntegralNormalDiscriminant F d = paperSymmetricNormalDiscriminant F d := by
  rw [paperIntegralNormalDiscriminant, paperIntegralDiscriminantPolynomial_eq_native]
  rfl

end

end GaloisForLFunctions.HTGeometry
