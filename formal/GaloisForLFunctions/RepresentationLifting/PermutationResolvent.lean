import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite cyclic factors of permutation resolvents

The finite geometric numerator clears `1 - sP` with scalar denominator
`1 - sʳ`, where `r` is the permutation order. Ordered products retain the
reverse order of the linear factors, so no commutativity of the permutations
is needed. These are the matrix factorizations in equations (7.9) and (7.13)
of Ait Mohamed–El-Baz, independent of a choice of graded algebra.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting

open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

theorem permutationMatrix_pow (σ : Equiv.Perm ι) (k : ℕ) :
    (σ.permMatrix R) ^ k = (σ ^ k).permMatrix R := by
  induction k with
  | zero => simp only [pow_zero, Matrix.permMatrix_one]
  | succ k ih => rw [pow_succ, ih, ← Matrix.permMatrix_mul, ← pow_succ']

theorem permutationMatrix_period (σ : Equiv.Perm ι) :
    (σ.permMatrix R) ^ orderOf σ = 1 := by
  rw [permutationMatrix_pow, pow_orderOf_eq_one, Matrix.permMatrix_one]

/-- The polynomial numerator of the cyclic matrix resolvent. -/
def permutationNumerator (σ : Equiv.Perm ι) (s : R) : Matrix ι ι R :=
  ∑ k ∈ Finset.range (orderOf σ), s ^ k • (σ.permMatrix R) ^ k

theorem permutationNumerator_eq_geom_sum (σ : Equiv.Perm ι) (s : R) :
    permutationNumerator σ s = ∑ k ∈ Finset.range (orderOf σ), (s • σ.permMatrix R) ^ k := by
  simp only [permutationNumerator, smul_pow]

/-- The cyclic numerator clears the denominator on both sides, at every scalar value. -/
theorem permutationNumerator_factorization (σ : Equiv.Perm ι) (s : R) :
    (1 - s • σ.permMatrix R) * permutationNumerator σ s = (1 - s ^ orderOf σ) • 1 ∧
      permutationNumerator σ s * (1 - s • σ.permMatrix R) = (1 - s ^ orderOf σ) • 1 := by
  rw [permutationNumerator_eq_geom_sum, mul_neg_geom_sum, geom_sum_mul_neg,
    smul_pow, permutationMatrix_period]
  constructor <;> simp only [sub_smul, one_smul]

/-- Ordered product of finite cyclic numerators. -/
def permutationNumeratorProduct (s : R) : List (Equiv.Perm ι) → Matrix ι ι R
  | [] => 1
  | σ :: ss => permutationNumerator σ s * permutationNumeratorProduct s ss

/-- The linear factors occur in reverse order when clearing a product of resolvents. -/
def permutationReverseFactors (s : R) : List (Equiv.Perm ι) → Matrix ι ι R
  | [] => 1
  | σ :: ss => permutationReverseFactors s ss * (1 - s • σ.permMatrix R)

/-- The scalar denominator of the ordered product. -/
def permutationScalarDenominator (s : R) : List (Equiv.Perm ι) → R
  | [] => 1
  | σ :: ss => (1 - s ^ orderOf σ) * permutationScalarDenominator s ss

/-- Denominator clearing for arbitrarily many noncommuting permutation factors. -/
theorem permutationProduct_factorization (s : R) (ss : List (Equiv.Perm ι)) :
    permutationReverseFactors s ss * permutationNumeratorProduct s ss =
        permutationScalarDenominator s ss • 1 ∧
      permutationNumeratorProduct s ss * permutationReverseFactors s ss =
        permutationScalarDenominator s ss • 1 := by
  induction ss with
  | nil => simp [permutationReverseFactors, permutationNumeratorProduct,
      permutationScalarDenominator]
  | cons σ ss ih =>
    rcases permutationNumerator_factorization σ s with ⟨hleft, hright⟩
    simp only [permutationReverseFactors, permutationNumeratorProduct,
      permutationScalarDenominator]
    constructor
    · calc
        _ = permutationReverseFactors s ss *
            (((1 - s • σ.permMatrix R) * permutationNumerator σ s) *
              permutationNumeratorProduct s ss) := by simp only [mul_assoc]
        _ = ((1 - s ^ orderOf σ) * permutationScalarDenominator s ss) • 1 := by
          rw [hleft, smul_mul_assoc, one_mul, mul_smul_comm, ih.1, smul_smul]
    · calc
        _ = permutationNumerator σ s *
            (permutationNumeratorProduct s ss * permutationReverseFactors s ss) *
              (1 - s • σ.permMatrix R) := by simp only [mul_assoc]
        _ = ((1 - s ^ orderOf σ) * permutationScalarDenominator s ss) • 1 := by
          rw [ih.2, mul_smul_comm, mul_one, smul_mul_assoc, hright, smul_smul,
            mul_comm (permutationScalarDenominator s ss)]

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.permutationProduct_factorization
