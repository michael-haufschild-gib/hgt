import GaloisForLFunctions.RepresentationLifting.PermutationResolvent
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Rational permutation resolvents

With an indeterminate scalar, the cyclic denominator never vanishes. Thus the
finite geometric factorization constructs an actual matrix unit over the
rational function field, without a nonvanishing assumption.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

omit [DecidableEq ι] in
/-- The cyclic denominator is nonzero as a rational function. -/
theorem permutationRationalDenominator_ne_zero (σ : Equiv.Perm ι) :
    (1 - (RatFunc.X : RatFunc K) ^ orderOf σ) ≠ 0 := by
  intro h
  have hp : (1 - Polynomial.X ^ orderOf σ : Polynomial K) = 0 := by
    apply RatFunc.algebraMap_injective K
    simpa only [map_sub, map_one, map_pow, RatFunc.algebraMap_X, map_zero] using h
  have he := congrArg (Polynomial.eval (0 : K)) hp
  have hr : orderOf σ ≠ 0 := Nat.ne_of_gt (orderOf_pos σ)
  simp [Polynomial.eval_sub, Polynomial.eval_pow, hr] at he

/-- The matrix `I-XP` and its explicit finite rational inverse. -/
def permutationRationalResolventUnit (σ : Equiv.Perm ι) : (Matrix ι ι (RatFunc K))ˣ where
  val := 1 - RatFunc.X • σ.permMatrix (RatFunc K)
  inv := (1 - (RatFunc.X : RatFunc K) ^ orderOf σ)⁻¹ •
    permutationNumerator σ (RatFunc.X : RatFunc K)
  val_inv := by
    rw [mul_smul_comm, (permutationNumerator_factorization σ (RatFunc.X : RatFunc K)).1,
      smul_smul, inv_mul_cancel₀ (permutationRationalDenominator_ne_zero σ), one_smul]
  inv_val := by
    rw [smul_mul_assoc, (permutationNumerator_factorization σ (RatFunc.X : RatFunc K)).2,
      smul_smul, inv_mul_cancel₀ (permutationRationalDenominator_ne_zero σ), one_smul]

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.permutationRationalResolventUnit
