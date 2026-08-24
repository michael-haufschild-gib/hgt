import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Faithfulness boundary for point specialization

Scalar extension along evaluation at a point cannot be faithful on a polynomial coefficient
category: a nonzero scalar endomorphism is killed.  No finite family of point specializations is
jointly faithful.  The exact positive replacement is the full evaluation profile, which is jointly
faithful over an infinite domain.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- Specialize the polynomial coefficient at one point. -/
def polynomialPointSpecialization (c : K) : Polynomial K →+* K :=
  Polynomial.evalRingHom c

@[simp]
theorem polynomialPointSpecialization_apply (c : K) (p : Polynomial K) :
    polynomialPointSpecialization c p = p.eval c := rfl

/-- A point specialization has the explicit nonzero kernel element `X - c`. -/
theorem polynomialPointSpecialization_not_injective (c : K) :
    ¬ Function.Injective (polynomialPointSpecialization c) := by
  intro h
  apply Polynomial.X_sub_C_ne_zero c
  apply h
  simp [polynomialPointSpecialization]

/-- Scalar endomorphism of the rank-one specialized module. -/
def specializedRankOneScalarEndomorphism (c : K) (p : Polynomial K) : K →ₗ[K] K :=
  LinearMap.mulLeft K (p.eval c)

/-- A nonzero scalar endomorphism of a free rank-one polynomial module becomes zero after point
specialization.  Hence pointwise scalar extension cannot define a faithful functor on any category
containing these scalar endomorphisms. -/
theorem exists_nonzero_rankOneScalarEndomorphism_specializes_to_zero (c : K) :
    ∃ p : Polynomial K, p ≠ 0 ∧ specializedRankOneScalarEndomorphism c p = 0 := by
  refine ⟨X - C c, Polynomial.X_sub_C_ne_zero c, ?_⟩
  apply LinearMap.ext
  intro x
  simp [specializedRankOneScalarEndomorphism]

/-- Product vanishing on a prescribed finite packet of specialization points. -/
def finiteSpecializationKernelPolynomial (S : Finset K) : Polynomial K :=
  ∏ c ∈ S, (X - C c)

/-- The finite-packet kernel polynomial is nonzero. -/
theorem finiteSpecializationKernelPolynomial_ne_zero (S : Finset K) :
    finiteSpecializationKernelPolynomial S ≠ 0 := by
  rw [finiteSpecializationKernelPolynomial, Finset.prod_ne_zero_iff]
  intro c hc
  exact Polynomial.X_sub_C_ne_zero c

/-- It vanishes at every point in its packet. -/
theorem finiteSpecializationKernelPolynomial_eval_eq_zero
    (S : Finset K) {c : K} (hc : c ∈ S) :
    (finiteSpecializationKernelPolynomial S).eval c = 0 := by
  rw [finiteSpecializationKernelPolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero hc
  simp

/-- No finite family of point specializations is jointly faithful. -/
theorem finite_pointSpecializations_not_jointly_injective (S : Finset K) :
    ∃ p : Polynomial K, p ≠ 0 ∧ ∀ c ∈ S, polynomialPointSpecialization c p = 0 := by
  exact ⟨finiteSpecializationKernelPolynomial S,
    finiteSpecializationKernelPolynomial_ne_zero S,
    fun c hc => finiteSpecializationKernelPolynomial_eval_eq_zero S hc⟩

/-- Full point-evaluation profile. -/
def polynomialEvaluationProfile : Polynomial K → K → K :=
  fun p c => p.eval c

/-- Sharp positive survivor: over an infinite field, all point specializations together are
faithful. -/
theorem polynomialEvaluationProfile_injective [Infinite K] :
    Function.Injective (polynomialEvaluationProfile (K := K)) := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hroot : {c : K | (p - q).IsRoot c} = Set.univ := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    change Polynomial.eval c (p - q) = 0
    rw [Polynomial.eval_sub]
    have hc := congrFun hpq c
    change Polynomial.eval c p = Polynomial.eval c q at hc
    rw [hc, sub_self]
  rw [hroot]
  exact Set.infinite_univ

/-- Exact boundary: no single point evaluation is faithful, while the full profile is. -/
theorem polynomialSpecialization_faithfulness_boundary [Infinite K] :
    (∀ c : K, ¬ Function.Injective (polynomialPointSpecialization c)) ∧
      Function.Injective (polynomialEvaluationProfile (K := K)) :=
  ⟨polynomialPointSpecialization_not_injective,
    polynomialEvaluationProfile_injective⟩

end

end GaloisForLFunctions.HTGeometry
