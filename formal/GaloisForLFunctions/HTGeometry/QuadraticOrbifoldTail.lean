import GaloisForLFunctions.HTGeometry.QuadraticNoInvariantDifferential
import GaloisForLFunctions.HTGeometry.RationalInvariantDifferential

/-!
# The two quadratic coarse-grainings have no nonconstant scaling eigenvector

Transporting the invariant-differential layer of the free jet field to `RatFunc ℂ` turns a
nonconstant eigenvector of the substitution endomorphism into a rational relation
`Q ∘ R · (R')^k = μ Q` with `k ≠ 0` and `μ ≠ 0`.  For `z² + 1` and for `(z − 1)²` no such relation
exists, so at jet order at most one there is no nonconstant eigenvector at all, and at any finite
jet order the only possible eigenvalue is one.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The substitution derivative of a polynomial map is its classical derivative, so it is nonzero
whenever the map is nonconstant. -/
theorem substitutionDeriv_algebraMap_ne_zero {P : Polynomial ℂ} (hP : Polynomial.derivative P ≠ 0) :
    substitutionDeriv (algebraMap (Polynomial ℂ) (RatFunc ℂ) P) ≠ 0 := by
  intro h
  have hinj : Function.Injective
      (ratFuncEval (JetField.jet ((), 0) : JetField ℂ Unit) transcendental_freeGen) :=
    ratFuncEval_injective _ transcendental_freeGen
  have h2 := ratFuncEval_ratFuncDeriv (algebraMap (Polynomial ℂ) (RatFunc ℂ) P)
  rw [h, ratFuncDeriv_algebraMap] at h2
  have h3 : (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative P)) = 0 :=
    hinj (by rw [h2, map_zero])
  exact hP ((RatFunc.algebraMap_injective ℂ) (by rw [h3, map_zero]))

theorem quadOne_substitutionDeriv_ne_zero :
    substitutionDeriv (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne) ≠ 0 := by
  refine substitutionDeriv_algebraMap_ne_zero ?_
  rw [derivative_quadOne]
  intro h
  have := congrArg (fun p => Polynomial.coeff p 1) h
  simp at this

theorem quadTwo_substitutionDeriv_ne_zero :
    substitutionDeriv (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo) ≠ 0 := by
  refine substitutionDeriv_algebraMap_ne_zero ?_
  rw [derivative_quadTwo]
  exact mul_ne_zero (by simp) (Polynomial.X_sub_C_ne_zero 1)

/-- **`z ↦ z² + 1` has no nonconstant eigenvector of jet order at most one.** -/
theorem quadOne_no_order_one_eigen
    {u : JetField ℂ Unit} (hu : ∀ j : ℕ, 1 < j → JetField.pd ((), j) u = 0)
    (hnc : ∀ e : ℂ, u ≠ algebraMap ℂ (JetField ℂ Unit) e) {lam : ℂ} (hlam : lam ≠ 0)
    (heig : jetSubstitution (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
        quadOne_substitutionDeriv_ne_zero u = algebraMap ℂ (JetField ℂ Unit) lam * u) :
    False := by
  obtain ⟨k, Q, μ, hk, hμ, hQ0, hrel⟩ :=
    exists_ratFunc_relation_of_order_one _ quadOne_substitutionDeriv_ne_zero hu hnc hlam heig
  rw [ratFuncDeriv_algebraMap] at hrel
  exact hk (quadOne_no_invariant_differential _ hQ0 hμ hrel).1

/-- **`z ↦ (z − 1)²` has no nonconstant eigenvector of jet order at most one.** -/
theorem quadTwo_no_order_one_eigen
    {u : JetField ℂ Unit} (hu : ∀ j : ℕ, 1 < j → JetField.pd ((), j) u = 0)
    (hnc : ∀ e : ℂ, u ≠ algebraMap ℂ (JetField ℂ Unit) e) {lam : ℂ} (hlam : lam ≠ 0)
    (heig : jetSubstitution (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
        quadTwo_substitutionDeriv_ne_zero u = algebraMap ℂ (JetField ℂ Unit) lam * u) :
    False := by
  obtain ⟨k, Q, μ, hk, hμ, hQ0, hrel⟩ :=
    exists_ratFunc_relation_of_order_one _ quadTwo_substitutionDeriv_ne_zero hu hnc hlam heig
  rw [ratFuncDeriv_algebraMap] at hrel
  exact hk (quadTwo_no_invariant_differential _ hQ0 hμ hrel).1

/-- **Every finite-order eigenvector of `z ↦ z² + 1` has eigenvalue one.** -/
theorem quadOne_eigen_eq_one {u : JetField ℂ Unit} (hu0 : u ≠ 0) {M : ℕ}
    (hu : ∀ j : ℕ, M < j → JetField.pd ((), j) u = 0) {lam : ℂ} (hlam : lam ≠ 0)
    (heig : jetSubstitution (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
        quadOne_substitutionDeriv_ne_zero u = algebraMap ℂ (JetField ℂ Unit) lam * u) :
    lam = 1 := by
  rcases exists_nonzero_isInvariantDifferential_or_eq_one _ quadOne_substitutionDeriv_ne_zero
    hu0 hu hlam heig with ⟨k, q, μ, hk, hμ, hq⟩ | h
  · obtain ⟨Q, hQ0, hrel⟩ :=
      exists_ratFunc_relation_of_isInvariantDifferential _ quadOne_substitutionDeriv_ne_zero hq
    rw [ratFuncDeriv_algebraMap] at hrel
    exact absurd (quadOne_no_invariant_differential _ hQ0 hμ hrel).1 hk
  · exact h

/-- **Every finite-order eigenvector of `z ↦ (z − 1)²` has eigenvalue one.** -/
theorem quadTwo_eigen_eq_one {u : JetField ℂ Unit} (hu0 : u ≠ 0) {M : ℕ}
    (hu : ∀ j : ℕ, M < j → JetField.pd ((), j) u = 0) {lam : ℂ} (hlam : lam ≠ 0)
    (heig : jetSubstitution (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
        quadTwo_substitutionDeriv_ne_zero u = algebraMap ℂ (JetField ℂ Unit) lam * u) :
    lam = 1 := by
  rcases exists_nonzero_isInvariantDifferential_or_eq_one _ quadTwo_substitutionDeriv_ne_zero
    hu0 hu hlam heig with ⟨k, q, μ, hk, hμ, hq⟩ | h
  · obtain ⟨Q, hQ0, hrel⟩ :=
      exists_ratFunc_relation_of_isInvariantDifferential _ quadTwo_substitutionDeriv_ne_zero hq
    rw [ratFuncDeriv_algebraMap] at hrel
    exact absurd (quadTwo_no_invariant_differential _ hQ0 hμ hrel).1 hk
  · exact h

end

end GaloisForLFunctions.HTGeometry
