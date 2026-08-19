import GaloisForLFunctions.HTGeometry.IndexTranslationRigidity

/-!
# Rigidity for the jet coordinates

The fixed-field law for a translation of the shift index carries over verbatim to the differential
coordinates: index the jets by `Λ × ℤ`, where the second component records the jet order, and let the
translation act by `(λ, j) ↦ (λ + μ, j)`.  That is translation by `(μ, 0)`, whose order is the order
of `μ`, so the plain rigidity applies unchanged.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {Λ : Type*} [AddCommGroup Λ] {K : Type*} [Field K]

/-- Translating the shift index of a jet coordinate has the order of the shift. -/
theorem jetIndexTranslation_infiniteOrder {μ : Λ} (hμ : ∀ n : ℕ, 0 < n → n • μ ≠ 0) :
    ∀ n : ℕ, 0 < n → n • ((μ, 0) : Λ × ℤ) ≠ 0 := by
  intro n hn hcon
  refine hμ n hn ?_
  have h := congrArg Prod.fst hcon
  simpa using h

/-- **The fixed-field rigidity in differential coordinates.**  A ratio in lowest terms of
polynomials in the jet coordinates that is invariant under translating the shift index by a
nonzero-order `μ` has constant numerator and denominator. -/
theorem eq_C_of_jetIndexTranslation_invariant [DecidableEq Λ] {μ : Λ}
    (hμ : ∀ n : ℕ, 0 < n → n • μ ≠ 0) {P Q : MvPolynomial (Λ × ℤ) K} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hrel : IsRelPrime P Q)
    (h : indexTranslation (K := K) ((μ, 0) : Λ × ℤ) P * Q
      = P * indexTranslation (K := K) ((μ, 0) : Λ × ℤ) Q) :
    P = MvPolynomial.C (P.coeff 0) ∧ Q = MvPolynomial.C (Q.coeff 0) :=
  eq_C_of_indexTranslation_invariant (jetIndexTranslation_infiniteOrder hμ) hP hQ hrel h

/-- **The variable-free form.**  Under the same hypotheses no jet coordinate occurs. -/
theorem vars_eq_empty_of_jetIndexTranslation_invariant [DecidableEq Λ] {μ : Λ}
    (hμ : ∀ n : ℕ, 0 < n → n • μ ≠ 0) {P Q : MvPolynomial (Λ × ℤ) K} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hrel : IsRelPrime P Q)
    (h : indexTranslation (K := K) ((μ, 0) : Λ × ℤ) P * Q
      = P * indexTranslation (K := K) ((μ, 0) : Λ × ℤ) Q) :
    P.vars = ∅ ∧ Q.vars = ∅ :=
  vars_eq_empty_of_indexTranslation_invariant (jetIndexTranslation_infiniteOrder hμ) hP hQ hrel h

end GaloisForLFunctions.HTGeometry
