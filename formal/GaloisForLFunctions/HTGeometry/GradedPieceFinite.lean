import GaloisForLFunctions.HTGeometry.FamilyDegreeModule

/-!
# The graded pieces are finite dimensional

```text
degreeExponents                       the exponents of a given total degree, as a finset
mem_degreeExponents                   membership is the degree condition
homogeneousSubmodule_eq_span          the degree-e polynomials are spanned by those monomials
finiteDimensional_homogeneousSubmodule_fin ** hence each graded piece is finite dimensional **
```

The finset comes from the tuples of naturals with a given sum, transported along the equivalence
between finitely supported functions and functions on a finite type.

This discharges the finiteness hypothesis carried by the Hilbert-function criterion and by the
degeneration theorem: over finitely many variables every graded piece is finite dimensional, so the
dimension counts those statements are about are all meaningful.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {K : Type u} [Field K]

/-- The exponents of a given total degree. -/
noncomputable def degreeExponents (N e : ℕ) : Finset (Fin N →₀ ℕ) :=
  (Finset.Nat.antidiagonalTuple N e).image (Finsupp.equivFunOnFinite.symm)

theorem degree_eq_sum_univ {N : ℕ} (α : Fin N →₀ ℕ) :
    Finsupp.degree α = ∑ i, α i := by
  classical
  rw [Finsupp.degree]
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro i _ hi
  rw [Finsupp.notMem_support_iff] at hi
  exact hi

theorem mem_degreeExponents {N e : ℕ} {α : Fin N →₀ ℕ} :
    α ∈ degreeExponents N e ↔ Finsupp.degree α = e := by
  classical
  rw [degreeExponents, Finset.mem_image]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [Finset.Nat.mem_antidiagonalTuple] at hf
    rw [degree_eq_sum_univ, ← hf]
    rfl
  · intro hα
    refine ⟨Finsupp.equivFunOnFinite α, ?_, by simp⟩
    rw [Finset.Nat.mem_antidiagonalTuple, ← hα, degree_eq_sum_univ]
    rfl

/-- The degree-`e` polynomials are spanned by the monomials of that degree. -/
theorem homogeneousSubmodule_eq_span (K : Type u) [Field K] (N e : ℕ) :
    homogeneousSubmodule (Fin N) K e
      = Submodule.span K ((fun α : Fin N →₀ ℕ => (MvPolynomial.monomial α (1 : K))) ''
        (degreeExponents N e : Set (Fin N →₀ ℕ))) := by
  classical
  refine le_antisymm ?_ ?_
  · intro p hp
    have hph : p.IsHomogeneous e := hp
    rw [show p = ∑ γ ∈ p.support, MvPolynomial.monomial γ (MvPolynomial.coeff γ p) from
      (MvPolynomial.support_sum_monomial_coeff p).symm]
    refine Submodule.sum_mem _ fun γ hγ => ?_
    have hdeg : Finsupp.degree γ = e := by
      have := hph (MvPolynomial.mem_support_iff.mp hγ)
      rwa [weight_one_eq_degree] at this
    have hmem : (MvPolynomial.monomial γ (1 : K)) ∈
        ((fun α : Fin N →₀ ℕ => (MvPolynomial.monomial α (1 : K))) ''
          (degreeExponents N e : Set (Fin N →₀ ℕ))) :=
      ⟨γ, mem_degreeExponents.mpr hdeg, rfl⟩
    have hsmul : MvPolynomial.monomial γ (MvPolynomial.coeff γ p)
        = (MvPolynomial.coeff γ p) • MvPolynomial.monomial γ (1 : K) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  · rw [Submodule.span_le]
    rintro q ⟨α, hα, rfl⟩
    have hdeg : Finsupp.degree α = e := mem_degreeExponents.mp hα
    intro γ hγ
    rw [MvPolynomial.coeff_monomial] at hγ
    by_cases hγα : α = γ
    · rw [weight_one_eq_degree, ← hγα]
      exact hdeg
    · rw [if_neg hγα] at hγ
      exact absurd rfl hγ

instance finiteDimensional_homogeneousSubmodule_fin (K : Type u) [Field K] (N e : ℕ) :
    FiniteDimensional K (homogeneousSubmodule (Fin N) K e) := by
  rw [homogeneousSubmodule_eq_span]
  exact FiniteDimensional.span_of_finite K (Set.Finite.image _ (degreeExponents N e).finite_toSet)

end GaloisForLFunctions.HTGeometry
