import GaloisForLFunctions.HTGeometry.GradedPieceFinite

/-!
# The graded pieces of the family are finitely generated over the base line

```text
sum_monomial_coeff_of_subset   a polynomial is the sum of its monomials over any superset of its
                               support
coeffPoly                      the coefficient of a fixed monomial, as a polynomial in the extra
                               variable
xDegreeSubmodule_eq_span       ** each graded piece is spanned by the monomials of that degree **
module_finite_xDegreeSubmodule ** hence it is finitely generated over the base line **
```

A polynomial in the extra variable whose coefficients are all homogeneous of one degree is the
combination, with coefficients in the base line, of the finitely many monomials of that degree: read
off each monomial's coefficient as a polynomial in the extra variable.

This is the structural input for applying the fibre-dimension semicontinuity degree by degree — the
family is, in each degree, a finitely generated module over `K[t]`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {K : Type u} [Field K]

theorem sum_monomial_coeff_of_subset {σ : Type*} {p : MvPolynomial σ K} {S : Finset (σ →₀ ℕ)}
    (hS : p.support ⊆ S) :
    ∑ α ∈ S, MvPolynomial.monomial α (MvPolynomial.coeff α p) = p := by
  classical
  refine Eq.trans ?_ (MvPolynomial.support_sum_monomial_coeff p)
  refine (Finset.sum_subset hS ?_).symm
  intro α _ hα
  rw [MvPolynomial.notMem_support_iff] at hα
  rw [hα]
  simp

/-- The coefficient of a fixed monomial, as a polynomial in the extra variable. -/
noncomputable def coeffPoly {N : ℕ} (F : Polynomial (MvPolynomial (Fin N) K))
    (α : Fin N →₀ ℕ) : Polynomial K := by
  classical
  exact ∑ j ∈ F.support, Polynomial.monomial j (MvPolynomial.coeff α (F.coeff j))

theorem coeffPoly_coeff {N : ℕ} (F : Polynomial (MvPolynomial (Fin N) K)) (α : Fin N →₀ ℕ)
    (j : ℕ) : (coeffPoly F α).coeff j = MvPolynomial.coeff α (F.coeff j) := by
  classical
  rw [coeffPoly, Polynomial.finsetSum_coeff]
  by_cases hj : j ∈ F.support
  · rw [← Finset.add_sum_erase _ _ hj, Polynomial.coeff_monomial, if_pos rfl,
      show (∑ i ∈ F.support.erase j,
        (Polynomial.monomial i (MvPolynomial.coeff α (F.coeff i))).coeff j) = 0 from ?_, add_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Polynomial.coeff_monomial, if_neg (Finset.mem_erase.mp hi).1]
  · rw [Polynomial.notMem_support_iff] at hj
    rw [hj, MvPolynomial.coeff_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Polynomial.coeff_monomial]
    by_cases hij : i = j
    · exfalso
      subst hij
      exact (Polynomial.mem_support_iff.mp hi) hj
    · rw [if_neg hij]

theorem smul_C_monomial_coeff {N : ℕ} (c : Polynomial K) (α : Fin N →₀ ℕ) (j : ℕ) :
    ((c • (Polynomial.C (MvPolynomial.monomial α (1 : K)) :
        Polynomial (MvPolynomial (Fin N) K)))).coeff j
      = MvPolynomial.monomial α (c.coeff j) := by
  rw [polyMvAlgebra_smul, Polynomial.coeff_mul_C, Polynomial.coeff_map]
  rw [MvPolynomial.C_mul_monomial, mul_one]

/-- **Each graded piece of the family is spanned over the base line by the monomials of that
degree**, hence finitely generated. -/
theorem xDegreeSubmodule_eq_span (K : Type u) [Field K] (N e : ℕ) :
    xDegreeSubmodule K (Fin N) e
      = Submodule.span (Polynomial K)
        ((fun α : Fin N →₀ ℕ =>
            (Polynomial.C (MvPolynomial.monomial α (1 : K)) :
              Polynomial (MvPolynomial (Fin N) K))) ''
          (degreeExponents N e : Set (Fin N →₀ ℕ))) := by
  classical
  refine le_antisymm ?_ ?_
  · intro F hF
    have hFh : IsXHomog e F := hF
    have hdecomp : F = ∑ α ∈ degreeExponents N e,
        (coeffPoly F α) • (Polynomial.C (MvPolynomial.monomial α (1 : K)) :
          Polynomial (MvPolynomial (Fin N) K)) := by
      refine Polynomial.ext fun j => ?_
      rw [Polynomial.finsetSum_coeff]
      have hsupp : (F.coeff j).support ⊆ degreeExponents N e := by
        intro γ hγ
        refine mem_degreeExponents.mpr ?_
        have := (hFh j) (MvPolynomial.mem_support_iff.mp hγ)
        rwa [weight_one_eq_degree] at this
      rw [← sum_monomial_coeff_of_subset hsupp]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [smul_C_monomial_coeff, coeffPoly_coeff]
    rw [hdecomp]
    refine Submodule.sum_mem _ fun α hα => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, hα, rfl⟩)
  · rw [Submodule.span_le]
    rintro G ⟨α, hα, rfl⟩
    intro j
    rw [Polynomial.coeff_C]
    by_cases hj : j = 0
    · rw [if_pos hj]
      intro γ hγ
      rw [MvPolynomial.coeff_monomial] at hγ
      by_cases hγα : α = γ
      · rw [weight_one_eq_degree, ← hγα]
        exact mem_degreeExponents.mp hα
      · rw [if_neg hγα] at hγ
        exact absurd rfl hγ
    · rw [if_neg hj]
      exact MvPolynomial.isHomogeneous_zero _ _ _

instance module_finite_xDegreeSubmodule (K : Type u) [Field K] (N e : ℕ) :
    Module.Finite (Polynomial K) (xDegreeSubmodule K (Fin N) e) := by
  rw [xDegreeSubmodule_eq_span]
  exact Module.Finite.span_of_finite _ (Set.Finite.image _ (degreeExponents N e).finite_toSet)

end GaloisForLFunctions.HTGeometry
