import GaloisForLFunctions.HTGeometry.FlatFamilyIdeal

/-!
# The `x`-grading of the family

The extra variable carries `x`-degree zero, so a polynomial in it decomposes by the degree of its
coefficients:

```text
xComp, xComp_coeff                the x-degree-e part
IsXHomog, isXHomog_xComp          homogeneity for the x-degree
xComp_eq_self_of_isXHomog
sum_xComp                         ** a polynomial is the sum of its x-homogeneous parts **
```

Along the way, the standard-degree analogues of the weighted decomposition lemmas
(`sum_homogeneousComponent_support`, `homogeneousComponent_eq_zero_of_notMem`) and the identity
`weight_one_eq_degree` between the all-ones weight and the total degree.

This is the second grading the flat family carries.  The weight grading, in which the extra variable
has weight `-1`, controls the degeneration; this one, in which it has degree zero, is what survives
quotienting by *linear* forms — and therefore what makes the graded pieces finitely generated modules
over the base line.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- The `x`-degree-`e` part of a polynomial in the extra variable, which carries degree zero. -/
noncomputable def xComp (e : ℕ) (F : Polynomial (MvPolynomial σ K)) :
    Polynomial (MvPolynomial σ K) :=
  ∑ j ∈ F.support, Polynomial.monomial j
    (MvPolynomial.homogeneousComponent e (F.coeff j))

theorem xComp_coeff (e : ℕ) (F : Polynomial (MvPolynomial σ K)) (j : ℕ) :
    (xComp e F).coeff j = MvPolynomial.homogeneousComponent e (F.coeff j) := by
  classical
  rw [xComp, Polynomial.finsetSum_coeff]
  by_cases hj : j ∈ F.support
  · rw [← Finset.add_sum_erase _ _ hj, Polynomial.coeff_monomial, if_pos rfl]
    rw [show (∑ i ∈ F.support.erase j,
        (Polynomial.monomial i
          (MvPolynomial.homogeneousComponent e (F.coeff i))).coeff j) = 0 from ?_, add_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Polynomial.coeff_monomial, if_neg (Finset.mem_erase.mp hi).1]
  · rw [Polynomial.notMem_support_iff] at hj
    rw [hj, map_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Polynomial.coeff_monomial]
    by_cases hij : i = j
    · exfalso
      subst hij
      exact (Polynomial.mem_support_iff.mp hi) hj
    · rw [if_neg hij]

theorem xComp_add (e : ℕ) (F G : Polynomial (MvPolynomial σ K)) :
    xComp e (F + G) = xComp e F + xComp e G := by
  refine Polynomial.ext fun j => ?_
  rw [Polynomial.coeff_add, xComp_coeff, xComp_coeff, xComp_coeff, Polynomial.coeff_add, map_add]

/-- Homogeneity for the `x`-degree: every coefficient is homogeneous of the same degree. -/
def IsXHomog (e : ℕ) (F : Polynomial (MvPolynomial σ K)) : Prop :=
  ∀ j : ℕ, (F.coeff j).IsHomogeneous e

theorem isXHomog_xComp (e : ℕ) (F : Polynomial (MvPolynomial σ K)) :
    IsXHomog e (xComp e F) := by
  intro j
  rw [xComp_coeff]
  exact MvPolynomial.homogeneousComponent_isHomogeneous e _

theorem weight_one_eq_degree (γ : σ →₀ ℕ) : (Finsupp.weight 1) γ = Finsupp.degree γ := by
  rw [Finsupp.weight_apply, Finsupp.degree, Finsupp.sum]
  simp

theorem xComp_eq_self_of_isXHomog {e : ℕ} {F : Polynomial (MvPolynomial σ K)}
    (hF : IsXHomog e F) : xComp e F = F := by
  refine Polynomial.ext fun j => ?_
  rw [xComp_coeff]
  ext γ
  rw [MvPolynomial.coeff_homogeneousComponent]
  by_cases hγ : Finsupp.degree γ = e
  · rw [if_pos hγ]
  · rw [if_neg hγ]
    by_contra hcon
    have hw := hF j (Ne.symm hcon)
    rw [weight_one_eq_degree] at hw
    exact hγ hw

theorem homogeneousComponent_eq_zero_of_notMem {p : MvPolynomial σ K} {e : ℕ}
    (he : e ∉ p.support.image Finsupp.degree) :
    MvPolynomial.homogeneousComponent e p = 0 := by
  classical
  ext γ
  rw [MvPolynomial.coeff_homogeneousComponent]
  by_cases hγ : Finsupp.degree γ = e
  · rw [if_pos hγ, MvPolynomial.coeff_zero]
    by_contra hcon
    exact he (hγ ▸ Finset.mem_image_of_mem _ (MvPolynomial.mem_support_iff.mpr hcon))
  · rw [if_neg hγ, MvPolynomial.coeff_zero]

theorem sum_homogeneousComponent_support (p : MvPolynomial σ K) :
    ∑ e ∈ p.support.image Finsupp.degree, MvPolynomial.homogeneousComponent e p = p := by
  classical
  ext γ
  rw [MvPolynomial.coeff_sum]
  by_cases hγ : γ ∈ p.support
  · have hmem : Finsupp.degree γ ∈ p.support.image Finsupp.degree :=
      Finset.mem_image_of_mem _ hγ
    rw [← Finset.add_sum_erase _ _ hmem, MvPolynomial.coeff_homogeneousComponent, if_pos rfl]
    rw [show (∑ e ∈ (p.support.image Finsupp.degree).erase (Finsupp.degree γ),
        MvPolynomial.coeff γ (MvPolynomial.homogeneousComponent e p)) = 0 from ?_, add_zero]
    refine Finset.sum_eq_zero fun e he => ?_
    have hne : e ≠ Finsupp.degree γ := (Finset.mem_erase.mp he).1
    rw [MvPolynomial.coeff_homogeneousComponent, if_neg (fun h => hne h.symm)]
  · rw [MvPolynomial.notMem_support_iff] at hγ
    rw [hγ]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [MvPolynomial.coeff_homogeneousComponent, hγ]
    exact ite_self 0

/-- The finitely many `x`-degrees carried by a polynomial in the extra variable. -/
noncomputable def xDegrees (F : Polynomial (MvPolynomial σ K)) : Finset ℕ := by
  classical
  exact F.support.biUnion (fun j => (F.coeff j).support.image Finsupp.degree)

/-- **A polynomial in the extra variable is the sum of its `x`-homogeneous parts.** -/
theorem sum_xComp (F : Polynomial (MvPolynomial σ K)) :
    ∑ e ∈ xDegrees F, xComp e F = F := by
  classical
  refine Polynomial.ext fun j => ?_
  rw [Polynomial.finsetSum_coeff]
  simp only [xComp_coeff]
  by_cases hj : j ∈ F.support
  · have hsub : (F.coeff j).support.image Finsupp.degree ⊆ xDegrees F := by
      intro e he
      rw [xDegrees, Finset.mem_biUnion]
      exact ⟨j, hj, he⟩
    rw [← Finset.sum_subset hsub ?_, sum_homogeneousComponent_support]
    intro e _ hnot
    exact homogeneousComponent_eq_zero_of_notMem hnot
  · rw [Polynomial.notMem_support_iff] at hj
    rw [hj]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [map_zero]

end GaloisForLFunctions.HTGeometry
