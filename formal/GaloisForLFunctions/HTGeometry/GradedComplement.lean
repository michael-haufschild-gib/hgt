import GaloisForLFunctions.HTGeometry.DegreewiseRegularity

/-!
# Graded complements, degree by degree

```text
IsGradedSubmodule       a subspace closed under taking homogeneous components
degreePart              its part in a fixed degree
isCompl_degreePart      ** a complement of graded subspaces is a complement in every degree **
finrank_degreePart_eq   ** hence two graded subspaces with the same complement have the same
                           dimension in every degree **
```

The degreewise complement is read off the global one by taking components: the decomposition of a
homogeneous element into a part in each subspace can be replaced by the degree-`e` components of
those parts, which stay in the subspaces because both are graded.

The dimension statement is the Hilbert-function equality of a Gröbner degeneration in the form a
regular-sequence argument uses it: an ideal and its initial ideal are both complementary to the span
of the standard monomials, so their graded pieces have equal dimensions, and therefore so do the
graded pieces of the two quotients.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Module

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- A `K`-submodule closed under taking homogeneous components. -/
def IsGradedSubmodule (A : Submodule K (MvPolynomial σ K)) : Prop :=
  ∀ (e : ℕ) (x : MvPolynomial σ K), x ∈ A → MvPolynomial.homogeneousComponent e x ∈ A

/-- The degree-`e` part of a submodule, as a subspace of the degree-`e` polynomials. -/
noncomputable def degreePart (A : Submodule K (MvPolynomial σ K)) (e : ℕ) :
    Submodule K (homogeneousSubmodule σ K e) :=
  Submodule.comap (homogeneousSubmodule σ K e).subtype A

theorem mem_degreePart {A : Submodule K (MvPolynomial σ K)} {e : ℕ}
    {x : homogeneousSubmodule σ K e} :
    x ∈ degreePart A e ↔ (x : MvPolynomial σ K) ∈ A := Iff.rfl

/-- **A complement of graded subspaces is a complement in each degree.** -/
theorem isCompl_degreePart {A S : Submodule K (MvPolynomial σ K)}
    (hA : IsGradedSubmodule A) (hS : IsGradedSubmodule S) (h : IsCompl A S) (e : ℕ) :
    IsCompl (degreePart A e) (degreePart S e) := by
  constructor
  · have hdisj := h.disjoint
    rw [disjoint_iff] at hdisj ⊢
    refine le_antisymm ?_ bot_le
    rintro x ⟨hxA, hxS⟩
    have hmem : (x : MvPolynomial σ K) ∈ A ⊓ S := ⟨hxA, hxS⟩
    rw [hdisj] at hmem
    have hx0 : (x : MvPolynomial σ K) = 0 := hmem
    exact Submodule.coe_eq_zero.mp hx0
  · have hcod := h.codisjoint
    rw [codisjoint_iff] at hcod ⊢
    refine le_antisymm le_top ?_
    intro x _
    have hx : (x : MvPolynomial σ K) ∈ A ⊔ S := by rw [hcod]; trivial
    obtain ⟨a, ha, s, hs, hax⟩ := Submodule.mem_sup.mp hx
    have hxhom : MvPolynomial.homogeneousComponent e (x : MvPolynomial σ K)
        = (x : MvPolynomial σ K) := by
      have hx' : ((x : MvPolynomial σ K)).IsHomogeneous e := x.2
      ext γ
      rw [MvPolynomial.coeff_homogeneousComponent]
      by_cases hγ : Finsupp.degree γ = e
      · rw [if_pos hγ]
      · rw [if_neg hγ]
        by_contra hcon
        refine hγ ?_
        have := hx' (Ne.symm hcon)
        rwa [weight_one_eq_degree] at this
    refine Submodule.mem_sup.mpr
      ⟨⟨MvPolynomial.homogeneousComponent e a,
        MvPolynomial.homogeneousComponent_isHomogeneous e a⟩, hA e a ha,
       ⟨MvPolynomial.homogeneousComponent e s,
        MvPolynomial.homogeneousComponent_isHomogeneous e s⟩, hS e s hs, ?_⟩
    refine Subtype.ext ?_
    show MvPolynomial.homogeneousComponent e a + MvPolynomial.homogeneousComponent e s
      = (x : MvPolynomial σ K)
    rw [← map_add, hax, hxhom]

/-- **Two graded subspaces with the same complement have the same dimension in every degree.**
This is the Hilbert-function equality of a Gröbner degeneration, in the form the chain uses. -/
theorem finrank_degreePart_eq {A B S : Submodule K (MvPolynomial σ K)}
    (hA : IsGradedSubmodule A) (hB : IsGradedSubmodule B) (hS : IsGradedSubmodule S)
    (hAS : IsCompl A S) (hBS : IsCompl B S) (e : ℕ)
    [FiniteDimensional K (homogeneousSubmodule σ K e)] :
    finrank K (degreePart A e) = finrank K (degreePart B e) := by
  have h1 := Submodule.finrank_add_eq_of_isCompl (isCompl_degreePart hA hS hAS e)
  have h2 := Submodule.finrank_add_eq_of_isCompl (isCompl_degreePart hB hS hBS e)
  omega

end GaloisForLFunctions.HTGeometry
