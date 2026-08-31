import GaloisForLFunctions.HTGeometry.HankelStandardMonomials

/-!
# The Hankel degeneration is graded

The canonical `(r+1)`-minors are determinants of matrices of variables, hence homogeneous of degree
`r+1`, so the Hankel secant ideal is a homogeneous ideal.  The standard-monomial complement is a
monomial span, hence closed under homogeneous components.  Together:

```text
isHomogeneous_finiteHankelMaximalMinorOver      the minors are homogeneous of degree n
homogeneousComponent_mem_finiteHankelSecantIdeal
    ** the Hankel secant ideal is homogeneous **
homogeneousComponent_mem_hankelStandardSpan     the standard span is graded
isHomogeneous_standardForm
    ** the normal form of a homogeneous polynomial is homogeneous of the same degree **
```

So the `K`-isomorphism `hankelDegenerationLinearEquiv` between the secant quotient and its monomial
degeneration is degree-by-degree: the two rings have the same Hilbert function, witnessed by one
common monomial basis.  That is the input a Cohen–Macaulay transfer from the Stanley–Reisner ring
of the chain complex consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial RHTower

universe u
variable {K : Type u} [Field K]

theorem homogeneousComponent_eq_weighted {N : ℕ} (d : ℕ) (p : MvPolynomial (Fin N) K) :
    MvPolynomial.homogeneousComponent d p
      = MvPolynomial.weightedHomogeneousComponent (1 : Fin N → ℕ) d p := rfl

/-- A canonical Hankel minor is homogeneous of degree `n`. -/
theorem isHomogeneous_finiteHankelMaximalMinorOver (K : Type u) [Field K] {N n : ℕ}
    (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N) :
    (finiteHankelMaximalMinorOver K c hbound).IsHomogeneous n := by
  classical
  rw [finiteHankelMaximalMinorOver, Matrix.det_apply']
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun s _ => ?_
  have hprod : (∏ i : Fin n,
      (MvPolynomial.X (finiteHankelIndex c hbound (s i) i) : MvPolynomial (Fin N) K)).IsHomogeneous
        (∑ _i : Fin n, 1) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => MvPolynomial.isHomogeneous_X K _
  have hn : (∑ _i : Fin n, 1) = n := by simp
  rw [hn] at hprod
  have hCast : ((Equiv.Perm.sign s : ℤ) : MvPolynomial (Fin N) K)
      = MvPolynomial.C ((Equiv.Perm.sign s : ℤ) : K) :=
    (map_intCast (MvPolynomial.C : K →+* MvPolynomial (Fin N) K) _).symm
  rw [hCast]
  simpa using (MvPolynomial.isHomogeneous_C (Fin N) (((Equiv.Perm.sign s : ℤ) : K))).mul hprod

/-- **The Hankel secant ideal is homogeneous.** -/
theorem homogeneousComponent_mem_finiteHankelSecantIdeal (K : Type u) [Field K] (N r d : ℕ)
    {q : MvPolynomial (Fin N) K} (hq : q ∈ finiteHankelSecantIdeal K N r) :
    MvPolynomial.homogeneousComponent d q ∈ finiteHankelSecantIdeal K N r := by
  classical
  letI : GradedAlgebra (MvPolynomial.weightedHomogeneousSubmodule K (1 : Fin N → ℕ)) :=
    MvPolynomial.weightedGradedAlgebra K (1 : Fin N → ℕ)
  have hhom : Ideal.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule K (1 : Fin N → ℕ))
      (finiteHankelSecantIdeal K N r) := by
    rw [finiteHankelSecantIdeal]
    refine Ideal.homogeneous_span _ _ ?_
    rintro b ⟨c, hbound, hc, rfl⟩
    exact ⟨r + 1, isHomogeneous_finiteHankelMaximalMinorOver K c hbound⟩
  have h2 := hhom d hq
  rw [homogeneousComponent_eq_weighted,
    ← MvPolynomial.weightedDecomposition.decompose'_apply K (1 : Fin N → ℕ) q d]
  exact h2

/-- Monomial spans are closed under homogeneous components. -/
theorem homogeneousComponent_mem_hankelStandardSpan {N r d : ℕ}
    {p : MvPolynomial (Fin N) K} (hp : p ∈ hankelStandardSpan K N r) :
    MvPolynomial.homogeneousComponent d p ∈ hankelStandardSpan K N r := by
  classical
  rw [mem_hankelStandardSpan_iff] at hp ⊢
  intro e he
  refine hp e ?_
  rw [homogeneousComponent_eq_weighted,
    MvPolynomial.support_weightedHomogeneousComponent] at he
  exact (Finset.mem_filter.mp he).1

/-- **The standard-form decomposition is graded.**  The normal form of a homogeneous polynomial is
homogeneous of the same degree, so the `K`-isomorphism of the Hankel secant quotient with its
monomial degeneration respects the grading. -/
theorem isHomogeneous_standardForm {N r d : ℕ} {p rem : MvPolynomial (Fin N) K}
    (hp : p.IsHomogeneous d) (hrem : rem ∈ hankelStandardSpan K N r)
    (hdiff : p - rem ∈ finiteHankelSecantIdeal K N r) :
    rem.IsHomogeneous d := by
  classical
  have hcomp : ∀ d' : ℕ, d' ≠ d →
      MvPolynomial.homogeneousComponent d' rem = 0 := by
    intro d' hne
    have h1 : MvPolynomial.homogeneousComponent d' (p - rem)
        ∈ finiteHankelSecantIdeal K N r :=
      homogeneousComponent_mem_finiteHankelSecantIdeal K N r d' hdiff
    have hp0 : MvPolynomial.homogeneousComponent d' p = 0 := by
      rw [homogeneousComponent_eq_weighted]
      exact MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne d' hp hne
    rw [map_sub, hp0, zero_sub] at h1
    have h2 : MvPolynomial.homogeneousComponent d' rem ∈ finiteHankelSecantIdeal K N r := by
      have := neg_mem h1
      simpa using this
    have h3 : MvPolynomial.homogeneousComponent d' rem ∈ hankelStandardSpan K N r :=
      homogeneousComponent_mem_hankelStandardSpan hrem
    have hdisj := (isCompl_finiteHankelSecantIdeal_standardSpan K N r).disjoint
    rw [Submodule.disjoint_def] at hdisj
    exact hdisj _ (by rwa [Submodule.restrictScalars_mem]) h3
  intro e he
  by_contra hne
  have hcoeff : MvPolynomial.coeff e
      (MvPolynomial.homogeneousComponent (Finsupp.weight (1 : Fin N → ℕ) e) rem)
        = MvPolynomial.coeff e rem := by
    rw [homogeneousComponent_eq_weighted, MvPolynomial.coeff_weightedHomogeneousComponent,
      if_pos rfl]
  rw [hcomp _ hne] at hcoeff
  simp only [MvPolynomial.coeff_zero] at hcoeff
  exact he hcoeff.symm

end GaloisForLFunctions.HTGeometry
