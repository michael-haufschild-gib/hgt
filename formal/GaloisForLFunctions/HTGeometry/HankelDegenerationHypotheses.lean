import GaloisForLFunctions.HTGeometry.HomogeneousSpan
import GaloisForLFunctions.HTGeometry.MonomialRegularity
import GaloisForLFunctions.HTGeometry.HankelGradedDegeneration

/-!
# The Hankel pair satisfies the degeneration hypotheses

```text
support_homogeneousComponent_subset      components shrink the support
isGradedSubmodule_monomialSpan           a span of monomials is graded
isHomogIdeal_of_support                  an ideal cut out by a support condition is homogeneous
isHomogIdeal_finiteHankelSecantIdeal     ** the secant ideal is homogeneous **
isHomogIdeal_finiteHankelChainIdeal      ** so is the chain ideal **
isGradedSubmodule_hankelStandardSpan     ** and the standard-monomial span is graded **
```

All three follow from the same observation — taking a homogeneous component only shrinks the support
— together with the support characterisations the corpus already proves for these objects.

These are the first three inputs of `forall_mem_of_degeneration` for this card's pair.  With the two
`isCompl` statements, only the fibre bound remains.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} {K : Type u} [Field K]

theorem support_homogeneousComponent_subset (e : ℕ) (p : MvPolynomial σ K) :
    (MvPolynomial.homogeneousComponent e p).support ⊆ p.support := by
  classical
  intro γ hγ
  rw [MvPolynomial.mem_support_iff] at hγ ⊢
  rw [MvPolynomial.coeff_homogeneousComponent] at hγ
  by_cases hd : Finsupp.degree γ = e
  · rwa [if_pos hd] at hγ
  · rw [if_neg hd] at hγ
    exact absurd rfl hγ

/-- **A span of monomials is graded.** -/
theorem isGradedSubmodule_monomialSpan (s : Set (σ →₀ ℕ)) :
    IsGradedSubmodule (monomialSpan K s) := by
  intro e x hx
  rw [mem_monomialSpan_iff] at hx ⊢
  intro γ hγ
  exact hx (support_homogeneousComponent_subset e x hγ)

/-- **An ideal cut out by a condition on supports is homogeneous.** -/
theorem isHomogIdeal_of_support {a : Ideal (MvPolynomial σ K)} {P : (σ →₀ ℕ) → Prop}
    (h : ∀ p : MvPolynomial σ K, p ∈ a ↔ ∀ e ∈ p.support, P e) : IsHomogIdeal a := by
  intro e x hx
  rw [h] at hx ⊢
  intro γ hγ
  exact hx γ (support_homogeneousComponent_subset e x hγ)

section Hankel

open RHTower

/-- The Hankel secant ideal is homogeneous. -/
theorem isHomogIdeal_finiteHankelSecantIdeal (K : Type u) [Field K] (N r : ℕ) :
    IsHomogIdeal (finiteHankelSecantIdeal K N r) :=
  fun e _ hp => homogeneousComponent_mem_finiteHankelSecantIdeal K N r e hp

/-- The chain ideal is homogeneous. -/
theorem isHomogIdeal_finiteHankelChainIdeal (K : Type u) [Field K] (N r : ℕ) :
    IsHomogIdeal (finiteHankelChainIdeal K N r) :=
  isHomogIdeal_of_support (fun _ => mem_finiteHankelChainIdeal_iff)

/-- The standard-monomial span is graded. -/
theorem isGradedSubmodule_hankelStandardSpan (K : Type u) [Field K] (N r : ℕ) :
    IsGradedSubmodule (hankelStandardSpan K N r) :=
  fun _ _ hp => homogeneousComponent_mem_hankelStandardSpan hp

end Hankel

end GaloisForLFunctions.HTGeometry
