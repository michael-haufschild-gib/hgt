import Mathlib

/-!
# The span of a set of monomials

A polynomial lies in the span of a set of monomials exactly when its support is contained in that
set.  If the set is closed under addition the span is closed under multiplication, and if it
contains zero the span contains one — so the monomial span of an additive submonoid of exponents is
a subalgebra.

This is the working description of a monomial subalgebra: membership is a support condition, so
every question about it becomes a question about the exponent semigroup.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u

variable {σ : Type*} {K : Type u} [Field K]

/-- The submodule spanned by a set of monomials. -/
noncomputable def monomialSpan (K : Type u) [Field K] (s : Set (σ →₀ ℕ)) :
    Submodule K (MvPolynomial σ K) :=
  Submodule.span K ((fun m => (MvPolynomial.monomial m (1 : K))) '' s)

theorem mem_monomialSpan_iff {s : Set (σ →₀ ℕ)} {p : MvPolynomial σ K} :
    p ∈ monomialSpan K s ↔ (↑p.support : Set (σ →₀ ℕ)) ⊆ s := by
  classical
  constructor
  · intro hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro q ⟨m, hm, rfl⟩ e he
      have : e = m := by
        have := MvPolynomial.support_monomial (a := (1 : K)) (s := m)
        rw [this] at he
        simpa using he
      exact this ▸ hm
    · simp
    · intro x y _ _ hx hy e he
      have := MvPolynomial.support_add (p := x) (q := y)
      have hmem : e ∈ x.support ∪ y.support := this (by simpa using he)
      rcases Finset.mem_union.mp hmem with h | h
      · exact hx (by simpa using h)
      · exact hy (by simpa using h)
    · intro a x _ hx e he
      have hsub : ((a • x : MvPolynomial σ K)).support ⊆ x.support := MvPolynomial.support_smul
      exact hx (by simpa using hsub (by simpa using he))
  · intro hp
    have hsum : p = ∑ m ∈ p.support, MvPolynomial.monomial m (MvPolynomial.coeff m p) :=
      (MvPolynomial.support_sum_monomial_coeff p).symm
    rw [hsum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have hmem : (MvPolynomial.monomial m (1 : K)) ∈ monomialSpan K s :=
      Submodule.subset_span ⟨m, hp (by simpa using hm), rfl⟩
    have hsm : MvPolynomial.monomial m (MvPolynomial.coeff m p)
        = (MvPolynomial.coeff m p) • (MvPolynomial.monomial m (1 : K)) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hsm]
    exact Submodule.smul_mem _ _ hmem

/-- The monomial span of an additively closed set is closed under multiplication. -/
theorem mul_mem_monomialSpan {s : Set (σ →₀ ℕ)} (hs : ∀ a ∈ s, ∀ b ∈ s, a + b ∈ s)
    {p q : MvPolynomial σ K} (hp : p ∈ monomialSpan K s) (hq : q ∈ monomialSpan K s) :
    p * q ∈ monomialSpan K s := by
  classical
  rw [mem_monomialSpan_iff] at hp hq ⊢
  intro e he
  have hsub := MvPolynomial.support_mul p q
  have hmem := hsub (by simpa using he)
  rw [Finset.mem_add] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  subst hab
  exact hs a (hp (by simpa using ha)) b (hq (by simpa using hb))

/-- The monomial span of an additively closed set containing zero, as a subalgebra. -/
theorem one_mem_monomialSpan {s : Set (σ →₀ ℕ)} (h0 : (0 : σ →₀ ℕ) ∈ s) :
    (1 : MvPolynomial σ K) ∈ monomialSpan K s := by
  classical
  rw [mem_monomialSpan_iff]
  intro e he
  have : e = 0 := by
    rw [MvPolynomial.support_one] at he
    simpa using he
  exact this ▸ h0


end GaloisForLFunctions.HTGeometry
