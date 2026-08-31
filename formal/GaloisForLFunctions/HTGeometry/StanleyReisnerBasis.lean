import GaloisForLFunctions.HTGeometry.StanleyReisnerDimension
import GaloisForLFunctions.HTGeometry.MonomialSpan

/-!
# The standard monomial basis of a Stanley–Reisner ring

For a downward-closed family of faces, a polynomial lies in the Stanley–Reisner ideal exactly when
no monomial of it is supported on a face.  So the monomials supported on faces are a complement of
the ideal — a `K`-basis of the quotient.

```text
IsFaceFamily                                downward closure
mem_faceFamilyIdeal_iff                     membership is a support condition
faceMonomialSpan                            the span of the monomials supported on faces
isCompl_faceFamilyIdeal_faceMonomialSpan
    ** the standard monomials are a K-basis of the Stanley–Reisner ring **
```

This is the general form of `isCompl_finiteHankelChainIdeal_standardSpan`, and it is the basis on
which Hilbert-series and shelling arguments are carried out.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type u} [Field K]

theorem mem_span_X_compl_iff' {S : Finset σ} {p : MvPolynomial σ K} :
    p ∈ Ideal.span (X '' (↑(Sᶜ) : Set σ) : Set (MvPolynomial σ K)) ↔
      ∀ e ∈ p.support, ¬ e.support ⊆ S := by
  classical
  rw [MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro h e he hsub
    obtain ⟨i, hi, hne⟩ := h e he
    have hiS : i ∈ S := hsub (Finsupp.mem_support_iff.mpr hne)
    simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hi
    exact hi hiS
  · intro h e he
    obtain ⟨i, hi, hiS⟩ := Finset.not_subset.mp (h e he)
    refine ⟨i, ?_, Finsupp.mem_support_iff.mp hi⟩
    simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe]
    exact hiS

/-- A face family is downward closed. -/
def IsFaceFamily (F : Finset (Finset σ)) : Prop :=
  ∀ ⦃S T : Finset σ⦄, T ∈ F → S ⊆ T → S ∈ F

theorem mem_faceFamilyIdeal_iff {F : Finset (Finset σ)} (hF : IsFaceFamily F)
    {p : MvPolynomial σ K} :
    p ∈ faceFamilyIdeal K F ↔ ∀ e ∈ p.support, e.support ∉ F := by
  classical
  rw [faceFamilyIdeal]
  simp only [Finset.inf_eq_iInf, Submodule.mem_iInf]
  constructor
  · intro h e he hmem
    have h2 := h e.support hmem
    rw [mem_span_X_compl_iff'] at h2
    exact h2 e he (subset_refl _)
  · intro h S hS
    rw [mem_span_X_compl_iff']
    intro e he hsub
    exact h e he (hF hS hsub)

/-- The span of the monomials whose support is a face: the standard monomials. -/
noncomputable def faceMonomialSpan (K : Type u) [Field K] (F : Finset (Finset σ)) :
    Submodule K (MvPolynomial σ K) :=
  monomialSpan K {e : σ →₀ ℕ | e.support ∈ F}

omit [Fintype σ] [DecidableEq σ] in
theorem mem_faceMonomialSpan_iff {F : Finset (Finset σ)} {p : MvPolynomial σ K} :
    p ∈ faceMonomialSpan K F ↔ ∀ e ∈ p.support, e.support ∈ F := by
  rw [faceMonomialSpan, mem_monomialSpan_iff]
  constructor
  · intro h e he; exact h (by simpa using he)
  · intro h e he; exact h e (by simpa using he)

/-- **The monomials supported on faces are a `K`-basis of the Stanley–Reisner ring.** -/
theorem isCompl_faceFamilyIdeal_faceMonomialSpan (K : Type u) [Field K] {F : Finset (Finset σ)}
    (hF : IsFaceFamily F) :
    IsCompl (Submodule.restrictScalars K (faceFamilyIdeal K F)) (faceMonomialSpan K F) := by
  classical
  constructor
  · rw [Submodule.disjoint_def]
    intro p hpI hpS
    rw [Submodule.restrictScalars_mem, mem_faceFamilyIdeal_iff hF] at hpI
    rw [mem_faceMonomialSpan_iff] at hpS
    by_contra hp0
    obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hp0
    exact hpI e he (hpS e he)
  · rw [codisjoint_iff, eq_top_iff]
    intro p _
    have hsplit : ∑ e ∈ p.support.filter (fun e => e.support ∉ F),
          MvPolynomial.monomial e (MvPolynomial.coeff e p)
        + ∑ e ∈ p.support.filter (fun e => e.support ∈ F),
          MvPolynomial.monomial e (MvPolynomial.coeff e p) = p := by
      rw [add_comm, Finset.sum_filter_add_sum_filter_not]
      exact MvPolynomial.support_sum_monomial_coeff p
    refine Submodule.mem_sup.mpr ⟨_, ?_, _, ?_, hsplit⟩
    · rw [Submodule.restrictScalars_mem]
      refine Ideal.sum_mem _ fun e he => ?_
      rw [Finset.mem_filter] at he
      have hgen : MvPolynomial.monomial e (1 : K) ∈ faceFamilyIdeal K F := by
        rw [mem_faceFamilyIdeal_iff hF]
        intro f hf
        have : f = e := by
          have := MvPolynomial.support_monomial (a := (1 : K)) (s := e)
          rw [this] at hf
          simpa using hf
        rw [this]
        exact he.2
      have hrw : MvPolynomial.monomial e (MvPolynomial.coeff e p)
          = MvPolynomial.C (MvPolynomial.coeff e p) * MvPolynomial.monomial e (1 : K) := by
        rw [MvPolynomial.C_mul_monomial, mul_one]
      rw [hrw]
      exact Ideal.mul_mem_left _ _ hgen
    · rw [faceMonomialSpan]
      refine Submodule.sum_mem _ fun e he => ?_
      rw [Finset.mem_filter] at he
      have hgen : MvPolynomial.monomial e (1 : K)
          ∈ monomialSpan K {e : σ →₀ ℕ | e.support ∈ F} :=
        Submodule.subset_span ⟨e, he.2, rfl⟩
      have hrw : MvPolynomial.monomial e (MvPolynomial.coeff e p)
          = (MvPolynomial.coeff e p) • MvPolynomial.monomial e (1 : K) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [hrw]
      exact Submodule.smul_mem _ _ hgen

end GaloisForLFunctions.HTGeometry
