import GaloisForLFunctions.HTGeometry.ExponentialPolynomialVandermondeMulti

/-!
# Distinct node tuples separate polynomial coefficient functions

The multi-node separation theorem is stated with the polynomial coefficients written out as a
finite sum of monomials in the integer parameters.  The form an orbit argument produces them in is
a multivariate polynomial evaluated at the parameters, so this module packages the theorem for that
input: if

```text
∑_i P_i(k_1,…,k_D) ∏_s Z(i,s)^{k_s} = 0
```

for every tuple `k` of positive integers, and the node tuples `Z i` are pairwise distinct with
nonzero entries, then every polynomial `P_i` is the zero polynomial.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {D : ℕ}

/-- **Distinct node tuples separate polynomial coefficients.**  Polynomial form. -/
theorem mvPolynomial_nodeSeparation {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (Z : ι → Fin D → ℂ) (hZ0 : ∀ i s, Z i s ≠ 0) (hZinj : Set.InjOn Z ↑S)
    (P : ι → MvPolynomial (Fin D) ℂ)
    (h : ∀ k : Fin D → ℕ, (∀ s, 1 ≤ k s) →
      ∑ i ∈ S, (MvPolynomial.eval (fun s => ((k s : ℕ) : ℂ)) (P i)) * ∏ s, (Z i s) ^ (k s) = 0) :
    ∀ i ∈ S, P i = 0 := by
  classical
  set E : Finset (Fin D → ℕ) :=
    (S.biUnion (fun i => (P i).support)).image (fun d => Finsupp.equivFunOnFinite d) with hE
  set a : ι → (Fin D → ℕ) → ℂ :=
    fun i e => if i ∈ S then MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) (P i) else 0
    with ha
  have haS : ∀ i ∈ S, ∀ e, a i e
      = MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) (P i) := by
    intro i hi e
    simp only [ha, if_pos hi]
  have hazero : ∀ i, ∀ e ∉ E, a i e = 0 := by
    intro i e he
    by_cases hi : i ∈ S
    · rw [haS i hi e]
      by_contra hne
      refine he ?_
      rw [hE]
      exact Finset.mem_image.mpr ⟨Finsupp.equivFunOnFinite.symm e,
        Finset.mem_biUnion.mpr ⟨i, hi, MvPolynomial.mem_support_iff.mpr hne⟩,
        Finsupp.equivFunOnFinite.apply_symm_apply e⟩
    · simp only [ha, if_neg hi]
  have hcoeffsum : ∀ i ∈ S, ∀ k : Fin D → ℕ,
      (∑ e ∈ E, a i e * ∏ s : Fin D, ((k s : ℕ) : ℂ) ^ (e s))
        = MvPolynomial.eval (fun s => ((k s : ℕ) : ℂ)) (P i) := by
    intro i hi k
    have hsub : (P i).support.image (fun d => Finsupp.equivFunOnFinite d) ⊆ E := by
      rw [hE]
      exact Finset.image_subset_image (fun d hd => Finset.mem_biUnion.mpr ⟨i, hi, hd⟩)
    have hstep : (∑ e ∈ (P i).support.image (fun d => Finsupp.equivFunOnFinite d),
          a i e * ∏ s : Fin D, ((k s : ℕ) : ℂ) ^ (e s))
        = ∑ e ∈ E, a i e * ∏ s : Fin D, ((k s : ℕ) : ℂ) ^ (e s) := by
      refine Finset.sum_subset hsub ?_
      intro e _ hne
      rw [haS i hi e]
      have hzero : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) (P i) = 0 := by
        by_contra hc
        exact hne (Finset.mem_image.mpr ⟨Finsupp.equivFunOnFinite.symm e,
          MvPolynomial.mem_support_iff.mpr hc, Finsupp.equivFunOnFinite.apply_symm_apply e⟩)
      rw [hzero, zero_mul]
    rw [← hstep, Finset.sum_image (fun d _ d' _ hdd => Finsupp.equivFunOnFinite.injective hdd),
      MvPolynomial.eval_eq']
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [haS i hi (Finsupp.equivFunOnFinite d), Finsupp.equivFunOnFinite.symm_apply_apply d]
    rfl
  have hmain := expPolySumMulti_eq_zero D S Z hZ0 hZinj E a hazero ?_
  · intro i hi
    refine MvPolynomial.ext _ _ fun d => ?_
    have h0 := hmain i hi (Finsupp.equivFunOnFinite d)
    rw [haS i hi (Finsupp.equivFunOnFinite d), Finsupp.equivFunOnFinite.symm_apply_apply d] at h0
    rw [MvPolynomial.coeff_zero]
    exact h0
  · intro k hk
    rw [Finset.sum_congr rfl (fun i hi => by rw [hcoeffsum i hi k])]
    exact h k hk

end

end GaloisForLFunctions.HTGeometry
